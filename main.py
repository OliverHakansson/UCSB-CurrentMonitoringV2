import json
import os
import queue
import re
import threading
import time
import tkinter as tk
from tkinter import filedialog, messagebox, ttk
import csv
import pyvisa
from matplotlib.figure import Figure
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
from datetime import datetime

EMAIL_PATTERN = re.compile(r"^[^@\s]+@[^@\s]+\.[^@\s]+$")


def is_valid_email(email):
    return bool(EMAIL_PATTERN.match(email))


def writeToTXT(elapsed_time, current_value,experiment_file_path):
    new_row = [f"{elapsed_time:.3f}", f"{current_value:.6e}"]
    with open(f'{experiment_file_path}', mode='a', newline='', encoding='utf-8') as file:
        writer = csv.writer(file)
        writer.writerow(new_row)



def plotToScreen(elapsed_time, current_value):
    """Helper function that stands in for updating a live plot."""
    print(f"[PLOT] Time: {elapsed_time:.3f} s | Conductivity: {current_value:.6e} A")


TAB_NAMES = ["Tab 1", "Tab 2", "Tab 3"]

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
PROFILES_PATH = os.path.join(SCRIPT_DIR, "profiles.json")
CHIPS_PATH = os.path.join(SCRIPT_DIR, "chips.json")

DEFAULT_PROFILES = [{"Name": "Me", "Email": "me@example.com"}]
DEFAULT_CHIPS = [{"Chip Name": "Sample Chip", "Chip Dimensions": "10mm x 10mm"}]

# Sentinel used to tell a consumer thread to stop waiting on its queue.
_STOP = None


def load_json(path, default):
    if not os.path.exists(path):
        save_json(path, default)
        return [dict(item) for item in default]
    try:
        with open(path, "r") as f:
            data = json.load(f)
            if isinstance(data, list):
                return data
    except (json.JSONDecodeError, OSError):
        pass
    save_json(path, default)
    return [dict(item) for item in default]


def save_json(path, data):
    with open(path, "w") as f:
        json.dump(data, f, indent=2)


class VerticalTabsApp(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("Pennathur Lab Current Monitoring GUI by Oliver Hakansson TM")
        self.geometry("900x550")

        # --- Application color palette ---
        self.colors = {
            "background": "#EBF4DD",
            "secondary": "#90AB8B",
            "accent": "#5A7863",
            "dark": "#3B4953",
            "white": "#F8FBF3",
        }
        self.configure(bg=self.colors["background"])

        self.active_tab = tk.StringVar(value="Tab 1")
        self.tab_buttons = {}
        self.tab_frames = {}  # name -> frame containing that tab's widgets

        # PyVISA / Keithley instrument variables
        self.rm = None
        self.keithley = None
        self.experiment_file_path = None

        # In-memory copies of the two JSON files
        self.profiles = load_json(PROFILES_PATH, DEFAULT_PROFILES)
        self.chips = load_json(CHIPS_PATH, DEFAULT_CHIPS)

        # Track which list entry (if any) is currently selected
        self.selected_profile_index = None
        self.selected_chip_index = None

        # Tab 2 experiment-builder state
        self.voltages = []      # list of floats currently staged
        self.timings = []       # list of floats (seconds) currently staged
        self.experiments = []   # list of {"voltages": [...], "timings": [...], "loops": int}

        self.save_folder = tk.StringVar(value=os.path.join(os.path.expanduser("~"), "Desktop"))

        # Queues that fan out each data point to the saving and plotting
        # consumers. Two separate queues are used (rather than one shared
        # queue) so that BOTH consumers see every data point -- a single
        # queue would only let one consumer claim each item.
        self.save_queue = queue.Queue()
        self.plot_queue = queue.Queue()
        self.save_thread = None

        # Live-plot state (Tab 3). The plot itself is only ever touched from
        # the main thread; the experiment thread just pushes data points onto
        # plot_queue, and we drain it periodically via `after()`.
        self.plot_times = []
        self.plot_values = []
        self._plot_polling_active = False

        self._build_layout()
        self._refresh_visa_resources()
        self._select_tab("Tab 1")  # initialize with first tab selected

        # Handle window closure cleanly
        self.protocol("WM_DELETE_WINDOW", self._on_close)

    # ---------------- Keithley Connection Management ----------------
    def _refresh_visa_resources(self):
        """Discovers available VISA devices and populates the drop-down menu."""
        try:
            if self.rm is None:
                self.rm = pyvisa.ResourceManager()
            resources = self.rm.list_resources()
            self.visa_combo["values"] = list(resources)
            if resources:
                self.visa_combo.current(0)
            else:
                self.visa_combo.set("No devices found")
        except Exception:
            self.visa_combo["values"] = []
            self.visa_combo.set("VISA Error")

    def connect_keithley(self):
        """Attempts to establish a connection with the selected Keithley instrument."""
        if self.keithley is not None:
            messagebox.showinfo("Already Connected", "Keithley is already connected.")
            return True

        selected_address = self.visa_combo.get().strip()
        if not selected_address or selected_address in ["No devices found", "VISA Error"]:
            messagebox.showwarning("Selection Error", "Please select a valid VISA instrument address.")
            return False

        try:
            if self.rm is None:
                self.rm = pyvisa.ResourceManager()

            self.keithley = self.rm.open_resource(selected_address)
            self.keithley.timeout = 5000
            idn = self.keithley.query("*IDN?")
            print(f"[Keithley] Successfully connected: {idn.strip()}")

            self.status_lbl.config(text="Status: Connected", foreground=self.colors["accent"])
            return True
        except Exception as e:
            messagebox.showerror("Connection Failed", f"Could not connect to {selected_address}:\n{e}")
            self.disconnect_keithley()
            return False

    def disconnect_keithley(self):
        """Safely disconnects and clears instrument resources."""
        if self.keithley is not None:
            try:
                self.keithley.close()
            except Exception:
                pass
            finally:
                self.keithley = None

        self.status_lbl.config(text="Status: Disconnected", foreground=self.colors["dark"])

    # ---------------- Layout Construction ----------------
    def _build_layout(self):
        container = ttk.Frame(self, padding=10)
        container.pack(fill="both", expand=True)

        # --- Left: vertical tab buttons ---
        style = ttk.Style(self)
        style.theme_use("clam")

        # Palette styling only — existing layout and widget placement are unchanged.
        style.configure(".", background=self.colors["background"],
                        foreground=self.colors["dark"],
                        fieldbackground=self.colors["white"])
        style.configure("TFrame", background=self.colors["background"])
        style.configure("TLabel", background=self.colors["background"],
                        foreground=self.colors["dark"])
        style.configure("TLabelframe", background=self.colors["background"],
                        foreground=self.colors["dark"],
                        bordercolor=self.colors["secondary"])
        style.configure("TLabelframe.Label", background=self.colors["background"],
                        foreground=self.colors["dark"],
                        font=("TkDefaultFont", 9, "bold"))
        style.configure("TEntry", fieldbackground=self.colors["white"],
                        foreground=self.colors["dark"],
                        bordercolor=self.colors["secondary"])
        style.configure("TCombobox", fieldbackground=self.colors["white"],
                        foreground=self.colors["dark"],
                        background=self.colors["white"],
                        arrowcolor=self.colors["accent"])
        style.configure("TButton", background=self.colors["secondary"],
                        foreground=self.colors["dark"],
                        bordercolor=self.colors["accent"],
                        lightcolor=self.colors["secondary"],
                        darkcolor=self.colors["accent"],
                        padding=(8, 5),
                        font=("TkDefaultFont", 9, "bold"))
        style.map("TButton",
                  background=[("active", self.colors["accent"]),
                              ("pressed", self.colors["accent"])],
                  foreground=[("active", self.colors["white"]),
                              ("pressed", self.colors["white"])])
        style.configure("Tab.TButton", padding=0,
                        font=("TkDefaultFont", 8, "bold"),
                        background=self.colors["secondary"],
                        foreground=self.colors["dark"],
                        bordercolor=self.colors["accent"])
        style.map("Tab.TButton",
                  background=[("active", self.colors["accent"]),
                              ("pressed", self.colors["accent"])],
                  foreground=[("active", self.colors["white"]),
                              ("pressed", self.colors["white"])])

        # Native Tk listboxes use the same palette.
        self.option_add("*Listbox.background", self.colors["white"])
        self.option_add("*Listbox.foreground", self.colors["dark"])
        self.option_add("*Listbox.selectBackground", self.colors["accent"])
        self.option_add("*Listbox.selectForeground", self.colors["white"])

        tab_bar = ttk.Frame(container)
        tab_bar.pack(side="left", fill="y", padx=(0, 10))

        for name in TAB_NAMES:
            btn = ttk.Button(
                tab_bar,
                text=name,
                width=8,
                style="Tab.TButton",
                command=lambda n=name: self._select_tab(n),
            )
            btn.pack(side="top", fill="x", pady=0)
            self.tab_buttons[name] = btn

        # --- Resizable area: content pane (middle) + side pane (right) ---
        paned = ttk.PanedWindow(container, orient="horizontal")
        paned.pack(side="left", fill="both", expand=True)

        content_frame = ttk.LabelFrame(paned, text="Tab Content", padding=10)
        content_frame.rowconfigure(0, weight=1)
        content_frame.columnconfigure(0, weight=1)

        self._build_tab1(content_frame)
        self._build_tab2(content_frame)
        self._build_tab3(content_frame)

        # --- Right: static side panels ---
        side_column = ttk.Frame(paned)
        side_column.rowconfigure(0, weight=1)
        side_column.rowconfigure(1, weight=2)
        side_column.columnconfigure(0, weight=1)

        # Top Right Panel: Connection Status & Device Selection
        self.side_box_top = ttk.LabelFrame(side_column, text="Keithley Connection", padding=10)
        self.side_box_top.grid(row=0, column=0, sticky="nsew")
        self.side_box_top.columnconfigure(1, weight=1)

        # Status Label
        self.status_lbl = ttk.Label(
            self.side_box_top,
            text="Status: Disconnected",
            foreground=self.colors["dark"],
            font=("TkDefaultFont", 9, "bold"),
        )
        self.status_lbl.grid(row=0, column=0, columnspan=2, sticky="w", pady=(0, 6))

        # Device Selection Combobox
        ttk.Label(self.side_box_top, text="Device:").grid(row=1, column=0, sticky="w", pady=4)
        self.visa_combo = ttk.Combobox(self.side_box_top, state="readonly")
        self.visa_combo.grid(row=1, column=1, sticky="ew", pady=4, padx=(4, 0))

        # Refresh, Connect, Disconnect Action Buttons
        btn_frame = ttk.Frame(self.side_box_top)
        btn_frame.grid(row=2, column=0, columnspan=2, sticky="ew", pady=(8, 0))

        ttk.Button(btn_frame, text="Refresh", command=self._refresh_visa_resources).pack(side="left", padx=(0, 2))
        ttk.Button(btn_frame, text="Connect", command=self.connect_keithley).pack(side="left", padx=2)
        ttk.Button(btn_frame, text="Disconnect", command=self.disconnect_keithley).pack(side="left", padx=2)

        # Top Right Panel (Tab 3 only): Live Data Plot. Occupies the same
        # grid cell as the Keithley connection panel above; only one of the
        # two is visible at a time (toggled in _select_tab).
        self.side_box_plot = ttk.LabelFrame(side_column, text="Live Data (|Current|)", padding=10)
        self.side_box_plot.grid(row=0, column=0, sticky="nsew")
        self.side_box_plot.grid_remove()

        self.fig = Figure(figsize=(4, 3), dpi=100,
                          facecolor=self.colors["background"])
        self.ax = self.fig.add_subplot(111)
        self.ax.set_facecolor(self.colors["white"])
        self.ax.set_xlabel("Time (s)", color=self.colors["dark"])
        self.ax.set_ylabel("|Current| (A)", color=self.colors["dark"])
        self.ax.tick_params(colors=self.colors["dark"])
        for spine in self.ax.spines.values():
            spine.set_color(self.colors["secondary"])
        (self.plot_line,) = self.ax.plot(
            [], [], marker="o", markersize=2, linestyle="-",
            color=self.colors["accent"])
        self.fig.tight_layout()

        self.plot_canvas = FigureCanvasTkAgg(self.fig, master=self.side_box_plot)
        self.plot_canvas.get_tk_widget().pack(fill="both", expand=True)

        # Tab 3 has no content widgets of its own; the graph is the complete
        # upper-right section and Logs remains the complete lower-right section.


        # Bottom Right Panel: Logs
        side_box_bottom = ttk.LabelFrame(side_column, text="Logs", padding=8)
        side_box_bottom.grid(row=1, column=0, sticky="nsew", pady=(10, 0))

        paned.add(content_frame, weight=3)
        paned.add(side_column, weight=2)

    def _make_list_box(self, parent, label_text, row, height=4):
        box_frame = ttk.LabelFrame(parent, text=label_text, padding=4)
        box_frame.grid(row=row, column=0, columnspan=4, sticky="ew", pady=(0, 8))
        box_frame.columnconfigure(0, weight=1)

        listbox = tk.Listbox(box_frame, height=height, exportselection=False,
                    bg=self.colors["white"], fg=self.colors["dark"],
                    selectbackground=self.colors["accent"],
                    selectforeground=self.colors["white"],
                    relief="flat", bd=0)
        listbox.grid(row=0, column=0, sticky="ew")

        scrollbar = ttk.Scrollbar(box_frame, orient="vertical", command=listbox.yview)
        scrollbar.grid(row=0, column=1, sticky="ns")
        listbox.config(yscrollcommand=scrollbar.set)

        return listbox

    def _build_tab1(self, parent):
        frame = ttk.Frame(parent)
        frame.grid(row=0, column=0, sticky="nsew")
        self.tab_frames["Tab 1"] = frame

        # --- Profiles list ---
        self.tab1_profile_listbox = self._make_list_box(
            frame, "Profiles (click to select)", row=0
        )
        self.tab1_profile_listbox.bind("<<ListboxSelect>>", self._on_profile_select)

        ttk.Label(frame, text="Name:").grid(row=1, column=0, sticky="w", pady=4)
        self.tab1_name_entry = ttk.Entry(frame)
        self.tab1_name_entry.grid(row=1, column=1, sticky="ew", pady=4)
        self.tab1_name_entry.bind("<KeyRelease>", self._clear_profile_selection)

        ttk.Label(frame, text="Email:").grid(row=1, column=2, sticky="w", pady=4)
        self.tab1_email_entry = ttk.Entry(frame)
        self.tab1_email_entry.grid(row=1, column=3, sticky="ew", pady=4)
        self.tab1_email_entry.bind("<KeyRelease>", self._clear_profile_selection)

        ttk.Button(
            frame, text="Add Profile", command=self._add_or_update_profile
        ).grid(row=2, column=0, pady=(4, 12), sticky="w")

        ttk.Button(
            frame, text="Delete Profile", command=self._delete_profile
        ).grid(row=2, column=1, pady=(4, 12), sticky="w")

        # --- Chips list ---
        self.tab1_chip_listbox = self._make_list_box(
            frame, "Chips (click to select)", row=3
        )
        self.tab1_chip_listbox.bind("<<ListboxSelect>>", self._on_chip_select)

        ttk.Label(frame, text="Chip Name:").grid(row=4, column=0, sticky="w", pady=4)
        self.tab1_chip_name_entry = ttk.Entry(frame)
        self.tab1_chip_name_entry.grid(row=4, column=1, sticky="ew", pady=4)
        self.tab1_chip_name_entry.bind("<KeyRelease>", self._clear_chip_selection)

        ttk.Label(frame, text="Chip Dimensions:").grid(row=4, column=2, sticky="w", pady=4)
        self.tab1_chip_dimensions_entry = ttk.Entry(frame)
        self.tab1_chip_dimensions_entry.grid(row=4, column=3, sticky="ew", pady=4)
        self.tab1_chip_dimensions_entry.bind("<KeyRelease>", self._clear_chip_selection)

        ttk.Button(
            frame, text="Add Chip", command=self._add_or_update_chip
        ).grid(row=5, column=0, pady=(4, 0), sticky="w")

        ttk.Button(
            frame, text="Delete Chip", command=self._delete_chip
        ).grid(row=5, column=1, pady=(4, 0), sticky="w")

        frame.columnconfigure(1, weight=1)
        frame.columnconfigure(3, weight=1)

        # --- Experiment Name Field ---
        ttk.Label(frame, text="Session Name:").grid(row=6, column=0, sticky="w", pady=4)
        self.tab1_experiment_name_entry = ttk.Entry(frame)
        self.tab1_experiment_name_entry.grid(row=6, column=1, sticky="ew", pady=4)

        ttk.Button(
            frame, text="Start Session", command=self._start_session
        ).grid(row=7, column=0, pady=(8, 0), sticky="w")

        self._refresh_profile_list()
        self._refresh_chip_list()

    def _start_session(self):
        """Reads Tab 1 inputs, populates the top bar of Tab 2, and switches to Tab 2."""
        session_data = {
            "Session": self.tab1_experiment_name_entry.get().strip(),
            "Name": self.tab1_name_entry.get().strip(),
            "Email": self.tab1_email_entry.get().strip(),
            "Chip": self.tab1_chip_name_entry.get().strip(),
            "Dims": self.tab1_chip_dimensions_entry.get().strip(),
        }

        # Update header bar labels on Tab 2
        self.tab2_session_lbl.config(text=session_data["Session"] or "N/A")
        self.tab2_profile_lbl.config(
            text=f"{session_data['Name']} ({session_data['Email']})"
            if session_data["Name"]
            else "N/A"
        )
        self.tab2_chip_lbl.config(
            text=f"{session_data['Chip']} [{session_data['Dims']}]"
            if session_data["Chip"]
            else "N/A"
        )

        self._select_tab("Tab 2")

    # ---------------- Profiles: list <-> fields <-> JSON ----------------
    def _refresh_profile_list(self):
        self.tab1_profile_listbox.delete(0, "end")
        for profile in self.profiles:
            name = profile.get("Name", "")
            email = profile.get("Email", "")
            self.tab1_profile_listbox.insert("end", f"{name}  <{email}>")

    def _on_profile_select(self, event=None):
        selection = self.tab1_profile_listbox.curselection()
        if not selection:
            return
        index = selection[0]
        self.selected_profile_index = index
        profile = self.profiles[index]

        self.tab1_name_entry.delete(0, "end")
        self.tab1_name_entry.insert(0, profile.get("Name", ""))
        self.tab1_email_entry.delete(0, "end")
        self.tab1_email_entry.insert(0, profile.get("Email", ""))

    def _clear_profile_selection(self, event=None):
        if self.selected_profile_index is not None:
            self.selected_profile_index = None
            self.tab1_profile_listbox.selection_clear(0, "end")

    def _add_or_update_profile(self):
        name = self.tab1_name_entry.get().strip()
        email = self.tab1_email_entry.get().strip()

        if not name:
            messagebox.showwarning("Missing name", "Please enter a name before adding a profile.")
            return

        if not is_valid_email(email):
            messagebox.showwarning(
                "Invalid email",
                f"'{email}' doesn't look like a valid email address (e.g. name@example.com).",
            )
            return

        if self.selected_profile_index is not None:
            self.profiles[self.selected_profile_index] = {"Name": name, "Email": email}
        else:
            self.profiles.append({"Name": name, "Email": email})

        save_json(PROFILES_PATH, self.profiles)
        self._refresh_profile_list()

    def _delete_profile(self):
        if self.selected_profile_index is None:
            messagebox.showinfo("No profile selected", "Click a profile in the list first to delete it.")
            return

        profile = self.profiles[self.selected_profile_index]
        confirmed = messagebox.askyesno(
            "Delete profile",
            f"Are you sure you want to delete '{profile.get('Name', '')}'?",
        )
        if not confirmed:
            return

        del self.profiles[self.selected_profile_index]
        save_json(PROFILES_PATH, self.profiles)
        self.selected_profile_index = None
        self.tab1_name_entry.delete(0, "end")
        self.tab1_email_entry.delete(0, "end")
        self._refresh_profile_list()

    # ---------------- Chips: list <-> fields <-> JSON ----------------
    def _refresh_chip_list(self):
        self.tab1_chip_listbox.delete(0, "end")
        for chip in self.chips:
            chip_name = chip.get("Chip Name", "")
            dims = chip.get("Chip Dimensions", "")
            self.tab1_chip_listbox.insert("end", f"{chip_name}  ({dims})")

    def _on_chip_select(self, event=None):
        selection = self.tab1_chip_listbox.curselection()
        if not selection:
            return
        index = selection[0]
        self.selected_chip_index = index
        chip = self.chips[index]

        self.tab1_chip_name_entry.delete(0, "end")
        self.tab1_chip_name_entry.insert(0, chip.get("Chip Name", ""))
        self.tab1_chip_dimensions_entry.delete(0, "end")
        self.tab1_chip_dimensions_entry.insert(0, chip.get("Chip Dimensions", ""))

    def _clear_chip_selection(self, event=None):
        if self.selected_chip_index is not None:
            self.selected_chip_index = None
            self.tab1_chip_listbox.selection_clear(0, "end")

    def _add_or_update_chip(self):
        chip_name = self.tab1_chip_name_entry.get().strip()
        dims = self.tab1_chip_dimensions_entry.get().strip()

        if not chip_name:
            messagebox.showwarning("Missing chip name", "Please enter a chip name before adding a chip.")
            return

        if self.selected_chip_index is not None:
            self.chips[self.selected_chip_index] = {"Chip Name": chip_name, "Chip Dimensions": dims}
        else:
            self.chips.append({"Chip Name": chip_name, "Chip Dimensions": dims})

        save_json(CHIPS_PATH, self.chips)
        self._refresh_chip_list()

    def _delete_chip(self):
        if self.selected_chip_index is None:
            messagebox.showinfo("No chip selected", "Click a chip in the list first to delete it.")
            return

        chip = self.chips[self.selected_chip_index]
        confirmed = messagebox.askyesno(
            "Delete chip",
            f"Are you sure you want to delete '{chip.get('Chip Name', '')}'?",
        )
        if not confirmed:
            return

        del self.chips[self.selected_chip_index]
        save_json(CHIPS_PATH, self.chips)
        self.selected_chip_index = None
        self.tab1_chip_name_entry.delete(0, "end")
        self.tab1_chip_dimensions_entry.delete(0, "end")
        self._refresh_chip_list()

    # ---------------- Tab 2 Construction ----------------
    def _build_tab2(self, parent):
        frame = ttk.Frame(parent)
        frame.grid(row=0, column=0, sticky="nsew")
        self.tab_frames["Tab 2"] = frame

        # --- Horizontal Header Bar Across the Top ---
        header_bar = ttk.Frame(frame, padding=(6, 4))
        header_bar.pack(fill="x", side="top", pady=(0, 10))

        ttk.Label(header_bar, text="Session:", font=("TkDefaultFont", 9, "bold")).pack(side="left", padx=(0, 2))
        self.tab2_session_lbl = ttk.Label(header_bar, text="Not started")
        self.tab2_session_lbl.pack(side="left", padx=(0, 15))

        ttk.Label(header_bar, text="Profile:", font=("TkDefaultFont", 9, "bold")).pack(side="left", padx=(0, 2))
        self.tab2_profile_lbl = ttk.Label(header_bar, text="N/A")
        self.tab2_profile_lbl.pack(side="left", padx=(0, 15))

        ttk.Label(header_bar, text="Chip:", font=("TkDefaultFont", 9, "bold")).pack(side="left", padx=(0, 2))
        self.tab2_chip_lbl = ttk.Label(header_bar, text="N/A")
        self.tab2_chip_lbl.pack(side="left", padx=(0, 5))

        ttk.Separator(frame, orient="horizontal").pack(fill="x", side="top", pady=(0, 10))

        # Body area for Tab 2 content: experiment builder
        body_frame = ttk.Frame(frame)
        body_frame.pack(fill="both", expand=True)

        # --- Voltages input list ---
        voltages_frame = ttk.LabelFrame(body_frame, text="Voltages (V)", padding=8)
        voltages_frame.pack(fill="x", pady=(0, 8))
        voltages_frame.columnconfigure(0, weight=1)

        self.tab2_voltage_listbox = tk.Listbox(voltages_frame, height=4, exportselection=False,
            bg=self.colors["white"], fg=self.colors["dark"],
            selectbackground=self.colors["accent"],
            selectforeground=self.colors["white"],
            relief="flat", bd=0)
        self.tab2_voltage_listbox.grid(row=0, column=0, columnspan=3, sticky="ew", pady=(0, 4))

        self.tab2_voltage_entry = ttk.Entry(voltages_frame, width=12)
        self.tab2_voltage_entry.grid(row=1, column=0, sticky="w")
        self.tab2_voltage_entry.bind("<Return>", lambda e: self._add_voltage())

        ttk.Button(voltages_frame, text="Add Voltage", command=self._add_voltage).grid(
            row=1, column=1, padx=4
        )
        ttk.Button(
            voltages_frame, text="Remove Selected", command=self._remove_voltage
        ).grid(row=1, column=2)

        # --- Timings input list ---
        timings_frame = ttk.LabelFrame(body_frame, text="Timings (s)", padding=8)
        timings_frame.pack(fill="x", pady=(0, 8))
        timings_frame.columnconfigure(0, weight=1)

        self.tab2_timing_listbox = tk.Listbox(timings_frame, height=4, exportselection=False,
            bg=self.colors["white"], fg=self.colors["dark"],
            selectbackground=self.colors["accent"],
            selectforeground=self.colors["white"],
            relief="flat", bd=0)
        self.tab2_timing_listbox.grid(row=0, column=0, columnspan=3, sticky="ew", pady=(0, 4))

        self.tab2_timing_entry = ttk.Entry(timings_frame, width=12)
        self.tab2_timing_entry.grid(row=1, column=0, sticky="w")
        self.tab2_timing_entry.bind("<Return>", lambda e: self._add_timing())

        ttk.Button(timings_frame, text="Add Timing", command=self._add_timing).grid(
            row=1, column=1, padx=4
        )
        ttk.Button(
            timings_frame, text="Remove Selected", command=self._remove_timing
        ).grid(row=1, column=2)

        # --- Experiment loops ---
        loops_frame = ttk.Frame(body_frame)
        loops_frame.pack(fill="x", pady=(0, 8))
        ttk.Label(loops_frame, text="Experiment Loops:").pack(side="left", padx=(0, 6))
        self.tab2_loops_entry = ttk.Entry(loops_frame, width=10)
        self.tab2_loops_entry.pack(side="left")

        # --- Add Experiment button ---
        ttk.Button(
            body_frame, text="Add Experiment", command=self._add_experiment
        ).pack(anchor="w", pady=(0, 10))

        # --- Queued experiments list ---
        experiments_frame = ttk.LabelFrame(body_frame, text="Experiments Queue", padding=8)
        experiments_frame.pack(fill="both", expand=True)
        experiments_frame.columnconfigure(0, weight=1)
        experiments_frame.rowconfigure(0, weight=1)

        self.tab2_experiments_listbox = tk.Listbox(experiments_frame, height=6, exportselection=False,
            bg=self.colors["white"], fg=self.colors["dark"],
            selectbackground=self.colors["accent"],
            selectforeground=self.colors["white"],
            relief="flat", bd=0)
        self.tab2_experiments_listbox.grid(row=0, column=0, sticky="nsew")

        exp_scrollbar = ttk.Scrollbar(
            experiments_frame, orient="vertical", command=self.tab2_experiments_listbox.yview
        )
        exp_scrollbar.grid(row=0, column=1, sticky="ns")
        self.tab2_experiments_listbox.config(yscrollcommand=exp_scrollbar.set)

        save_folder_frame = ttk.Frame(body_frame)
        save_folder_frame.pack(fill="x", pady=(8, 0))
        save_folder_frame.columnconfigure(1, weight=1)

        ttk.Label(save_folder_frame, text="Save Folder:").grid(row=0, column=0, sticky="w", padx = (0,6))

        self.tab2_save_folder_entry = ttk.Entry(save_folder_frame, textvariable=self.save_folder)
        self.tab2_save_folder_entry.grid(row=0, column=1, sticky="ew", padx=(6, 0))

        ttk.Button(save_folder_frame, text="Browse...", command=self._choose_save_folder).grid(row=0, column=2, padx=(6, 0))

        # --- Run Experiments Button ---
        ttk.Button(
            body_frame, text="Run Experiments", command=self._start_experiments_thread
        ).pack(anchor="w", pady=(8, 0))


    def _choose_save_folder(self):
        folder = filedialog.askdirectory(title="Select Save Folder", initialdir=self.save_folder.get())
        if folder:
            self.save_folder.set(folder)
    # ---------------- Tab 2: Consumer thread (saving) & main-thread plot poller ----------------
    def _saving_worker(self):
        """Consumer thread: pulls data points off save_queue one at a time and
        logs/saves each one, removing it from the queue before moving to the next."""
        while True:
            item = self.save_queue.get()
            if item is _STOP:
                self.save_queue.task_done()
                break
            elapsed_time, current_value = item
            writeToTXT(elapsed_time, current_value, self.experiment_file_path)
            self.save_queue.task_done()

    def _poll_plot_queue(self):
        """Runs on the main thread via `after()` and drains any data points the
        experiment thread has pushed onto plot_queue, plotting the absolute
        value of the current in the Tab 3 live-plot panel. Tkinter/matplotlib
        widgets are only ever touched here, never from the worker threads."""
        updated = False
        try:
            while True:
                item = self.plot_queue.get_nowait()
                if item is _STOP:
                    self.plot_queue.task_done()
                    self._plot_polling_active = False
                    if updated:
                        self._redraw_plot()
                    return
                elapsed_time, current_value = item
                abs_value = abs(current_value)
                self.plot_times.append(elapsed_time)
                self.plot_values.append(abs_value)
                plotToScreen(elapsed_time, abs_value)
                updated = True
                self.plot_queue.task_done()
        except queue.Empty:
            pass

        if updated:
            self._redraw_plot()

        if self._plot_polling_active:
            self.after(150, self._poll_plot_queue)

    def _redraw_plot(self):
        self.plot_line.set_data(self.plot_times, self.plot_values)
        self.ax.relim()
        self.ax.autoscale_view()
        self.plot_canvas.draw_idle()

    # ---------------- Tab 2: Execution & Validation ----------------
    def _start_experiments_thread(self):
        if not self.experiments:
            messagebox.showwarning("Empty Queue", "There are ZERO experiments in the queue to run. SLACKER")
            return

        # Start the consumer thread that will drain save_queue as the
        # producer (the experiment thread) fills it.
        self.save_thread = threading.Thread(target=self._saving_worker, daemon=True)
        self.save_thread.start()

        # Reset the live plot and start draining plot_queue on the main
        # thread (Tkinter/matplotlib aren't thread-safe, so this can't be
        # done from a worker thread).
        self.plot_times = []
        self.plot_values = []
        self._redraw_plot()
        self._plot_polling_active = True
        self.after(150, self._poll_plot_queue)

        # Jump over to Tab 3 so the live plot is visible while running.
        self._select_tab("Tab 3")

        headers = ['Timing', 'Current']

        profile_name = "Unknown"
        if self.selected_profile_index is not None:
            profile_name = self.profiles[self.selected_profile_index].get("Name", "Unknown")

        timestamp = datetime.now().strftime("%Y-%m-%d_%H-%M-%S")
        save_folder = self.save_folder.get().strip() or os.path.expanduser("~/Desktop")
        os.makedirs(save_folder, exist_ok=True)
        self.experiment_file_path = os.path.join(save_folder, f'{profile_name} - {timestamp}.csv')

        with open(self.experiment_file_path, mode='w', newline='', encoding='utf-8') as file:
            writer = csv.writer(file)
            writer.writerow(headers)

        thread = threading.Thread(target=self._run_experiments, daemon=True)
        thread.start()

    def _run_experiments(self):
        # Raise error immediately if hardware is disconnected
        if self.keithley is None:
            error_msg = "Cannot start experiment: Keithley instrument is not connected! I thought you've done this before?"
            messagebox.showerror("Connection Error", error_msg)
            self.save_queue.put(_STOP)
            self.plot_queue.put(_STOP)
            raise RuntimeError(error_msg)

        try:
            for idx, exp in enumerate(self.experiments, start=1):

                experiment_data = {"data_points": []}
                current_voltages = exp["voltages"]
                current_timings = exp["timings"]
                experiment_loops = exp["loops"]

                # Initialize output zero and turn output ON
                self.keithley.write("SOUR:VOLT 0")
                self.keithley.write("OUTP ON")

                experiment_start_time = time.time()
                first_data_point = False

                for h in range(experiment_loops):
                    length = min(len(current_timings), len(current_voltages))

                    for i in range(length):
                        cycle_start_time = time.time()
                        target_voltage = float(current_voltages[i])
                        target_duration = float(current_timings[i])

                        self.keithley.write(f"SOUR:VOLT {target_voltage}")

                        while (cycle_start_time + target_duration) > time.time():
                            if self.keithley is None:
                                raise RuntimeError("Keithley connection lost mid-experiment!")

                            current_val = self.keithley.query("MEAS:CURR?")

                            if not first_data_point:
                                first_data_point = True
                                experiment_start_time = time.time()

                            elapsed_time = time.time() - experiment_start_time
                            match = re.match(r"([+-]?\d+\.?\d*(?: Ee[+-]?\d+)?)", current_val.strip(), re.IGNORECASE)
                            if match:
                                current_value = float(match.group(1))

                            experiment_data["data_points"].append({
                                "time": elapsed_time,
                                "conductivity": current_value
                            })

                            # Push the same data point onto BOTH queues so the
                            # saving thread and the plot poller each get
                            # their own copy to consume independently.
                            data_point = (elapsed_time, current_value)
                            self.save_queue.put(data_point)
                            self.plot_queue.put(data_point)

                self.keithley.write("SOUR:VOLT 0")
                self.keithley.write("OUTP OFF")

        except Exception as e:
            import traceback
            print("[EXPERIMENT ERROR] The experiment thread stopped early:")
            traceback.print_exc()
            if self.keithley is not None:
                try:
                    self.keithley.write("SOUR:VOLT 0")
                    self.keithley.write("OUTP OFF")
                except Exception:
                    pass
        finally:
            # Tell both consumers there's no more data coming so they can
            # stop instead of blocking/polling forever.
            self.save_queue.put(_STOP)
            self.plot_queue.put(_STOP)

    # ---------------- Tab 2: Voltages list <-> entry ----------------
    def _add_voltage(self):
        raw = self.tab2_voltage_entry.get().strip()
        if not raw:
            return
        try:
            value = float(raw)
        except ValueError:
            messagebox.showwarning("Invalid voltage", f"'{raw}' is not a valid number.")
            return

        self.voltages.append(value)
        self.tab2_voltage_listbox.insert("end", f"{value} V")
        self.tab2_voltage_entry.delete(0, "end")

    def _remove_voltage(self):
        selection = self.tab2_voltage_listbox.curselection()
        if not selection:
            messagebox.showinfo(
                "No voltage selected", "Click a voltage in the list first to remove it."
            )
            return
        index = selection[0]
        del self.voltages[index]
        self.tab2_voltage_listbox.delete(index)

    # ---------------- Tab 2: Timings list <-> entry ----------------
    def _add_timing(self):
        raw = self.tab2_timing_entry.get().strip()
        if not raw:
            return
        try:
            value = float(raw)
        except ValueError:
            messagebox.showwarning("Invalid timing", f"'{raw}' is not a valid number.")
            return

        self.timings.append(value)
        self.tab2_timing_listbox.insert("end", f"{value} s")
        self.tab2_timing_entry.delete(0, "end")

    def _remove_timing(self):
        selection = self.tab2_timing_listbox.curselection()
        if not selection:
            messagebox.showinfo(
                "No timing selected", "Click a timing in the list first to remove it."
            )
            return
        index = selection[0]
        del self.timings[index]
        self.tab2_timing_listbox.delete(index)

    # ---------------- Tab 2: Add Experiment ----------------
    def _add_experiment(self):
        raw_loops = self.tab2_loops_entry.get().strip()
        if not raw_loops:
            messagebox.showwarning("Missing loops", "Please enter a number of experiment loops.")
            return
        try:
            loops = int(raw_loops)
        except ValueError:
            messagebox.showwarning("Invalid loops", f"'{raw_loops}' is not a whole number.")
            return

        if not self.voltages:
            messagebox.showwarning("No voltages", "Add at least one voltage before adding an experiment.")
            return
        if not self.timings:
            messagebox.showwarning("No timings", "Add at least one timing before adding an experiment.")
            return

        if len(self.voltages) != len(self.timings):
            messagebox.showwarning(
                "Length Mismatch", 
                "The number of voltages and timings must match before adding an experiment."
            )
            return

        experiment = {
            "voltages": list(self.voltages),
            "timings": list(self.timings),
            "loops": loops,
        }
        self.experiments.append(experiment)

        summary = f"V={experiment['voltages']}  T={experiment['timings']}  Loops={loops}"
        self.tab2_experiments_listbox.insert("end", summary)

    # ---------------- Tab 3 Construction ----------------
    def _build_tab3(self, parent):
        # Tab 3 content area is intentionally empty.
        # The right-hand top panel is the live graph and the lower panel is logs.
        frame = ttk.Frame(parent)
        frame.grid(row=0, column=0, sticky="nsew")
        self.tab_frames["Tab 3"] = frame

    def _select_tab(self, name):
        self.active_tab.set(name)

        for tab_name, btn in self.tab_buttons.items():
            if tab_name == name:
                btn.state(["pressed"])
            else:
                btn.state(["!pressed"])

        self.tab_frames[name].tkraise()

        # On Tab 3, hide the Keithley connection panel and show the live
        # data plot in its place; on Tab 1 & Tab 2, show the connection
        # panel and hide the plot.
        if name == "Tab 3":
            self.side_box_top.grid_remove()
            self.side_box_plot.grid()
        else:
            self.side_box_top.grid()
            self.side_box_plot.grid_remove()

    def _on_close(self):
        """Clean shutdown handler for window exit."""
        self.disconnect_keithley()
        self.destroy()


if __name__ == "__main__":
    app = VerticalTabsApp()
    app.mainloop()