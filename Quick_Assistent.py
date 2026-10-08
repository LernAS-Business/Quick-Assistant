from __future__ import annotations

import base64
import ctypes
from collections.abc import Callable
from concurrent.futures import (
    ThreadPoolExecutor,
    TimeoutError as FuturesTimeoutError,
    as_completed,
)
from dataclasses import dataclass
import html
from http.client import HTTPException
from html.parser import HTMLParser
import json
import math
import os
from pathlib import Path
import queue
import re
import shutil
import subprocess
import threading
import tkinter as tk
from tkinter import font as tkfont, messagebox
from typing import cast
from urllib.error import URLError
from urllib.parse import parse_qs, quote_plus, unquote, urlparse
from urllib.request import Request, urlopen
import webbrowser


SEARCH_ENGINES = {
    "Bing": "https://www.bing.com/search?q={query}",
    "DuckDuckGo": "https://lite.duckduckgo.com/lite/?q={query}",
    "Yahoo": "https://search.yahoo.com/search?p={query}",
    "Google": "https://www.google.com/search?q={query}&num=10",
    "Brave": "https://search.brave.com/search?q={query}",
    "Mojeek": "https://www.mojeek.com/search?q={query}",
    "Startpage": "https://www.startpage.com/sp/search?query={query}",
    "Ecosia": "https://www.ecosia.org/search?q={query}",
    "Qwant": "https://www.qwant.com/?q={query}&t=web",
    "Wikipedia": (
        "https://en.wikipedia.org/w/api.php?action=query&list=search"
        "&format=json&srlimit=10&srsearch={query}"
    ),
    "Wikipedia (Deutsch)": (
        "https://de.wikipedia.org/w/api.php?action=query&list=search"
        "&format=json&srlimit=10&srsearch={query}"
    ),
}
SEARCH_REQUEST_TIMEOUT = 20
SEARCH_TOTAL_TIMEOUT = 45
WINDOW_OPACITY = 0.9
GLASS_BACKGROUND = "#171a21"
GLASS_CARD = "#292f3a"
GLASS_INPUT = "#12151c"
GLASS_BORDER = "#536078"
USER_AGENT = "Mozilla/5.0 (Windows NT 10.0; Win64; x64) QuickAssistent/1.0"
GREETING = "Hallo! Ich bin Quick Assistent. Wie kann ich dir heute weiterhelfen?"
GLASS_ACCENT = "#6da9ff"
APP_ALIASES = {
    "editor": "notepad.exe",
    "notepad": "notepad.exe",
    "rechner": "calc.exe",
    "taschenrechner": "calc.exe",
    "calculator": "calc.exe",
    "paint": "mspaint.exe",
    "datei explorer": "explorer.exe",
    "file explorer": "explorer.exe",
    "explorer": "explorer.exe",
    "eingabeaufforderung": "cmd.exe",
    "command prompt": "cmd.exe",
    "cmd": "cmd.exe",
    "powershell": "powershell.exe",
    "edge": "msedge.exe",
    "microsoft edge": "msedge.exe",
    "chrome": "chrome.exe",
    "google chrome": "chrome.exe",
    "firefox": "firefox.exe",
    "vscode": "code.exe",
    "visual studio code": "code.exe",
}

@dataclass(frozen=True)
class SearchResult:
    title: str
    url: str
    snippet: str
    engine: str


class RoundedBubble(tk.Canvas):
    def __init__(
        self,
        master: tk.Misc,
        text: str,
        title: str = "",
        thinking: bool = False,
    ) -> None:
        super().__init__(
            master,
            height=48,
            background=GLASS_BACKGROUND,
            borderwidth=0,
            highlightthickness=0,
        )
        self.text = text
        self.title = title
        self.thinking = thinking
        self.body_font = tkfont.Font(
            root=self,
            family="Segoe UI",
            size=10,
            weight="normal",
        )
        self.title_font = tkfont.Font(
            root=self, family="Segoe UI Semibold", size=11, weight="bold"
        )
        self.bind("<Configure>", self.redraw)
        self.redraw()

    def wrap_lines(self, text: str, font: tkfont.Font, max_width: int) -> list[str]:
        lines: list[str] = []
        for paragraph in text.splitlines() or [""]:
            if not paragraph:
                lines.append("")
                continue
            line = ""
            for word in paragraph.split():
                candidate = f"{line} {word}".strip()
                if line and font.measure(candidate) > max_width:
                    lines.append(line)
                    line = word
                else:
                    line = candidate
            lines.append(line)
        return lines or [""]

    @staticmethod
    def rounded_points(width: int, height: int, radius: int) -> list[float]:
        points: list[float] = []
        corners = (
            (radius, radius, 180, 270),
            (width - radius, radius, 270, 360),
            (width - radius, height - radius, 0, 90),
            (radius, height - radius, 90, 180),
        )
        for center_x, center_y, start, end in corners:
            for step in range(7):
                angle = math.radians(start + (end - start) * step / 6)
                points.extend(
                    (
                        center_x + radius * math.cos(angle),
                        center_y + radius * math.sin(angle),
                    )
                )
        return points

    def redraw(self, _event: tk.Event[tk.Misc] | None = None) -> None:
        width = max(self.winfo_width(), 300)
        padding_x = 16
        line_gap = 4
        content_width = width - padding_x * 2
        title_lines = self.wrap_lines(self.title, self.title_font, content_width) if self.title else []
        body_lines = self.wrap_lines(self.text, self.body_font, content_width)
        title_height = len(title_lines) * (self.title_font.metrics("linespace") + line_gap)
        body_height = len(body_lines) * (self.body_font.metrics("linespace") + line_gap)
        title_gap = 5 if title_lines else 0
        height = max(48 if self.thinking else 58, 16 + title_height + title_gap + body_height + 12)
        if self.winfo_reqheight() != height:
            self.configure(height=height)

        self.delete("all")
        if not self.thinking:
            self.create_polygon(
                self.rounded_points(width - 1, height - 1, min(16, height // 2)),
                smooth=True,
                splinesteps=24,
                fill=GLASS_CARD,
                outline=GLASS_BORDER,
                width=1,
            )

        y = 12
        for line in title_lines:
            self.create_text(
                padding_x,
                y,
                text=line,
                font=self.title_font,
                fill="#ffffff",
                anchor="nw",
            )
            y += self.title_font.metrics("linespace") + line_gap
        if title_lines:
            y += title_gap
        for line in body_lines:
            self.create_text(
                padding_x,
                y,
                text=line,
                font=self.body_font,
                fill="#cbd3e1" if self.thinking else "#f4f6fa",
                anchor="nw",
            )
            y += self.body_font.metrics("linespace") + line_gap


class RoundedMessageLog(tk.Frame):
    def __init__(self, master: tk.Misc) -> None:
        super().__init__(master, background=GLASS_BACKGROUND)
        self._scroll_bindtag = f"RoundedMessageLog_{id(self)}"
        self.bind_class(
            self._scroll_bindtag, "<MouseWheel>", self.on_mousewheel
        )
        self.canvas = tk.Canvas(
            self,
            background=GLASS_BACKGROUND,
            borderwidth=0,
            highlightthickness=0,
        )
        self.scrollbar = tk.Scrollbar(
            self, orient="vertical", command=self.canvas.yview
        )
        self.canvas.configure(yscrollcommand=self.scrollbar.set)
        self.scrollbar.pack(side="right", fill="y")
        self.canvas.pack(side="left", fill="both", expand=True)
        self.messages = tk.Frame(self.canvas, background=GLASS_BACKGROUND)
        self.window_id = self.canvas.create_window(
            (0, 0), window=self.messages, anchor="nw"
        )
        for widget in (self.canvas, self.scrollbar, self.messages):
            self.enable_mousewheel(widget)
        self.messages.bind("<Configure>", self.update_scroll_region)
        self.canvas.bind("<Configure>", self.resize_messages)
        self.bind("<Destroy>", self.remove_scroll_binding, add="+")

    def update_scroll_region(self, _event: tk.Event[tk.Misc] | None = None) -> None:
        self.canvas.configure(scrollregion=self.canvas.bbox("all"))

    def resize_messages(self, event: tk.Event[tk.Misc]) -> None:
        self.canvas.itemconfigure(self.window_id, width=event.width)

    def enable_mousewheel(self, widget: tk.Widget) -> None:
        bindtags = widget.bindtags()
        if self._scroll_bindtag not in bindtags:
            widget.bindtags((*bindtags, self._scroll_bindtag))

    def on_mousewheel(self, event: tk.Event[tk.Misc]) -> str:
        if self.winfo_exists() and event.delta:
            steps = -int(event.delta / 120)
            if steps == 0:
                steps = -1 if event.delta > 0 else 1
            self.canvas.yview_scroll(steps, "units")
        return "break"

    def remove_scroll_binding(self, event: tk.Event[tk.Misc]) -> None:
        if event.widget is self:
            self.unbind_class(self._scroll_bindtag, "<MouseWheel>")

    def add_speaker(self, speaker: str) -> None:
        color = "#a9caff" if speaker == "Assistent" else "#e0e5ee"
        speaker_label = tk.Label(
            self.messages,
            text=speaker,
            background=GLASS_BACKGROUND,
            foreground=color,
            font=("Segoe UI Semibold", 9),
            anchor="w",
        )
        self.enable_mousewheel(speaker_label)
        speaker_label.pack(fill="x", padx=8, pady=(4, 2))

    def add_message(
        self,
        speaker: str,
        text: str,
        *,
        title: str = "",
        thinking: bool = False,
        source_url: str | None = None,
    ) -> tk.Widget:
        if not thinking:
            self.add_speaker(speaker)
        message_frame = tk.Frame(self.messages, background=GLASS_BACKGROUND)
        bubble = RoundedBubble(
            message_frame, text=text, title=title, thinking=thinking
        )
        self.enable_mousewheel(bubble)
        bubble.pack(fill="x", padx=(2, 2), pady=(0, 10 if not thinking else 5))
        if (
            speaker == "Assistent"
            and not thinking
            and not (text == GREETING and not title and source_url is None)
        ):
            actions = tk.Frame(message_frame, background=GLASS_BACKGROUND)
            copy_text = f"{title}\n\n{text}" if title else text
            copy_button = tk.Button(
                actions,
                text="Copy",
                command=lambda: self.copy_message(copy_text),
                background=GLASS_BACKGROUND,
                foreground="#a9caff",
                activebackground=GLASS_CARD,
                activeforeground="#ffffff",
                relief="flat",
                borderwidth=0,
                font=("Segoe UI", 9),
                cursor="hand2",
                padx=8,
                pady=2,
            )
            copy_button.pack(side="left")
            if source_url is not None:
                source_button = tk.Button(
                    actions,
                    text="Source",
                    command=lambda: self.open_source(source_url),
                    background=GLASS_BACKGROUND,
                    foreground="#a9caff",
                    activebackground=GLASS_CARD,
                    activeforeground="#ffffff",
                    relief="flat",
                    borderwidth=0,
                    font=("Segoe UI", 9),
                    cursor="hand2",
                    padx=8,
                    pady=2,
                )
                source_button.pack(side="left")
            self.enable_mousewheel(actions)
            for child in actions.winfo_children():
                self.enable_mousewheel(child)
            actions.pack(fill="x", padx=4, pady=(0, 6))
        self.enable_mousewheel(message_frame)
        message_frame.pack(fill="x", pady=(0, 5 if thinking else 0))
        self.update_idletasks()
        self.canvas.configure(scrollregion=self.canvas.bbox("all"))
        self.canvas.yview_moveto(1.0)
        return message_frame

    def copy_message(self, text: str) -> None:
        try:
            self.clipboard_clear()
            self.clipboard_append(text)
        except tk.TclError as error:
            messagebox.showerror(
                "Kopieren fehlgeschlagen",
                f"Der Text konnte nicht kopiert werden: {error}",
                parent=self.winfo_toplevel(),
            )

    def open_source(self, source_url: str) -> None:
        if not source_url.startswith(("http://", "https://")):
            messagebox.showerror(
                "Quelle nicht verfügbar",
                "Die Quellen-URL ist ungültig.",
                parent=self.winfo_toplevel(),
            )
            return
        try:
            opened = webbrowser.open(source_url)
        except (webbrowser.Error, OSError) as error:
            messagebox.showerror(
                "Quelle konnte nicht geöffnet werden",
                f"Der Link konnte nicht im Browser geöffnet werden: {error}",
                parent=self.winfo_toplevel(),
            )
            return
        if not opened:
            messagebox.showerror(
                "Quelle konnte nicht geöffnet werden",
                "Der Link konnte nicht im Browser geöffnet werden.",
                parent=self.winfo_toplevel(),
            )


class RoundedEntryCanvas(tk.Canvas):
    def __init__(self, master: tk.Misc, **entry_options: object) -> None:
        super().__init__(
            master,
            height=48,
            background=GLASS_BACKGROUND,
            borderwidth=0,
            highlightthickness=0,
        )
        self.entry = tk.Entry(
            self,
            relief="flat",
            borderwidth=0,
            highlightthickness=0,
            **entry_options,
        )
        self.entry_window = self.create_window(
            15, 24, window=self.entry, anchor="w", height=26
        )
        self.bind("<Configure>", self.redraw)

    def redraw(self, event: tk.Event[tk.Misc]) -> None:
        self.delete("glass")
        self.create_polygon(
            RoundedBubble.rounded_points(event.width - 1, 47, 15),
            smooth=True,
            splinesteps=24,
            fill=GLASS_INPUT,
            outline=GLASS_BORDER,
            width=1,
            tags="glass",
        )
        self.tag_lower("glass")
        self.coords(self.entry_window, 15, 24)
        self.itemconfigure(self.entry_window, width=max(10, event.width - 30))


class RoundedSendButton(tk.Canvas):
    def __init__(self, master: tk.Misc, command: Callable[[], object]) -> None:
        super().__init__(
            master,
            width=46,
            height=46,
            background=GLASS_BACKGROUND,
            borderwidth=0,
            highlightthickness=0,
        )
        self.create_polygon(
            RoundedBubble.rounded_points(45, 45, 15),
            smooth=True,
            splinesteps=24,
            fill=GLASS_INPUT,
            outline="#ffffff",
            width=1,
        )
        self.create_line(
            23,
            32,
            23,
            14,
            fill="#ffffff",
            width=1.5,
            arrow="last",
            arrowshape=(7, 8, 3),
            capstyle=tk.ROUND,
            joinstyle=tk.ROUND,
        )
        self.configure(cursor="hand2")
        self.bind("<Button-1>", lambda _event: command())


class RoundedVoiceButton(tk.Canvas):
    def __init__(self, master: tk.Misc, command: Callable[[], object]) -> None:
        super().__init__(
            master,
            width=46,
            height=46,
            background=GLASS_BACKGROUND,
            borderwidth=0,
            highlightthickness=0,
            cursor="hand2",
        )
        self.create_polygon(
            RoundedBubble.rounded_points(45, 45, 15),
            smooth=True,
            splinesteps=24,
            fill=GLASS_INPUT,
            outline="#ffffff",
            width=1,
        )
        self.microphone_color = self.create_oval(
            18, 10, 28, 25, fill="#54d68b", outline="", tags="mic-indicator"
        )
        self.create_line(
            15, 20, 15, 23, 17, 28, 21, 31, 25, 31, 29, 28, 31, 23, 31, 20,
            fill="#54d68b",
            width=2,
            smooth=True,
            tags="mic-icon",
        )
        self.create_line(
            23, 31, 23, 35, fill="#54d68b", width=2, tags="mic-icon"
        )
        self.create_line(
            19, 35, 27, 35, fill="#54d68b", width=2, tags="mic-icon"
        )
        self.bind("<Button-1>", lambda _event: command())

    def set_enabled(self, enabled: bool) -> None:
        color = "#54d68b" if enabled else "#ff5c68"
        self.itemconfigure("mic-indicator", fill=color)
        self.itemconfigure("mic-icon", fill=color)


def launch_application(app_name: str) -> None:
    normalized_name = re.sub(r"\s+", " ", app_name.strip().casefold())
    if normalized_name == "google":
        chrome_executable = find_chrome_executable()
        if chrome_executable is not None:
            subprocess.Popen(
                [str(chrome_executable), "https://www.google.com"],
                close_fds=True,
            )
            return
        if webbrowser.open("https://www.google.com"):
            return
        raise FileNotFoundError(
            "Google konnte nicht geöffnet werden: Chrome und kein Standardbrowser gefunden."
        )

    if normalized_name in {"chrome", "google chrome"}:
        chrome_executable = find_chrome_executable()
        if chrome_executable is not None:
            subprocess.Popen([str(chrome_executable)], close_fds=True)
            return

    if normalized_name == "roblox":
        versions_dir = (
            Path(os.environ.get("LOCALAPPDATA", ""))
            / "Roblox"
            / "Versions"
        )
        player_paths = list(versions_dir.glob("version-*/RobloxPlayerBeta.exe"))
        if player_paths:
            player = max(player_paths, key=lambda path: path.stat().st_mtime)
            subprocess.Popen(
                [str(player)],
                cwd=str(player.parent),
                close_fds=True,
            )
            return

    executable = APP_ALIASES.get(normalized_name, app_name.strip())
    resolved_executable = shutil.which(executable)
    if resolved_executable:
        subprocess.Popen([resolved_executable], close_fds=True)
        return

    supplied_path = Path(app_name.strip()).expanduser()
    if supplied_path.is_file():
        if supplied_path.suffix.casefold() == ".exe":
            subprocess.Popen([str(supplied_path.resolve())], close_fds=True)
            return
        start_file = getattr(os, "startfile", None)
        if start_file is not None:
            start_file(str(supplied_path.resolve()))
            return

    start_menu_dirs = (
        Path(os.environ.get("APPDATA", ""))
        / "Microsoft"
        / "Windows"
        / "Start Menu"
        / "Programs",
        Path(os.environ.get("PROGRAMDATA", ""))
        / "Microsoft"
        / "Windows"
        / "Start Menu"
        / "Programs",
    )
    shortcut_names = {normalized_name}
    if normalized_name in {"chrome", "google chrome"}:
        shortcut_names.update({"chrome", "google chrome"})
    for start_menu_dir in start_menu_dirs:
        if not start_menu_dir.is_dir():
            continue
        for shortcut in start_menu_dir.rglob("*.lnk"):
            if shortcut.stem.casefold() not in shortcut_names:
                continue
            start_file = getattr(os, "startfile", None)
            if start_file is None:
                break
            start_file(str(shortcut))
            return

    raise FileNotFoundError(f"App wurde nicht gefunden: {app_name}")


def find_chrome_executable() -> Path | None:
    install_dirs = (
        os.environ.get("LOCALAPPDATA"),
        os.environ.get("PROGRAMFILES"),
        os.environ.get("PROGRAMFILES(X86)"),
    )
    for install_dir in install_dirs:
        if install_dir:
            executable = (
                Path(install_dir) / "Google" / "Chrome" / "Application" / "chrome.exe"
            )
            if executable.is_file():
                return executable
    return None


def apply_windows_glass(window: tk.Toplevel) -> None:
    try:
        hwnd = ctypes.c_void_p(window.winfo_id())
        backdrop_type = ctypes.c_int(2)
        corner_preference = ctypes.c_int(2)
        dwmapi = ctypes.windll.dwmapi
        dwmapi.DwmSetWindowAttribute(
            hwnd, 38, ctypes.byref(backdrop_type), ctypes.sizeof(backdrop_type)
        )
        dwmapi.DwmSetWindowAttribute(
            hwnd,
            33,
            ctypes.byref(corner_preference),
            ctypes.sizeof(corner_preference),
        )
    except (AttributeError, OSError):
        pass


class SearchResultsParser(HTMLParser):
    def __init__(self, engine: str) -> None:
        super().__init__(convert_charrefs=True)
        self.engine = engine
        self.results: list[SearchResult] = []
        self.current: dict[str, str] | None = None
        self.capture_title = False
        self.capture_snippet = False

    def handle_starttag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        attributes = dict(attrs)
        classes = set((attributes.get("class") or "").split())
        is_result = (
            (
                self.engine == "DuckDuckGo"
                and (
                    (tag == "div" and "result" in classes)
                    or (tag == "a" and bool(classes & {"result-link", "result__a"}))
                )
            )
            or (self.engine == "Bing" and tag == "li" and "b_algo" in classes)
            or (self.engine == "Yahoo" and tag == "div" and "algo" in classes)
            or (self.engine == "Google" and tag == "div" and "MjjYud" in classes)
            or (self.engine == "Brave" and tag == "div" and "snippet" in classes)
            or (self.engine == "Mojeek" and tag == "li" and "result" in classes)
            or (
                self.engine == "Startpage"
                and tag == "div"
                and bool(classes & {"w-gl__result", "result"})
            )
            or (self.engine == "Ecosia" and tag == "div" and "result" in classes)
            or (
                self.engine == "Qwant"
                and tag == "div"
                and bool(classes & {"webResult", "web-result"})
            )
        )
        if is_result:
            self._save_result()
            self.current = {"title": "", "url": "", "snippet": ""}

        if self.current is None:
            return

        if self.engine == "DuckDuckGo" and tag == "a" and classes & {"result-link", "result__a"}:
            self.current["url"] = attributes.get("href") or ""
            self.capture_title = True
        elif self.engine == "Bing" and tag == "h2":
            self.capture_title = True
        elif self.engine == "Yahoo" and tag == "h3":
            self.capture_title = True
        elif self.engine in ("Google", "Brave", "Mojeek", "Ecosia", "Qwant") and tag in (
            "h2",
            "h3",
        ):
            self.capture_title = True
        elif (
            self.engine == "Startpage"
            and tag == "a"
            and "w-gl__result-title" in classes
        ):
            self.capture_title = True
        elif tag == "a" and self.capture_title and not self.current["url"]:
            self.current["url"] = attributes.get("href") or ""
        if tag == "a" and not self.current["url"]:
            self.current["url"] = attributes.get("href") or ""

        if (
            self.engine == "DuckDuckGo"
            and tag in ("a", "div", "td")
            and bool(classes & {"result__snippet", "result-snippet"})
        ):
            self.capture_snippet = True
        elif (
            self.engine in ("Bing", "Yahoo", "Mojeek", "Ecosia", "Qwant")
            and tag == "p"
        ):
            self.capture_snippet = True
        elif self.engine == "Google" and tag == "div" and bool(
            classes & {"VwiC3b", "yXK7lf"}
        ):
            self.capture_snippet = True
        elif self.engine == "Brave" and tag in ("p", "div") and bool(
            classes & {"snippet-description", "snippet-content"}
        ):
            self.capture_snippet = True
        elif self.engine == "Startpage" and tag == "div" and bool(
            classes & {"w-gl__description", "w-gl__description--default"}
        ):
            self.capture_snippet = True
        elif self.engine == "Ecosia" and tag == "div" and bool(
            classes & {"result-snippet", "result__snippet"}
        ):
            self.capture_snippet = True

    def handle_endtag(self, tag: str) -> None:
        if self.capture_title and tag in ("a", "h2", "h3"):
            self.capture_title = False
        if self.capture_snippet and tag in ("a", "div", "p", "td"):
            self.capture_snippet = False

    def handle_data(self, data: str) -> None:
        if self.current is None:
            return
        if self.capture_title:
            self.current["title"] += data
        if self.capture_snippet:
            self.current["snippet"] += data

    def close(self) -> None:
        super().close()
        self._save_result()

    def _save_result(self) -> None:
        if self.current is None:
            return
        title = re.sub(r"\s+", " ", self.current["title"]).strip()
        url = self.current["url"].strip()
        snippet = re.sub(r"\s+", " ", self.current["snippet"]).strip()
        if url.startswith("//"):
            url = "https:" + url
        if self.engine == "DuckDuckGo":
            redirect = parse_qs(urlparse(url).query).get("uddg")
            if redirect:
                url = unquote(redirect[0])
        elif self.engine == "Bing":
            encoded_url = parse_qs(urlparse(url).query).get("u", [""])[0]
            if encoded_url.startswith("a1"):
                try:
                    decoded = base64.urlsafe_b64decode(encoded_url[2:] + "===")
                    decoded_url = decoded.decode("utf-8", errors="replace")
                    if decoded_url.startswith(("http://", "https://")):
                        url = decoded_url
                except (ValueError, UnicodeDecodeError):
                    pass
        if title and url.startswith(("http://", "https://")):
            self.results.append(SearchResult(title, url, snippet, self.engine))
        self.current = None


def search_engine(engine: str, url_template: str, query: str) -> list[SearchResult]:
    url = url_template.format(query=quote_plus(query))
    request = Request(url, headers={"User-Agent": USER_AGENT})
    with urlopen(request, timeout=SEARCH_REQUEST_TIMEOUT) as response:
        page = response.read().decode("utf-8", errors="replace")
    if engine.startswith("Wikipedia"):
        payload = json.loads(page)
        search_data = payload.get("query", {}).get("search")
        if not isinstance(search_data, list):
            raise ValueError("Wikipedia response did not contain search results")
        wiki_domain = (
            "de.wikipedia.org"
            if engine == "Wikipedia (Deutsch)"
            else "en.wikipedia.org"
        )
        return [
            SearchResult(
                title=item["title"],
                url=f"https://{wiki_domain}/?curid={item['pageid']}",
                snippet=html.unescape(re.sub(r"<[^>]+>", "", item.get("snippet", ""))),
                engine=engine,
            )
            for item in search_data
            if isinstance(item, dict)
            and isinstance(item.get("title"), str)
            and isinstance(item.get("pageid"), int)
        ]
    parser = SearchResultsParser(engine)
    parser.feed(page)
    parser.close()
    return parser.results


def search_web(query: str) -> tuple[list[SearchResult], list[str]]:
    queries = [query]
    successful_engines: set[str] = set()
    matches_by_query: dict[str, list[SearchResult]] = {
        search_query: [] for search_query in queries
    }
    with ThreadPoolExecutor(max_workers=len(SEARCH_ENGINES) * len(queries)) as executor:
        pending = {
            executor.submit(search_engine, engine, url_template, search_query): (
                engine,
                search_query,
            )
            for search_query in queries
            for engine, url_template in SEARCH_ENGINES.items()
        }
        try:
            for future in as_completed(pending, timeout=SEARCH_TOTAL_TIMEOUT):
                engine, search_query = pending[future]
                try:
                    engine_results = future.result()
                except (OSError, URLError, TimeoutError, HTTPException, ValueError):
                    continue
                match = best_matching_result(search_query, engine_results)
                if match is not None:
                    successful_engines.add(engine)
                    matches_by_query[search_query].append(match)
        except FuturesTimeoutError:
            for future in pending:
                future.cancel()

    best_match = next(
        (
            match
            for search_query in queries
            if (match := best_matching_result(search_query, matches_by_query[search_query]))
            is not None
        ),
        None,
    )
    failures = sorted(set(SEARCH_ENGINES) - successful_engines)
    return ([best_match] if best_match is not None else []), failures


SEARCH_STOP_WORDS = {
    "aber", "alle", "als", "am", "an", "auch", "auf", "aus", "bei", "bin",
    "bis", "bitte", "das", "dass", "dein", "deine", "dem", "den", "der",
    "des", "die", "dies", "diese", "einen", "einer", "eines", "ein", "eine",
    "er", "es", "für", "gibt", "hat", "ich", "im", "in", "ist", "kann",
    "kannst", "mit", "nach", "oder", "sie", "sind", "und", "von", "was",
    "welche", "wer", "wie", "wird", "wir", "zu", "the", "and", "are",
    "for", "from", "how", "is", "it", "of", "on", "or", "that", "the",
    "to", "was", "what", "when", "where", "which", "who", "why", "with",
}


def search_terms(text: str) -> set[str]:
    words = re.findall(r"[^\W_]+", text.casefold())
    terms: set[str] = set()
    for word in words:
        if len(word) <= 2 or word in SEARCH_STOP_WORDS:
            continue
        if word.endswith("ies") and len(word) > 5:
            word = word[:-3] + "y"
        elif word.endswith("s") and len(word) > 4:
            word = word[:-1]
        terms.add(word)
    return terms


def best_matching_result(
    query: str, results: list[SearchResult]
) -> SearchResult | None:
    terms = search_terms(query)
    if not terms:
        return results[0] if results else None

    ranked: list[tuple[float, SearchResult]] = []
    for result in results:
        title_terms = search_terms(result.title)
        snippet_terms = search_terms(result.snippet)
        matched = terms & (title_terms | snippet_terms)
        title_matched = terms & title_terms
        snippet_matched = terms & snippet_terms
        snippet_coverage = len(snippet_matched) / len(terms)
        title_coverage = len(title_matched) / len(terms)
        score = snippet_coverage * 2 + title_coverage
        if len(terms) >= 2 and len(matched) < 2:
            continue
        if score >= 0.7:
            ranked.append((score, result))

    if not ranked:
        return None
    return max(ranked, key=lambda item: item[0])[1]


class QuickAssistant:
    def __init__(self, root: tk.Tk) -> None:
        self.root = root
        self.events: queue.Queue[tuple[str, object]] = queue.Queue()
        self.chat_window: tk.Toplevel | None = None
        self.chat_body: RoundedMessageLog | None = None
        self.chat_entry: tk.Entry | None = None
        self.chat_history: list[tuple[str, str, str, str | None]] = []
        self.chat_visible = False
        self.chat_animating = False
        self.chat_height = 520
        self.chat_query_id = 0
        self.thinking_marks: dict[int, tk.Widget] = {}
        self.pending_chat_queries: set[int] = set()
        self.f7_was_down = False
        self.voice_enabled = False
        self.voice_preference = True
        self.voice_session_id = 0
        self.voice_stop_event: threading.Event | None = None
        self.voice_thread: threading.Thread | None = None
        self.voice_silence_job: str | None = None
        self.voice_button: RoundedVoiceButton | None = None

        root.withdraw()
        root.protocol("WM_DELETE_WINDOW", self.close)

        self.root.after(60, self.poll_f7)
        self.root.after(100, self.poll_events)

    def poll_events(self) -> None:
        while True:
            try:
                event, value = self.events.get_nowait()
            except queue.Empty:
                break

            if event == "CHAT_SEARCH_DONE":
                query_id, results = cast(
                    tuple[int, list[SearchResult]], value
                )
                if query_id in self.pending_chat_queries:
                    self.pending_chat_queries.remove(query_id)
                    self.remove_thinking(query_id)
                    self.show_chat_results(results)
            elif event == "CHAT_SEARCH_ERROR":
                query_id, _error = cast(tuple[int, object], value)
                if query_id in self.pending_chat_queries:
                    self.pending_chat_queries.remove(query_id)
                    self.remove_thinking(query_id)
                    self.append_bubble(
                        "Es konnte keine Antwort geladen werden. Bitte versuche es erneut.\n\n",
                        "error",
                    )
            elif event == "VOICE_TEXT":
                session_id, phrase = cast(tuple[int, str], value)
                self.handle_voice_text(session_id, phrase)
            elif event == "VOICE_ERROR":
                session_id, error = cast(tuple[int, str], value)
                if (
                    self.voice_enabled
                    and session_id == self.voice_session_id
                    and self.chat_visible
                ):
                    self.stop_voice_input()
                    self.append_bubble(
                        f"Lokale Spracherkennung nicht verfügbar: {error}",
                        "error",
                    )
        self.root.after(100, self.poll_events)

    def run_search(self, query: str, event_name: str, query_id: int = 0) -> None:
        try:
            results = search_web(query)[0]
        except (OSError, URLError, TimeoutError, HTTPException, ValueError) as error:
            self.events.put(("CHAT_SEARCH_ERROR", (query_id, error)))
            return
        self.events.put((event_name, (query_id, results)))

    def poll_f7(self) -> None:
        try:
            is_down = bool(ctypes.windll.user32.GetAsyncKeyState(0x76) & 0x8000)
        except (AttributeError, OSError):
            is_down = False
        if is_down and not self.f7_was_down:
            self.toggle_chat()
        self.f7_was_down = is_down
        self.root.after(60, self.poll_f7)

    def toggle_chat(self) -> None:
        if self.chat_animating:
            return
        if self.chat_visible:
            self.hide_chat()
        else:
            self.show_chat()

    def show_chat(self) -> None:
        self.chat_visible = True
        self.chat_animating = True

        panel = tk.Toplevel(self.root)
        self.chat_window = panel
        panel.overrideredirect(True)
        panel.attributes("-topmost", True)
        panel.attributes("-alpha", WINDOW_OPACITY)
        panel.configure(bg=GLASS_BACKGROUND)
        panel.title("Quick Assistent")
        panel.bind("<Escape>", lambda _event: self.hide_chat())

        screen_width = panel.winfo_screenwidth()
        panel_width = min(820, screen_width - 32)
        self.chat_height = min(560, panel.winfo_screenheight() - 72)
        self.chat_x = (screen_width - panel_width) // 2
        self.chat_y = 12
        panel.geometry(f"{panel_width}x{self.chat_height}+{self.chat_x}+{-self.chat_height}")
        panel.update_idletasks()
        apply_windows_glass(panel)

        shell = tk.Frame(
            panel,
            bg=GLASS_BACKGROUND,
            highlightbackground="#ffffff",
            highlightthickness=1,
        )
        shell.pack(fill="both", expand=True)
        header = tk.Frame(shell, bg=GLASS_BACKGROUND, height=52)
        header.pack(fill="x")
        header.pack_propagate(False)
        tk.Label(
            header,
            text="Quick Assistent",
            bg=GLASS_BACKGROUND,
            fg="#ffffff",
            font=("Segoe UI Semibold", 14),
        ).pack(side="left", padx=20)
        close_button = tk.Button(
            header,
            text="×",
            command=self.hide_chat,
            bg=GLASS_BACKGROUND,
            fg="#ffffff",
            activebackground=GLASS_CARD,
            activeforeground="#ffffff",
            relief="flat",
            font=("Segoe UI", 19),
            cursor="hand2",
        )
        close_button.pack(side="right", padx=12)
        exit_button = tk.Button(
            header,
            text="Exit",
            command=self.confirm_exit,
            bg=GLASS_BACKGROUND,
            fg="#ffffff",
            activebackground=GLASS_CARD,
            activeforeground="#ffffff",
            relief="flat",
            font=("Segoe UI", 10),
            cursor="hand2",
        )
        exit_button.pack(side="right", padx=(0, 8))
        tk.Frame(shell, bg="#ffffff", height=1).pack(fill="x", padx=18)

        input_frame = tk.Frame(shell, bg=GLASS_BACKGROUND)
        input_frame.pack(side="bottom", fill="x", padx=18, pady=(4, 16))
        self.voice_button = RoundedVoiceButton(input_frame, self.toggle_voice_input)
        self.voice_button.pack(side="right", padx=(10, 0))
        self.voice_button.set_enabled(self.voice_preference)
        send_frame = RoundedSendButton(input_frame, self.submit_chat_query)
        send_frame.pack(side="right")
        entry_frame = RoundedEntryCanvas(
            input_frame,
            font=("Segoe UI", 11),
            bg=GLASS_INPUT,
            fg="#ffffff",
            insertbackground="#ffffff",
            selectbackground="#555555",
        )
        entry_frame.pack(side="left", fill="x", expand=True, padx=(0, 10))
        self.chat_entry = entry_frame.entry
        self.chat_entry.bind("<Return>", self.submit_chat_query)

        body_frame = tk.Frame(shell, bg=GLASS_BACKGROUND)
        body_frame.pack(side="top", fill="both", expand=True, padx=18, pady=(8, 8))
        self.chat_body = RoundedMessageLog(body_frame)
        self.chat_body.pack(fill="both", expand=True)

        for speaker, text, title, source_url in self.chat_history:
            self.chat_body.add_message(
                speaker,
                text,
                title=title,
                source_url=source_url,
            )
        if not self.chat_history:
            self.append_bubble(GREETING, "assistant")
        for query_id in self.pending_chat_queries:
            self.thinking_marks[query_id] = self.chat_body.add_message(
                "Assistent",
                "Denkt...",
                thinking=True,
            )
        self.chat_entry.focus_set()
        if self.voice_preference:
            self.start_voice_input()
        self.animate_chat(0, True)

    def hide_chat(self) -> None:
        if not self.chat_visible or self.chat_animating:
            return
        self.stop_voice_input(remember=False)
        self.chat_animating = True
        self.chat_query_id += 1
        self.thinking_marks.clear()
        self.animate_chat(0, False)

    def animate_chat(self, frame: int, opening: bool) -> None:
        panel = self.chat_window
        if panel is None or not panel.winfo_exists():
            self.finish_chat_animation(opening)
            return
        frames = 16
        progress = min((frame + 1) / frames, 1.0)
        easing = 1 - (1 - progress) ** 3 if opening else progress**3
        if opening:
            y = round(-self.chat_height + easing * (self.chat_height + self.chat_y))
        else:
            y = round(self.chat_y - easing * (self.chat_height + self.chat_y))
        panel.geometry(f"+{self.chat_x}+{y}")
        if frame + 1 < frames:
            panel.after(12, self.animate_chat, frame + 1, opening)
        else:
            self.finish_chat_animation(opening)

    def finish_chat_animation(self, opening: bool) -> None:
        self.chat_animating = False
        if opening:
            if self.chat_window is not None:
                self.chat_window.lift()
                self.chat_window.focus_force()
            if self.chat_entry is not None:
                self.chat_entry.focus_force()
            return
        if self.chat_window is not None:
            self.chat_window.destroy()
        self.chat_window = None
        self.chat_body = None
        self.chat_entry = None
        self.voice_button = None
        self.chat_visible = False

    def update_voice_button(self) -> None:
        button = self.voice_button
        if button is None or not button.winfo_exists():
            return
        enabled = self.voice_enabled
        button.set_enabled(enabled)

    def start_voice_input(self) -> None:
        if self.voice_enabled:
            return
        self.voice_preference = True
        self.voice_session_id += 1
        session_id = self.voice_session_id
        stop_event = threading.Event()
        self.voice_stop_event = stop_event
        self.voice_enabled = True
        self.update_voice_button()
        self.voice_thread = threading.Thread(
            target=self.run_google_speech_recognition,
            args=(session_id, stop_event),
            daemon=True,
        )
        self.voice_thread.start()

    def stop_voice_input(self, *, remember: bool = True) -> None:
        if remember:
            self.voice_preference = False
        self.voice_enabled = False
        self.voice_session_id += 1
        if self.voice_stop_event is not None:
            self.voice_stop_event.set()
            self.voice_stop_event = None
        if self.voice_silence_job is not None:
            self.root.after_cancel(self.voice_silence_job)
            self.voice_silence_job = None
        self.update_voice_button()

    def toggle_voice_input(self) -> None:
        if self.voice_preference:
            self.stop_voice_input()
        else:
            self.start_voice_input()

    def confirm_exit(self) -> None:
        if messagebox.askyesno(
            "Exit",
            "Are you sure you want to Close Quick Assistent",
            parent=self.chat_window,
        ):
            self.close()

    def run_google_speech_recognition(
        self, session_id: int, stop_event: threading.Event
    ) -> None:
        try:
            import speech_recognition as sr

            recognizer = sr.Recognizer()
            recognizer.pause_threshold = 1.0
            recognizer.non_speaking_duration = 0.5
            recognizer.dynamic_energy_threshold = True
            with sr.Microphone() as microphone:
                recognizer.adjust_for_ambient_noise(microphone, duration=0.4)
                while not stop_event.is_set():
                    try:
                        audio = recognizer.listen(
                            microphone,
                            timeout=1,
                            phrase_time_limit=10,
                        )
                    except sr.WaitTimeoutError:
                        continue
                    if stop_event.is_set():
                        break
                    try:
                        phrase = recognizer.recognize_google(
                            audio, language="de-DE"
                        )
                    except sr.UnknownValueError:
                        continue
                    except sr.RequestError as error:
                        self.events.put(
                            ("VOICE_ERROR", (session_id, str(error)))
                        )
                        return
                    if phrase.strip():
                        self.events.put(("VOICE_TEXT", (session_id, phrase)))
        except Exception as error:
            self.events.put(("VOICE_ERROR", (session_id, str(error))))

    def handle_voice_text(self, session_id: int, phrase: str) -> None:
        entry = self.chat_entry
        if (
            not self.chat_visible
            or not self.voice_enabled
            or session_id != self.voice_session_id
            or entry is None
            or not phrase.strip()
        ):
            return
        existing_text = entry.get()
        separator = " " if existing_text and not existing_text.endswith(" ") else ""
        entry.insert("end", f"{separator}{phrase.strip()}")
        if self.voice_silence_job is not None:
            self.root.after_cancel(self.voice_silence_job)
        self.voice_silence_job = self.root.after(
            1000, self.submit_voice_query, session_id
        )

    def submit_voice_query(self, session_id: int) -> None:
        self.voice_silence_job = None
        if self.voice_enabled and session_id == self.voice_session_id:
            self.submit_chat_query()

    def append_bubble(self, text: str, tag: str) -> None:
        speaker = "User" if tag == "user" else "Assistent"
        message_text = text.rstrip()
        self.chat_history.append((speaker, message_text, "", None))
        body = self.chat_body
        if body is None:
            return
        if tag == "thinking":
            body.add_message("Assistent", message_text, thinking=True)
        else:
            body.add_message(speaker, message_text)

    def finish_application_launch(self, query_id: int, app_name: str) -> None:
        if query_id not in self.pending_chat_queries:
            return
        self.pending_chat_queries.remove(query_id)
        self.remove_thinking(query_id)
        try:
            launch_application(app_name)
        except (FileNotFoundError, OSError) as error:
            self.append_bubble(
                f"Ich konnte {app_name} nicht öffnen: {error}",
                "error",
            )
        else:
            self.append_bubble(
                f"Okay, ich öffne {app_name}.",
                "assistant",
            )

    def handle_local_command(self, query: str) -> bool:
        original_command = re.sub(r"[.!?]+$", "", query.strip())
        command = original_command.casefold()
        command = re.sub(r"^(?:bitte)\s+", "", command)
        if re.fullmatch(
            r"(?:öffne|oeffne|open)\s+(?:die\s+)?letzte\s+frage"
            r"(?:\s+im\s+browser)?",
            command,
        ):
            return False
        open_app = re.fullmatch(
            r"(?:öffne|oeffne|open|starte|launch)\s+(?:bitte\s+)?(.+)",
            command,
        )
        if open_app is None:
            return False

        display_match = re.fullmatch(
            r"(?:öffne|oeffne|open|starte|launch)\s+(?:bitte\s+)?(.+)",
            original_command,
            flags=re.IGNORECASE,
        )
        display_name = display_match.group(1).strip() if display_match else open_app.group(1).strip()
        display_name = re.sub(
            r"^(?:(?:die\s+)?app\s+|die\s+)",
            "",
            display_name,
            flags=re.IGNORECASE,
        )
        app_name = display_name.casefold()
        if app_name in {"app", "anwendung", "programm"}:
            self.append_bubble("Welche App soll ich öffnen?", "assistant")
            return True
        self.chat_query_id += 1
        query_id = self.chat_query_id
        if self.chat_body is None:
            return True
        self.thinking_marks[query_id] = self.chat_body.add_message(
            "Assistent",
            "Denkt...",
            thinking=True,
        )
        self.pending_chat_queries.add(query_id)
        self.root.after(2000, self.finish_application_launch, query_id, display_name)
        return True

    def submit_chat_query(self, _event: tk.Event[tk.Misc] | None = None) -> str:
        entry = self.chat_entry
        if entry is None:
            return "break"
        query = entry.get().strip()
        if not query:
            return "break"
        entry.delete(0, "end")
        self.append_bubble(query, "user")
        if self.handle_local_command(query):
            return "break"
        self.chat_query_id += 1
        query_id = self.chat_query_id
        if self.chat_body is None:
            return "break"
        self.thinking_marks[query_id] = self.chat_body.add_message(
            "Assistent",
            "Denkt...",
            thinking=True,
        )
        self.pending_chat_queries.add(query_id)
        threading.Thread(
            target=self.run_search,
            args=(query, "CHAT_SEARCH_DONE", query_id),
            daemon=True,
        ).start()
        return "break"

    def remove_thinking(self, query_id: int) -> None:
        marks = self.thinking_marks.pop(query_id, None)
        if marks is not None and marks.winfo_exists():
            marks.destroy()

    def show_chat_results(self, results: list[SearchResult]) -> None:
        if not results:
            self.append_bubble(
                "Ich konnte keinen Treffer finden.",
                "error",
            )
            return

        result = results[0]
        description = result.snippet.strip() or "Für diese Seite wurde keine Beschreibung gefunden."
        self.append_answer_box(result.title.strip(), description, result.url)

    def append_answer_box(
        self, title: str, description: str, source_url: str
    ) -> None:
        self.chat_history.append(("Assistent", description, title, source_url))
        body = self.chat_body
        if body is None:
            return
        body.add_message(
            "Assistent",
            description,
            title=title,
            source_url=source_url,
        )

    def close(self) -> None:
        self.stop_voice_input(remember=False)
        if self.chat_window is not None:
            self.chat_window.destroy()
        self.root.destroy()


def main() -> None:
    if os.name != "nt":
        raise SystemExit("Der globale F7-Hotkey benötigt Windows.")
    root = tk.Tk()
    QuickAssistant(root)
    root.mainloop()


if __name__ == "__main__":
    main()
