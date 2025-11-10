#!/usr/bin/env python3
"""Interactive macro editor and recorder with drag, wait, and block support."""
from __future__ import annotations

import json
import threading
import time
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Tuple

import tkinter as tk
from tkinter import filedialog, messagebox, ttk

from pynput import keyboard, mouse
import pyautogui as pag

try:
    import pytesseract
except ImportError:  # pragma: no cover - optional dependency
    pytesseract = None

try:
    import pyperclip
except ImportError:  # pragma: no cover - optional dependency
    pyperclip = None


MIN_DELAY = 0.01  # 10ms base delay


@dataclass
class DragPathPoint:
    x: int
    y: int
    dt: float


@dataclass
class MacroEvent:
    type: str
    event: str
    dt: float = MIN_DELAY
    x: int = 0
    y: int = 0
    button: str = "Button.left"
    pressed: Optional[bool] = None
    dx: int = 0
    dy: int = 0
    key: str = ""
    rgb: Optional[Tuple[int, int, int]] = None
    tolerance: int = 10
    count: int = 1
    op: str = "=="
    value: int = 0
    mode: str = "contains"
    text: str = ""
    lang: str = "eng"
    x2: int = 0
    y2: int = 0
    interval: float = 0.05
    block: str = ""
    path: List[DragPathPoint] = field(default_factory=list)
    release_dt: float = 0.0

    def ensure_min_delay(self) -> None:
        if self.dt < MIN_DELAY:
            self.dt = MIN_DELAY


class MacroRecorder:
    """Record and replay mouse/keyboard macros."""

    def __init__(self) -> None:
        self.events: List[MacroEvent] = []
        self.recording = False
        self.record_moves = True
        self.merge_threshold = 0.15
        self.last_time: Optional[float] = None
        self.stop_request = False

        self.mouse_listener: Optional[mouse.Listener] = None
        self.keyboard_listener: Optional[keyboard.Listener] = None
        self.emergency_listener: Optional[keyboard.Listener] = None

        self.mouse_controller = mouse.Controller()
        self.keyboard_controller = keyboard.Controller()

        self.pending_mouse_press: Optional[Dict[str, object]] = None
        self.drag_active = False

        self.pending_key_press: Dict[str, float] = {}
        self.mod_keys: set[str] = set()
        self.main_keys: set[str] = set()

    # ------------------------------------------------------------------ utils
    def _dt_from_last(self, now: float) -> float:
        if self.last_time is None:
            dt = MIN_DELAY
        else:
            dt = max(now - self.last_time, MIN_DELAY)
        self.last_time = now
        return dt

    @staticmethod
    def _normalize_key(key: keyboard.KeyCode | keyboard.Key) -> Optional[str]:
        try:
            if hasattr(key, "char") and key.char:
                ch = key.char
                code = ord(ch)
                if 32 <= code < 127:
                    return ch
                if 1 <= code <= 26:
                    return chr(ord("a") + code - 1)
        except Exception:
            pass

        text = str(key)
        if text.startswith("Key."):
            text = text[4:]

        mapping = {
            "ctrl_l": "Ctrl",
            "ctrl_r": "Ctrl",
            "ctrl": "Ctrl",
            "shift_l": "Shift",
            "shift_r": "Shift",
            "shift": "Shift",
            "alt_l": "Alt",
            "alt_r": "Alt",
            "alt": "Alt",
            "cmd": "Win",
            "cmd_l": "Win",
            "cmd_r": "Win",
            "windows": "Win",
            "space": "Space",
            "enter": "Enter",
            "return": "Enter",
            "escape": "Esc",
            "esc": "Esc",
            "tab": "Tab",
            "backspace": "Backspace",
            "delete": "Delete",
            "up": "Up",
            "down": "Down",
            "left": "Left",
            "right": "Right",
        }

        lower = text.lower()
        if lower in mapping:
            return mapping[lower]
        if lower.startswith("f") and lower[1:].isdigit():
            return text.upper()
        if text:
            return text.capitalize()
        return None

    # -------------------------------------------------------------- recording
    def start_record(self, record_moves: bool = True, merge_threshold_sec: float = 0.15) -> None:
        if self.recording:
            return
        self.events = []
        self.recording = True
        self.record_moves = record_moves
        self.merge_threshold = merge_threshold_sec
        self.last_time = time.time()
        self.pending_mouse_press = None
        self.pending_key_press.clear()
        self.mod_keys.clear()
        self.main_keys.clear()
        self.stop_request = False
        self.drag_active = False

        self.mouse_listener = mouse.Listener(
            on_move=self._on_move,
            on_click=self._on_click,
            on_scroll=self._on_scroll,
        )
        self.keyboard_listener = keyboard.Listener(
            on_press=self._on_press,
            on_release=self._on_release,
        )
        self.mouse_listener.start()
        self.keyboard_listener.start()
        self._start_emergency_listener()

    def stop_record(self) -> None:
        if not self.recording:
            return
        self.recording = False
        if self.mouse_listener:
            self.mouse_listener.stop()
            self.mouse_listener = None
        if self.keyboard_listener:
            self.keyboard_listener.stop()
            self.keyboard_listener = None
        self._stop_emergency_listener()
        self.pending_mouse_press = None
        self.pending_key_press.clear()
        self.mod_keys.clear()
        self.main_keys.clear()

    # ------------------------------ mouse callbacks + drag detection helpers
    def _start_drag(self, now: float, btn: str, x: int, y: int) -> None:
        self.drag_active = True
        self.pending_mouse_press = {
            "time": now,
            "button": btn,
            "x": x,
            "y": y,
            "dt": max(now - (self.last_time or now), MIN_DELAY),
            "moves": [],
            "last": now,
        }

    def _finish_drag(self, now: float, x: int, y: int) -> None:
        assert self.pending_mouse_press is not None
        info = self.pending_mouse_press
        path = [DragPathPoint(pt[0], pt[1], pt[2]) for pt in info["moves"]]
        release_dt = max(now - info.get("last", now), MIN_DELAY)
        ev = MacroEvent(
            type="mouse",
            event="drag",
            dt=float(info["dt"]),
            x=int(info["x"]),
            y=int(info["y"]),
            button=str(info["button"]),
            path=path,
            release_dt=release_dt,
        )
        if not ev.path and (ev.x, ev.y) == (x, y):
            # degrade to click if no movement
            click = MacroEvent(
                type="mouse",
                event="click_combined",
                dt=ev.dt,
                x=ev.x,
                y=ev.y,
                button=ev.button,
            )
            self.events.append(click)
            self.last_time = now
        else:
            if not ev.path:
                # ensure at least final position
                ev.path.append(DragPathPoint(int(x), int(y), MIN_DELAY))
            self.events.append(ev)
            self.last_time = now
        self.pending_mouse_press = None
        self.drag_active = False

    def _on_move(self, x: float, y: float) -> None:
        if not self.recording:
            return
        if self.drag_active and self.pending_mouse_press:
            now = time.time()
            last = self.pending_mouse_press["last"]
            dt = max(now - last, MIN_DELAY)
            self.pending_mouse_press["moves"].append((int(x), int(y), dt))
            self.pending_mouse_press["last"] = now
            return
        if not self.record_moves:
            return
        now = time.time()
        dt = self._dt_from_last(now)
        ev = MacroEvent(type="mouse", event="move", dt=dt, x=int(x), y=int(y))
        self.events.append(ev)

    def _on_click(self, x: float, y: float, button: mouse.Button, pressed: bool) -> None:
        if not self.recording:
            return
        now = time.time()
        btn_str = str(button)
        if pressed:
            self._start_drag(now, btn_str, int(x), int(y))
        else:
            if self.drag_active and self.pending_mouse_press and self.pending_mouse_press["button"] == btn_str:
                hold = now - float(self.pending_mouse_press["time"])
                if hold <= self.merge_threshold and not self.pending_mouse_press["moves"]:
                    dt = self._dt_from_last(now)
                    ev = MacroEvent(
                        type="mouse",
                        event="click_combined",
                        dt=dt,
                        x=int(x),
                        y=int(y),
                        button=btn_str,
                    )
                    self.events.append(ev)
                else:
                    self._finish_drag(now, int(x), int(y))
            else:
                dt = self._dt_from_last(now)
                ev = MacroEvent(
                    type="mouse",
                    event="click",
                    dt=dt,
                    x=int(x),
                    y=int(y),
                    button=btn_str,
                    pressed=False,
                )
                self.events.append(ev)
            self.pending_mouse_press = None
            self.drag_active = False

    def _on_scroll(self, x: float, y: float, dx: float, dy: float) -> None:
        if not self.recording:
            return
        now = time.time()
        dt = self._dt_from_last(now)
        ev = MacroEvent(
            type="mouse",
            event="scroll",
            dt=dt,
            x=int(x),
            y=int(y),
            dx=int(dx),
            dy=int(dy),
        )
        self.events.append(ev)

    # --------------------------------------------------------------- keyboard
    def _on_press(self, key: keyboard.KeyCode | keyboard.Key) -> None:
        if not self.recording or self.stop_request:
            return
        key_str = self._normalize_key(key)
        if not key_str:
            return
        now = time.time()
        self.pending_key_press[key_str] = now
        if key_str in {"Ctrl", "Shift", "Alt", "Win"}:
            self.mod_keys.add(key_str)
        else:
            self.main_keys.add(key_str)

    def _on_release(self, key: keyboard.KeyCode | keyboard.Key) -> None:
        if not self.recording or self.stop_request:
            return
        key_str = self._normalize_key(key)
        if not key_str:
            return
        now = time.time()
        press_time = self.pending_key_press.pop(key_str, None)
        self.main_keys.discard(key_str)
        if key_str in {"Ctrl", "Shift", "Alt", "Win"}:
            self.mod_keys.discard(key_str)
            return
        if press_time is None:
            return
        hold = now - press_time
        if key_str == "F12" and {"Ctrl", "Alt"}.issubset(self.mod_keys):
            return
        if self.mod_keys:
            combo = "+".join(sorted(self.mod_keys) + [key_str])
            dt = self._dt_from_last(now)
            ev = MacroEvent(type="keyboard", event="stroke", dt=dt, key=combo)
            self.events.append(ev)
        elif hold <= self.merge_threshold:
            dt = self._dt_from_last(now)
            ev = MacroEvent(type="keyboard", event="stroke", dt=dt, key=key_str)
            self.events.append(ev)
        else:
            dt_down = max(press_time - (self.last_time or press_time), MIN_DELAY)
            ev_down = MacroEvent(type="keyboard", event="down", dt=dt_down, key=key_str)
            dt_up = max(now - press_time, MIN_DELAY)
            ev_up = MacroEvent(type="keyboard", event="up", dt=dt_up, key=key_str)
            self.events.extend([ev_down, ev_up])
            self.last_time = now

    # --------------------------------------------------------- emergency stop
    def _start_emergency_listener(self) -> None:
        def on_press(key: keyboard.KeyCode | keyboard.Key) -> None:
            try:
                ks = self._normalize_key(key)
            except Exception:
                ks = None
            if not ks:
                return
            if ks == "F12" and self.mod_keys.issuperset({"Ctrl", "Alt"}):
                self.stop_request = True
                self.stop_record()

        self.emergency_listener = keyboard.Listener(on_press=on_press)
        self.emergency_listener.start()

    def _stop_emergency_listener(self) -> None:
        if self.emergency_listener:
            self.emergency_listener.stop()
            self.emergency_listener = None

    # ---------------------------------------------------------------- playback
    def _button_from_str(self, btn: str) -> mouse.Button:
        if "right" in btn:
            return mouse.Button.right
        if "middle" in btn:
            return mouse.Button.middle
        return mouse.Button.left

    def _press_combo(self, combo: str) -> None:
        parts = [part.strip() for part in combo.split("+") if part.strip()]
        mods: List[object] = []
        mains: List[object] = []
        for part in parts:
            lower = part.lower()
            key_obj: object
            if lower == "ctrl":
                key_obj = keyboard.Key.ctrl
            elif lower == "shift":
                key_obj = keyboard.Key.shift
            elif lower == "alt":
                key_obj = keyboard.Key.alt
            elif lower in {"win", "cmd"}:
                key_obj = keyboard.Key.cmd
            elif len(part) == 1:
                key_obj = part
            elif lower.startswith("f") and lower[1:].isdigit():
                key_obj = getattr(keyboard.Key, lower, part)
            else:
                key_obj = part
            if lower in {"ctrl", "shift", "alt", "win", "cmd"}:
                mods.append(key_obj)
            else:
                mains.append(key_obj)
        for key_obj in mods:
            self.keyboard_controller.press(key_obj)
        for key_obj in mains:
            self.keyboard_controller.press(key_obj)
        for key_obj in reversed(mains):
            self.keyboard_controller.release(key_obj)
        for key_obj in reversed(mods):
            self.keyboard_controller.release(key_obj)

    def _play_mouse(self, ev: MacroEvent) -> None:
        current_x, current_y = self.mouse_controller.position
        target_x = ev.x or current_x
        target_y = ev.y or current_y
        if ev.event == "move":
            self.mouse_controller.position = (target_x, target_y)
        elif ev.event == "move_rel":
            self.mouse_controller.position = (current_x + ev.x, current_y + ev.y)
        elif ev.event == "scroll":
            self.mouse_controller.position = (target_x, target_y)
            self.mouse_controller.scroll(ev.dx, ev.dy)
        elif ev.event == "click":
            btn = self._button_from_str(ev.button)
            self.mouse_controller.position = (target_x, target_y)
            if ev.pressed:
                self.mouse_controller.press(btn)
            else:
                self.mouse_controller.release(btn)
        elif ev.event == "click_combined":
            btn = self._button_from_str(ev.button)
            self.mouse_controller.position = (target_x, target_y)
            self.mouse_controller.press(btn)
            self.mouse_controller.release(btn)
        elif ev.event == "drag":
            btn = self._button_from_str(ev.button)
            self.mouse_controller.position = (target_x, target_y)
            self.mouse_controller.press(btn)
            last_time = 0.0
            for point in ev.path:
                time.sleep(max(point.dt, MIN_DELAY))
                self.mouse_controller.position = (point.x or target_x, point.y or target_y)
                last_time = point.dt
            if ev.release_dt > 0:
                time.sleep(max(ev.release_dt, MIN_DELAY))
            self.mouse_controller.release(btn)

    def _play_keyboard(self, ev: MacroEvent) -> None:
        if ev.event == "stroke":
            self._press_combo(ev.key)
        else:
            key_obj: object
            lower = ev.key.lower()
            if lower == "ctrl":
                key_obj = keyboard.Key.ctrl
            elif lower == "shift":
                key_obj = keyboard.Key.shift
            elif lower == "alt":
                key_obj = keyboard.Key.alt
            elif lower in {"win", "cmd"}:
                key_obj = keyboard.Key.cmd
            elif len(ev.key) == 1:
                key_obj = ev.key
            elif lower.startswith("f") and lower[1:].isdigit():
                key_obj = getattr(keyboard.Key, lower)
            else:
                return
            if ev.event == "down":
                self.keyboard_controller.press(key_obj)
            elif ev.event == "up":
                self.keyboard_controller.release(key_obj)

    def _eval_count(self, cur: int, op: str, value: int) -> bool:
        if op == "<":
            return cur < value
        if op == "<=":
            return cur <= value
        if op == "==":
            return cur == value
        if op == ">":
            return cur > value
        if op == ">=":
            return cur >= value
        return False

    def _eval_clip(self, pattern: str, mode: str) -> bool:
        if pyperclip is None:
            return False
        clip = pyperclip.paste() or ""
        text = pattern or ""
        mode_lower = (mode or "contains").lower()
        if mode_lower == "equals":
            return clip == text
        if mode_lower == "not":
            return text not in clip
        if mode_lower == "startswith":
            return clip.startswith(text)
        if mode_lower == "endswith":
            return clip.endswith(text)
        if mode_lower == "regex":
            import re

            return bool(re.search(text, clip))
        return text in clip

    def _build_loop_maps(self) -> Tuple[Dict[int, int], Dict[int, int]]:
        start_to_end: Dict[int, int] = {}
        end_to_start: Dict[int, int] = {}
        stack: List[int] = []
        for idx, ev in enumerate(self.events):
            if ev.type == "control" and ev.event == "loop_start":
                stack.append(idx)
            elif ev.type == "control" and ev.event == "loop_end" and stack:
                start = stack.pop()
                start_to_end[start] = idx
                end_to_start[idx] = start
        return start_to_end, end_to_start

    def _build_if_maps(
        self,
    ) -> Tuple[Dict[int, int], Dict[int, int], Dict[int, int], Dict[int, int]]:
        if_to_end: Dict[int, int] = {}
        if_to_else: Dict[int, int] = {}
        else_to_end: Dict[int, int] = {}
        else_to_if: Dict[int, int] = {}
        stack: List[Tuple[int, Optional[int]]] = []
        for idx, ev in enumerate(self.events):
            if ev.type == "control" and ev.event in {"if_color", "if_count", "if_clip"}:
                stack.append((idx, None))
            elif ev.type == "control" and ev.event == "else" and stack:
                start, _ = stack[-1]
                if_to_else[start] = idx
                stack[-1] = (start, idx)
                else_to_if[idx] = start
            elif ev.type == "control" and ev.event == "if_end" and stack:
                start, else_idx = stack.pop()
                if_to_end[start] = idx
                if else_idx is not None:
                    else_to_end[else_idx] = idx
        return if_to_end, if_to_else, else_to_end, else_to_if

    def _innermost_loop(self, idx: int, loop_map: Dict[int, int]) -> Optional[Tuple[int, int]]:
        candidate: Optional[Tuple[int, int]] = None
        for start, end in loop_map.items():
            if start <= idx <= end:
                if candidate is None or start > candidate[0]:
                    candidate = (start, end)
        return candidate

    def play(self) -> None:
        loop_start_to_end, loop_end_to_start = self._build_loop_maps()
        if_to_end, if_to_else, else_to_end, else_to_if = self._build_if_maps()
        loop_state: Dict[int, Dict[str, int]] = {}
        if_results: Dict[int, bool] = {}

        i = 0
        while i < len(self.events) and not self.stop_request:
            ev = self.events[i]
            if ev.dt > 0:
                time.sleep(max(ev.dt, MIN_DELAY))
            if ev.type == "mouse":
                self._play_mouse(ev)
                i += 1
                continue
            if ev.type == "keyboard":
                self._play_keyboard(ev)
                i += 1
                continue
            if ev.type == "color" and ev.event == "sample":
                i += 1
                continue
            if ev.type == "string":
                x1, y1, x2, y2 = ev.x, ev.y, ev.x2, ev.y2
                try:
                    shot = pag.screenshot(region=(x1, y1, x2 - x1, y2 - y1))
                except Exception:
                    shot = None
                if shot and pytesseract:
                    text = pytesseract.image_to_string(shot, lang=ev.lang).strip()
                    if pyperclip:
                        pyperclip.copy(text)
                i += 1
                continue
            if ev.type == "control":
                if ev.event == "loop_start":
                    loop_state.setdefault(i, {"count": 0})
                    i += 1
                elif ev.event == "loop_end":
                    start = loop_end_to_start.get(i)
                    if start is None:
                        i += 1
                        continue
                    state = loop_state.setdefault(start, {"count": 0})
                    state["count"] += 1
                    max_count = self.events[start].count
                    if state["count"] < max_count:
                        i = start + 1
                    else:
                        i += 1
                elif ev.event == "break":
                    loop_info = self._innermost_loop(i, loop_start_to_end)
                    if loop_info is None:
                        i += 1
                        continue
                    start, end = loop_info
                    loop_state.setdefault(start, {"count": self.events[start].count})
                    i = end + 1
                elif ev.event == "if_color":
                    try:
                        r, g, b = pag.pixel(ev.x, ev.y)
                    except Exception:
                        r = g = b = 0
                    diff = sum(abs(a - b) for a, b in zip((r, g, b), ev.rgb or (0, 0, 0)))
                    ok = diff <= ev.tolerance * 3
                    if_results[i] = ok
                    if not ok:
                        if if_to_else.get(i) is not None:
                            i = if_to_else[i] + 1
                        else:
                            i = if_to_end.get(i, i) + 1
                    else:
                        i += 1
                elif ev.event == "if_count":
                    loop_info = self._innermost_loop(i, loop_start_to_end)
                    cur = loop_state.get(loop_info[0], {"count": 0})["count"] if loop_info else 0
                    ok = self._eval_count(cur, ev.op, ev.value)
                    if_results[i] = ok
                    if not ok:
                        if if_to_else.get(i) is not None:
                            i = if_to_else[i] + 1
                        else:
                            i = if_to_end.get(i, i) + 1
                    else:
                        i += 1
                elif ev.event == "if_clip":
                    ok = self._eval_clip(ev.text, ev.mode)
                    if_results[i] = ok
                    if not ok:
                        if if_to_else.get(i) is not None:
                            i = if_to_else[i] + 1
                        else:
                            i = if_to_end.get(i, i) + 1
                    else:
                        i += 1
                elif ev.event == "else":
                    start = else_to_if.get(i)
                    if start is None:
                        i += 1
                        continue
                    if if_results.get(start, False):
                        i = else_to_end.get(i, i) + 1
                    else:
                        i += 1
                elif ev.event == "if_end":
                    i += 1
                elif ev.event == "wait_color":
                    timeout = ev.value if ev.value else 0
                    start_time = time.time()
                    while not self.stop_request:
                        try:
                            r, g, b = pag.pixel(ev.x, ev.y)
                        except Exception:
                            r = g = b = 0
                        diff = sum(abs(a - b) for a, b in zip((r, g, b), ev.rgb or (0, 0, 0)))
                        if diff <= ev.tolerance * 3:
                            break
                        if timeout and time.time() - start_time > timeout:
                            break
                        time.sleep(max(ev.interval, MIN_DELAY))
                    i += 1
                elif ev.event == "block_start":
                    i += 1
                elif ev.event == "block_end":
                    i += 1
                else:
                    i += 1
            else:
                i += 1

    # -------------------------------------------------------------- persistence
    def save(self, path: str, name: str = "macro") -> None:
        data = {
            "name": name,
            "events": [self._event_to_dict(ev) for ev in self.events],
        }
        with open(path, "w", encoding="utf-8") as fh:
            json.dump(data, fh, ensure_ascii=False, indent=2)

    def load(self, path: str) -> Tuple[str, int]:
        with open(path, "r", encoding="utf-8") as fh:
            data = json.load(fh)
        events = []
        for raw in data.get("events", []):
            ev = MacroEvent(**raw)
            ev.ensure_min_delay()
            events.append(ev)
        self.events = events
        return data.get("name", ""), len(events)

    # ----------------------------------------------------------------- helpers
    def _event_to_dict(self, ev: MacroEvent) -> Dict[str, object]:
        payload = ev.__dict__.copy()
        payload["path"] = [point.__dict__ for point in ev.path]
        return payload


class MacroGUI:
    """Tkinter based macro editor."""

    TYPE_HINTS: Dict[str, str] = {
        "MOVE": "마우스를 지정 좌표로 이동합니다.",
        "MOVE_REL": "현재 위치에서 상대 이동(dx, dy).",
        "CLICK": "누르고 떼는 클릭 한 번.",
        "CLICK_DOWN": "마우스 버튼 누르기.",
        "CLICK_UP": "마우스 버튼 떼기.",
        "DRAG": "누른 상태에서 이동 후 떼기.",
        "SCROLL": "지정 좌표에서 스크롤(dx,dy).",
        "KEY": "키 또는 조합키 입력.",
        "KEY_DOWN": "키 누르기.",
        "KEY_UP": "키 떼기.",
        "COLOR": "화면 픽셀 색상 기록.",
        "STRING": "OCR 영역을 읽어 클립보드에 복사.",
        "IF_COLOR": "픽셀 색이 일치하면 분기.",
        "IF_COUNT": "루프 반복 횟수 조건.",
        "IF_CLIP": "클립보드 내용 비교.",
        "ELSE": "IF가 실패했을 때 실행 영역 시작.",
        "IF_END": "IF/ELSE 영역 종료.",
        "WAIT_COLOR": "지정 픽셀이 원하는 색이 될 때까지 대기.",
        "BLOCK_START": "블록 영역 시작 (가독용).",
        "BLOCK_END": "블록 영역 종료.",
        "LOOP_START": "루프 시작.",
        "LOOP_END": "루프 종료.",
        "BREAK": "루프 즉시 탈출.",
    }

    def __init__(self, root: tk.Tk) -> None:
        self.root = root
        self.root.title("Macro Recorder")
        self.recorder = MacroRecorder()
        self.selected_index: Optional[int] = None
        self.copied_events: List[MacroEvent] = []
        self.capture_mode: Optional[str] = None
        self.cell_editor = None
        self.rgb_style_cache: Dict[str, str] = {}

        self._build_gui()
        self.root.after(150, self._update_mouse_info)

    # --------------------------------------------------------------- ui layout
    def _build_gui(self) -> None:
        frame = tk.Frame(self.root, padx=8, pady=8)
        frame.pack(fill=tk.BOTH, expand=True)

        toolbar = tk.Frame(frame)
        toolbar.grid(row=0, column=0, columnspan=8, sticky="we")

        self.entry_name = tk.Entry(toolbar, width=20)
        self.entry_name.insert(0, "macro")
        self.entry_name.pack(side="left", padx=(0, 12))

        self.entry_merge = tk.Entry(toolbar, width=6)
        self.entry_merge.insert(0, "150")
        ttk.Button(toolbar, text="녹화(상세)", command=lambda: self.start_record(True)).pack(side="left", padx=2)
        ttk.Button(toolbar, text="녹화(간단)", command=lambda: self.start_record(False)).pack(side="left", padx=2)
        ttk.Button(toolbar, text="정지", command=self.stop_record).pack(side="left", padx=8)
        ttk.Button(toolbar, text="재생", command=self.play_macro).pack(side="left", padx=2)
        ttk.Button(toolbar, text="저장", command=self.save_macro).pack(side="left", padx=2)
        ttk.Button(toolbar, text="불러오기", command=self.load_macro).pack(side="left", padx=2)

        self.status_var = tk.StringVar(value="준비")
        tk.Label(frame, textvariable=self.status_var, fg="blue").grid(row=1, column=0, columnspan=8, sticky="w", pady=4)
        self.count_var = tk.StringVar(value="이벤트: 0")
        tk.Label(frame, textvariable=self.count_var).grid(row=2, column=0, columnspan=8, sticky="w")

        columns = ("idx", "type", "info", "x", "y", "rgb", "key", "delay")
        self.tree = ttk.Treeview(frame, columns=columns, show="headings", selectmode="extended", height=18)
        for name, text, width in (
            ("idx", "#", 50),
            ("type", "Type", 110),
            ("info", "Info", 200),
            ("x", "X", 70),
            ("y", "Y", 70),
            ("rgb", "RGB", 150),
            ("key", "Key", 170),
            ("delay", "지연(ms)", 80),
        ):
            self.tree.heading(name, text=text)
            self.tree.column(name, width=width, anchor="w")

        self.tree.grid(row=3, column=0, columnspan=8, sticky="nsew")
        scroll = ttk.Scrollbar(frame, orient=tk.VERTICAL, command=self.tree.yview)
        self.tree.configure(yscrollcommand=scroll.set)
        scroll.grid(row=3, column=8, sticky="ns")
        frame.rowconfigure(3, weight=1)

        self.tree.bind("<<TreeviewSelect>>", self._on_select)

        info_frame = tk.Frame(frame)
        info_frame.grid(row=4, column=0, columnspan=8, sticky="we", pady=6)
        self.mouse_info = tk.StringVar(value="마우스: x=?, y=?")
        tk.Label(info_frame, textvariable=self.mouse_info).pack(side="left")

    # ------------------------------------------------------------- gui events
    def start_record(self, record_moves: bool) -> None:
        try:
            merge = int(self.entry_merge.get()) / 1000.0
        except ValueError:
            merge = 0.15
        self.recorder.start_record(record_moves=record_moves, merge_threshold_sec=merge)
        self.status_var.set("녹화 중 (Ctrl+Alt+F12)")

    def stop_record(self) -> None:
        self.recorder.stop_record()
        self.status_var.set("녹화 종료")
        self._refresh_tree()

    def play_macro(self) -> None:
        def worker() -> None:
            self.status_var.set("재생 중")
            self.recorder.play()
            self.status_var.set("준비")

        threading.Thread(target=worker, daemon=True).start()

    def save_macro(self) -> None:
        if not self.recorder.events:
            messagebox.showwarning("저장", "저장할 이벤트가 없습니다.")
            return
        name = self.entry_name.get() or "macro"
        path = filedialog.asksaveasfilename(defaultextension=".json", filetypes=[["JSON", "*.json"]])
        if not path:
            return
        self.recorder.save(path, name=name)
        self.status_var.set(f"저장 완료: {path}")

    def load_macro(self) -> None:
        path = filedialog.askopenfilename(filetypes=[["JSON", "*.json"]])
        if not path:
            return
        name, count = self.recorder.load(path)
        if name:
            self.entry_name.delete(0, tk.END)
            self.entry_name.insert(0, name)
        self.status_var.set(f"불러오기 완료 ({count} events)")
        self._refresh_tree()

    # -------------------------------------------------------------- tree utils
    def _refresh_tree(self) -> None:
        self.tree.delete(*self.tree.get_children())
        for idx, ev in enumerate(self.recorder.events):
            row = self._event_to_row(idx, ev)
            tag = self._tag_for_rgb(ev)
            kwargs = {"tags": (tag,)} if tag else {}
            self.tree.insert("", tk.END, iid=str(idx), values=row, **kwargs)
        self.count_var.set(f"이벤트: {len(self.recorder.events)}")

    def _tag_for_rgb(self, ev: MacroEvent) -> Optional[str]:
        if ev.rgb is None:
            return None
        r, g, b = ev.rgb
        color = f"#{r:02x}{g:02x}{b:02x}"
        if color not in self.rgb_style_cache:
            fg = "#000000" if (0.299 * r + 0.587 * g + 0.114 * b) > 186 else "#ffffff"
            self.tree.tag_configure(color, background=color, foreground=fg)
            self.rgb_style_cache[color] = color
        return self.rgb_style_cache[color]

    def _event_to_row(self, idx: int, ev: MacroEvent) -> Tuple[str, ...]:
        delay_ms = int(round(max(ev.dt, MIN_DELAY) * 1000))
        info = ""
        rgb = ""
        key = ev.key
        if ev.event == "scroll":
            info = f"dx={ev.dx},dy={ev.dy}"
        elif ev.event in {"click", "click_combined", "drag"}:
            info = f"btn={ev.button.split('.')[-1]}"
            if ev.event == "drag" and ev.path:
                last = ev.path[-1]
                info += f",x2={last.x},y2={last.y}"
        elif ev.event == "string":
            info = f"x2={ev.x2},y2={ev.y2},lang={ev.lang}"
        elif ev.event == "if_color":
            info = f"tol={ev.tolerance}"
        elif ev.event == "if_count":
            info = f"{ev.op}{ev.value}"
        elif ev.event == "if_clip":
            info = f"mode={ev.mode}"
        elif ev.event == "wait_color":
            info = f"tol={ev.tolerance},interval={ev.interval}"
        elif ev.event == "loop_start":
            info = f"count={ev.count}"
        elif ev.event == "block_start":
            info = ev.block
        elif ev.event == "block_end":
            info = ev.block
        if ev.rgb:
            rgb = f"{ev.rgb[0]},{ev.rgb[1]},{ev.rgb[2]}"
        return (
            str(idx),
            self._type_from_event(ev),
            info,
            str(ev.x),
            str(ev.y),
            rgb,
            key,
            str(delay_ms),
        )

    @staticmethod
    def _type_from_event(ev: MacroEvent) -> str:
        mapping = {
            "move": "MOVE",
            "move_rel": "MOVE_REL",
            "click": "CLICK_DOWN" if ev.pressed else "CLICK_UP",
            "click_combined": "CLICK",
            "drag": "DRAG",
            "scroll": "SCROLL",
            "stroke": "KEY",
            "down": "KEY_DOWN",
            "up": "KEY_UP",
            "sample": "COLOR",
            "capture": "STRING",
            "if_color": "IF_COLOR",
            "if_count": "IF_COUNT",
            "if_clip": "IF_CLIP",
            "if_end": "IF_END",
            "else": "ELSE",
            "wait_color": "WAIT_COLOR",
            "loop_start": "LOOP_START",
            "loop_end": "LOOP_END",
            "break": "BREAK",
            "block_start": "BLOCK_START",
            "block_end": "BLOCK_END",
        }
        return mapping.get(ev.event, ev.event.upper())

    # ----------------------------------------------------------- selection info
    def _on_select(self, _: object) -> None:
        sel = self.tree.selection()
        if not sel:
            return
        idx = int(sel[-1])
        self.selected_index = idx
        ev = self.recorder.events[idx]
        hint = self.TYPE_HINTS.get(self._type_from_event(ev), "")
        if hint:
            self.status_var.set(hint)

    # ----------------------------------------------------------- mouse tracker
    def _update_mouse_info(self) -> None:
        try:
            x, y = pag.position()
            r, g, b = pag.pixel(x, y)
            self.mouse_info.set(f"마우스: x={x}, y={y}, rgb=({r},{g},{b})")
        except Exception:
            self.mouse_info.set("마우스 정보를 읽을 수 없습니다.")
        self.root.after(150, self._update_mouse_info)

    # -------------------------------------------------------------- app runner
    def run(self) -> None:
        self.root.mainloop()


def main() -> None:
    root = tk.Tk()
    app = MacroGUI(root)
    app.run()


if __name__ == "__main__":
    main()
