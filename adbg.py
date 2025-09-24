#!/usr/bin/env python3
import argparse
import socket
import logging
import cmd
import sys
import signal
import struct
import shlex
import re
import os
import math
import bisect
import time
from collections import deque
from typing import Optional, Tuple, Dict, List

from capstone import Cs, CS_ARCH_X86, CS_MODE_16, CS_MODE_32

from capstone.x86_const import (
    X86_OP_IMM,
    X86_OP_MEM,
    X86_REG_EIP,
    X86_INS_CALL,
    X86_INS_JMP,
    X86_GRP_JUMP,
    X86_GRP_CALL,
    X86_GRP_INT,
    X86_INS_RET,
    X86_INS_RETF,
)

logging.basicConfig(level=logging.INFO)
logger = logging.getLogger("adbg_cli")

FAS_SIG = 0x1A736166


def u8(b, o):
    return b[o]


def u16(b, o):
    return struct.unpack_from("<H", b, o)[0]


def u32(b, o):
    return struct.unpack_from("<I", b, o)[0]


def u64(b, o):
    return struct.unpack_from("<Q", b, o)[0]


def i32(b, o):
    return struct.unpack_from("<i", b, o)[0]


class _Colors:
    def __init__(self, enabled: bool):
        if enabled:
            self.RESET = "\x1b[0m"
            self.BOLD = "\x1b[1m"
            self.DIM = "\x1b[2m"
            self.GRAY = "\x1b[90m"
            self.RED = "\x1b[31m"
            self.GREEN = "\x1b[32m"
            self.YELLOW = "\x1b[33m"
            self.BLUE = "\x1b[34m"
            self.MAGENTA = "\x1b[35m"
            self.CYAN = "\x1b[36m"
        else:
            self.RESET = ""
            self.BOLD = ""
            self.DIM = ""
            self.GRAY = ""
            self.RED = ""
            self.GREEN = ""
            self.YELLOW = ""
            self.BLUE = ""
            self.MAGENTA = ""
            self.CYAN = ""


def _color_enabled() -> bool:
    if os.environ.get("NO_COLOR"):
        return False
    try:
        return sys.stdout.isatty()
    except Exception:
        return False


C = _Colors(_color_enabled())


class FasFile:
    def __init__(self, data: bytes):
        self.data = data
        self.header_len = 0
        self.off_str = self.len_str = 0
        self.off_sym = self.len_sym = 0
        self.off_src = self.len_src = 0
        self.off_asm = self.len_asm = 0
        self.off_secn = self.len_secn = 0
        self.off_syref = self.len_syref = 0

        self.input_name_off = 0
        self.output_name_off = 0

        self.section_names: List[str] = []
        self.symbols: List[dict] = []
        self.addr2line: Dict[int, Tuple[str, int, str, bool]] = {}

        self._parse_header()
        self._parse_sections()
        self._parse_symbols()
        self._parse_asm_dump_addr2line()

    def _parse_header(self):
        b = self.data
        if len(b) < 16:
            raise ValueError("FAS: too small")
        sig = u32(b, 0)
        if sig != FAS_SIG:
            raise ValueError("FAS: bad signature")
        maj = u8(b, 4)
        min_ = u8(b, 5)
        self.header_len = u16(b, 6)

        self.input_name_off = u32(b, 8)
        self.output_name_off = u32(b, 12)
        self.off_str = u32(b, 16)
        self.len_str = u32(b, 20)

        if self.header_len >= 64:
            self.off_sym = u32(b, 24)
            self.len_sym = u32(b, 28)
            self.off_src = u32(b, 32)
            self.len_src = u32(b, 36)
            self.off_asm = u32(b, 40)
            self.len_asm = u32(b, 44)
            self.off_secn = u32(b, 48)
            self.len_secn = u32(b, 52)
            self.off_syref = u32(b, 56)
            self.len_syref = u32(b, 60)

        logger.debug(
            "FAS header: v%d.%d, hdr=%d bytes, strings@%d+%d, syms@%d+%d, src@%d+%d, asm@%d+%d",
            maj,
            min_,
            self.header_len,
            self.off_str,
            self.len_str,
            self.off_sym,
            self.len_sym,
            self.off_src,
            self.len_src,
            self.off_asm,
            self.len_asm,
        )

    def _bounds(self, off, length):
        if off == 0 or length == 0:
            return False
        if off + length > len(self.data):
            return False
        return True

    def get_str_from_strtab(self, off_in_strtab) -> str:
        if off_in_strtab == 0:
            return ""
        start = self.off_str + off_in_strtab
        sect_end = self.off_str + self.len_str
        if start < self.off_str or start >= sect_end:
            self._log_bad_offset("strtab", start)
            return ""
        end = self.data.find(b"\x00", start, sect_end)
        if end == -1:
            end = sect_end
        if end < start or end > sect_end:
            self._log_bad_offset("strtab", start)
            return ""
        return self.data[start:end].decode("utf-8", errors="replace")

    def get_cstr_from_preproc(self, off_in_preproc) -> str:
        if off_in_preproc == 0:
            return ""
        start = self.off_src + off_in_preproc
        sect_end = self.off_src + self.len_src
        if start < self.off_src or start >= sect_end:
            self._log_bad_offset("preproc-cstr", start)
            return ""
        end = self.data.find(b"\x00", start, sect_end)
        if end == -1:
            end = sect_end
        if end < start or end > sect_end:
            self._log_bad_offset("preproc-cstr", start)
            return ""
        return self.data[start:end].decode("utf-8", errors="replace")

    def get_pascal_from_preproc(self, off_in_preproc) -> str:
        if off_in_preproc == 0:
            return ""
        p = self.off_src + off_in_preproc
        sect_end = self.off_src + self.len_src
        if p < self.off_src or p >= sect_end:
            self._log_bad_offset("preproc-pascal", p)
            return ""
        ln = u8(self.data, p)
        start = p + 1
        end = start + ln
        if start > sect_end or end > sect_end or end < start:
            self._log_bad_offset("preproc-pascal", p)
            return ""
        s = self.data[start:end]
        return s.decode("utf-8", errors="replace")

    def _parse_sections(self):
        self.section_names = []
        if self._bounds(self.off_secn, self.len_secn) and self.len_secn % 4 == 0:
            count = self.len_secn // 4
            for i in range(count):
                off = u32(self.data, self.off_secn + i * 4)
                self.section_names.append(self.get_str_from_strtab(off))

    def _parse_symbols(self):
        self.symbols = []
        if not self._bounds(self.off_sym, self.len_sym):
            return
        if self.len_sym % 32 != 0:
            logger.warning("FAS: symbols table length is not multiple of 32 bytes")
        n = self.len_sym // 32
        for i in range(n):
            base = self.off_sym + i * 32
            val = u64(self.data, base + 0)
            flags = u16(self.data, base + 8)
            size = u8(self.data, base + 10)
            vtype = struct.unpack_from("<b", self.data, base + 11)[0]
            exsib = u32(self.data, base + 12)
            pass_def = u16(self.data, base + 16)
            pass_use = u16(self.data, base + 18)
            reloc_info = u32(self.data, base + 20)
            name_off = u32(self.data, base + 24)
            def_line_off = u32(self.data, base + 28)

            if name_off == 0:
                name = ""
            elif (name_off & 0x80000000) != 0:
                name = self.get_str_from_strtab(name_off & 0x7FFFFFFF)
            else:
                name = self.get_pascal_from_preproc(name_off)

            sym = {
                "value": val,
                "flags": flags,
                "size": size,
                "type": vtype,
                "exsib": exsib,
                "pass_def": pass_def,
                "pass_use": pass_use,
                "reloc": reloc_info,
                "name": name,
                "def_line_off": def_line_off,
            }
            self.symbols.append(sym)

    def decode_line_meta(self, line_off: int):
        if line_off == 0 or not self._bounds(self.off_src + line_off, 16):
            return None

        o = self.off_src + line_off
        f0 = u32(self.data, o + 0)
        f1 = u32(self.data, o + 4)
        f2 = u32(self.data, o + 8)
        f3 = u32(self.data, o + 12)

        generated = True if (f1 & 0x80000000) != 0 else False
        line_no = f1 & 0x7FFFFFFF

        if generated:
            macro = self.get_pascal_from_preproc(f0)
            return {
                "generated": True,
                "line_no": line_no,
                "file": "",
                "macro_name": macro,
            }
        else:
            if f0 == 0:
                file_name = self.get_str_from_strtab(self.input_name_off)
            else:
                file_name = self.get_cstr_from_preproc(f0)
            return {
                "generated": False,
                "line_no": line_no,
                "file": file_name,
                "macro_name": "",
            }

    def _parse_asm_dump_addr2line(self):
        self.addr2line = {}
        if not self._bounds(self.off_asm, self.len_asm) or self.len_asm < 4:
            return
        rows_len = self.len_asm - 4
        if rows_len % 28 != 0:
            rows_len -= rows_len % 28
        rows = rows_len // 28
        for i in range(rows):
            base = self.off_asm + i * 28
            out_off = u32(self.data, base + 0)
            line_off = u32(self.data, base + 4)
            addr_lo = u64(self.data, base + 8)
            exsib = u32(self.data, base + 16)
            reloc = u32(self.data, base + 20)
            addr_type = struct.unpack_from("<b", self.data, base + 24)[0]
            code_type = u8(self.data, base + 25)
            flags = u8(self.data, base + 26)
            addr_hi = u8(self.data, base + 27)

            if addr_type == 0:
                addr = (addr_hi << 64) | addr_lo

                lm = self.decode_line_meta(line_off)
                if lm:
                    file_name = lm["file"] if not lm["generated"] else ""
                    macro_name = lm["macro_name"] if lm["generated"] else ""
                    self.addr2line.setdefault(
                        addr, (file_name, lm["line_no"], macro_name, lm["generated"])
                    )

    def _log_bad_offset(self, what: str, off: int):
        start = max(0, off - 16)
        end = min(len(self.data), off + 16)
        snippet = " ".join(f"{b:02x}" for b in self.data[start:end])
        logger.warning(
            "FAS: invalid offset in %s at 0x%x; around: %s", what, off, snippet
        )


def parse_fas(path):
    with open(path, "rb") as f:
        data = f.read()
    fas = FasFile(data)

    sym2addr: Dict[str, int] = {}
    addr2sym: Dict[int, str] = {}

    for s in fas.symbols:
        name = s["name"]
        if not name:
            continue
        if (s["flags"] & 0x0001) == 0:
            continue
        val = int(s["value"] & 0xFFFFFFFFFFFFFFFF)
        if name not in sym2addr:
            sym2addr[name] = val
        addr2sym.setdefault(val, name)

    return sym2addr, addr2sym, fas


class RSPClient:
    def __init__(self, host, port, timeout=0.5):
        self.sock = socket.create_connection((host, port), timeout)
        self.sock.settimeout(timeout)
        try:
            self._read_packet()
        except IOError:
            pass

    def _checksum(self, data: bytes) -> int:
        return sum(data) % 256

    def _read_packet(self) -> str:
        while True:
            ch = self.sock.recv(1)
            if not ch:
                raise IOError("Disconnected")
            if ch == b"$":
                break
        data = bytearray()
        while True:
            ch = self.sock.recv(1)
            if not ch:
                raise IOError("Disconnected")
            if ch == b"#":
                break
            data += ch

        _ = self.sock.recv(2)

        self.sock.send(b"+")
        return data.decode()

    def _send_packet(self, payload: str) -> str:
        raw = payload.encode()
        chk = self._checksum(raw)
        pkt = b"$" + raw + b"#" + f"{chk:02x}".encode()
        attempt = 0
        last_stage = "send"
        while attempt < 2:
            try:
                last_stage = "send"
                self.sock.send(pkt)
                last_stage = "recv-ack"
                ack = self.sock.recv(1)
                if ack != b"+":
                    raise IOError("No ACK from stub")
                last_stage = "recv-packet"
                return self._read_packet()
            except Exception as e:
                attempt += 1
                if attempt >= 2:
                    head = payload[:16]
                    raise IOError(
                        f"RSP _send_packet failed during {last_stage}: payload='{head}' expected_ack='+' error={e}"
                    )
                time.sleep(0.05)

    def get_regs(self) -> dict:
        raw = self._send_packet("g")
        names = [
            "EAX",
            "ECX",
            "EDX",
            "EBX",
            "ESP",
            "EBP",
            "ESI",
            "EDI",
            "EIP",
            "EFLAGS",
            "CS",
            "SS",
            "DS",
            "ES",
            "FS",
            "GS",
        ]
        regs = {}
        for i, n in enumerate(names):
            chunk = raw[i * 8 : (i + 1) * 8]
            le = "".join(chunk[j : j + 2] for j in (6, 4, 2, 0))
            regs[n] = int(le, 16)
        return regs

    def read_mem(self, addr: int, length: int) -> bytes:
        resp = self._send_packet(f"m{addr:x},{length:x}")
        if resp.startswith("E") and len(resp) == 3:
            raise IOError(f"Read error {resp}")
        return bytes(int(resp[i : i + 2], 16) for i in range(0, len(resp), 2))

    def write_mem(self, addr: int, data: bytes):
        hexdata = "".join(f"{b:02x}" for b in data)
        resp = self._send_packet(f"M{addr:x},{len(data):x}:{hexdata}")
        if resp != "OK":
            raise IOError(f"Write failed: {resp}")

    def step(self):
        self._send_packet("s")

    def cont(self):
        self._send_packet("c")

    def set_break(self, addr: int):
        self._send_packet(f"Z0,{addr:x},1")

    def remove_break(self, addr: int):
        self._send_packet(f"z0,{addr:x},1")

    def set_watch(self, addr: int, kind: int = 3, length: int = 1):
        self._send_packet(f"Z{kind},{addr:x},{length:x}")

    def remove_watch(self, addr: int, kind: int = 3, length: int = 1):
        self._send_packet(f"z{kind},{addr:x},{length:x}")


class Disassembler:
    def __init__(self, default_mode="x86_16"):
        self.mode = default_mode
        self._syntax = "intel"
        self.cs = Cs(
            CS_ARCH_X86, CS_MODE_16 if default_mode == "x86_16" else CS_MODE_32
        )
        self.cs.detail = True
        self._apply_syntax()

    def _apply_syntax(self):
        try:
            from capstone import CS_OPT_SYNTAX_ATT, CS_OPT_SYNTAX_INTEL

            self.cs.syntax = (
                CS_OPT_SYNTAX_INTEL if self._syntax == "intel" else CS_OPT_SYNTAX_ATT
            )
        except Exception:
            pass
        return self.cs

    def update_mode(self, regs: dict):
        vm86 = bool(regs["EFLAGS"] & (1 << 17))
        new_mode = "x86_16" if vm86 else "x86_32"
        if new_mode != self.mode:
            self.mode = new_mode
            m = CS_MODE_16 if vm86 else CS_MODE_32
            self.cs = Cs(CS_ARCH_X86, m)
            self.cs.detail = True
            self._apply_syntax()
            logger.info(f"Switched disassembler to {self.mode}")
        return self.cs

    def set_syntax(self, syntax: str):
        self._syntax = "att" if syntax.lower() == "att" else "intel"
        self._apply_syntax()


def hexdump(addr: int, data: bytes, width: int = 16):
    for off in range(0, len(data), width):
        line = data[off : off + width]
        hexpart = " ".join(f"{b:02x}" for b in line)
        asciipart = "".join(chr(b) if 32 <= b < 127 else "." for b in line)
        print(
            f"{C.DIM}0x{addr+off:08x}:{C.RESET} {hexpart:<{width*3}} {C.GRAY}{asciipart}{C.RESET}"
        )


class MergedFas:
    def __init__(self, fas_list: List[FasFile]):
        self.addr2line: Dict[int, Tuple[str, int, str, bool]] = {}
        for fas in fas_list:
            for addr, src in fas.addr2line.items():
                self.addr2line.setdefault(addr, src)
        self._sorted_addrs = sorted(self.addr2line.keys())

        self._intervals: List[Tuple[int, int, Tuple[str, int, str, bool]]] = []
        if self._sorted_addrs:
            for idx, start in enumerate(self._sorted_addrs):
                end = (
                    self._sorted_addrs[idx + 1]
                    if idx + 1 < len(self._sorted_addrs)
                    else start + 1
                )
                meta = self.addr2line[start]
                if end <= start:
                    end = start + 1
                self._intervals.append((start, end, meta))
        self._interval_starts: List[int] = [s for s, _, _ in self._intervals]

    def get_line_exact(self, addr: int) -> Optional[Tuple[str, int, str, bool]]:
        return self.addr2line.get(addr)

    def get_line_near(self, addr: int) -> Optional[Tuple[str, int, str, bool]]:
        if not self._sorted_addrs:
            return None
        i = bisect.bisect_right(self._sorted_addrs, addr)
        if i == 0:
            return None
        return self.addr2line.get(self._sorted_addrs[i - 1])

    def get_line_covering(self, addr: int) -> Optional[Tuple[str, int, str, bool]]:
        if not self._intervals:
            return None
        i = bisect.bisect_right(self._interval_starts, addr) - 1
        if i < 0:
            return None
        start, end, meta = self._intervals[i]
        if start <= addr < end:
            return meta
        return None


class CFG:
    def __init__(self):
        self.adj: Dict[int, Dict[int, int]] = {}
        self.visits: Dict[int, int] = {}
        self.first_seen: Dict[int, float] = {}
        self.last_seen: Dict[int, float] = {}

    def add_node(self, u: int, ts: float):
        if u not in self.visits:
            self.visits[u] = 0
            self.first_seen[u] = ts
        self.last_seen[u] = ts
        self.visits[u] += 1

    def add_edge(self, u: int, v: int, ts: float):
        self.add_node(u, ts)
        self.add_node(v, ts)
        self.adj.setdefault(u, {}).setdefault(v, 0)
        self.adj[u][v] += 1

    def nodes(self):
        return self.visits.keys()

    def edges(self):
        for u, nbrs in self.adj.items():
            for v, c in nbrs.items():
                yield (u, v, c)

    def top_nodes(self, k=10):
        return sorted(self.visits.items(), key=lambda kv: kv[1], reverse=True)[:k]

    def top_edges(self, k=10):
        return sorted(self.edges(), key=lambda e: e[2], reverse=True)[:k]

    def sccs(self) -> List[set]:
        index = 0
        stack: List[int] = []
        onstack: Dict[int, bool] = {}
        indices: Dict[int, int] = {}
        lowlink: Dict[int, int] = {}
        result: List[set] = []

        def strongconnect(v: int):
            nonlocal index
            indices[v] = index
            lowlink[v] = index
            index += 1
            stack.append(v)
            onstack[v] = True
            for w in self.adj.get(v, {}):
                if w not in indices:
                    strongconnect(w)
                    lowlink[v] = min(lowlink[v], lowlink[w])
                elif onstack.get(w, False):
                    lowlink[v] = min(lowlink[v], indices[w])
            if lowlink[v] == indices[v]:
                comp = set()
                while True:
                    w = stack.pop()
                    onstack[w] = False
                    comp.add(w)
                    if w == v:
                        break
                result.append(comp)

        for v in list(self.nodes()):
            if v not in indices:
                strongconnect(v)
        return result


def extract_scc_containing(
    cfg: CFG, node: int, region: Optional[Tuple[int, int]] = None
):
    in_region = lambda addr: True if region is None else (region[0] <= addr < region[1])
    for comp in cfg.sccs():
        if node in comp:
            has_out = False
            for u in comp:
                for v in cfg.adj.get(u, {}):
                    if v not in comp and in_region(v):
                        has_out = True
                        break
                if has_out:
                    break
            return comp, has_out

    return {node}, False


class ADbgCLI(cmd.Cmd):
    intro = (
        "adbg_cli — simple assembly debugger\n" "Type `help` or `?` to list commands.\n"
    )
    prompt = "(adbg) "

    _gp32 = ["EAX", "ECX", "EDX", "EBX", "ESP", "EBP", "ESI", "EDI"]
    _segs = ["CS", "SS", "DS", "ES", "FS", "GS"]

    def __init__(
        self,
        rsp: RSPClient,
        dasm: Disassembler,
        sym2addr: dict,
        addr2sym: dict,
        fas: MergedFas,
        default_reg_width: int = 32,
    ):
        super().__init__()
        self.rsp = rsp
        self.dasm = dasm
        self.sym2addr = sym2addr
        self.addr2sym = addr2sym
        self.fas = fas

        self._sym_index: List[Tuple[int, str]] = sorted(
            ((addr, name) for name, addr in self.sym2addr.items()),
            key=lambda x: x[0],
        )
        self._sym_addrs: List[int] = [a for a, _ in self._sym_index]
        self._sym_conflicts: Dict[str, List[int]] = getattr(self, "_sym_conflicts", {})

        self.breakpoints: Dict[int, int] = {}
        self.next_bp_id = 1

        self.watchpoints: Dict[int, Tuple[int, int, int]] = {}
        self.next_wp_id = 1

        self._show_bytes: bool = False
        self._show_ann: bool = True

        self.reg_width = default_reg_width

    def resolve(self, tok: str) -> int:
        tok = tok.strip().lstrip("*")

        m = re.match(r"^(.*?)([+-])(0x[0-9a-fA-F]+|\d+)$", tok)
        if m:
            base = self.resolve(m.group(1))
            off = int(m.group(3), 0)
            return base + off if m.group(2) == "+" else base - off

        if tok in self.sym2addr:
            return self.sym2addr[tok]

        if tok.startswith("."):
            matches = [n for n in self.sym2addr if n.endswith(tok)]
            if len(matches) == 1:
                return self.sym2addr[matches[0]]
            if len(matches) > 1:
                raise ValueError(
                    f"Ambiguous local {tok}; candidates: "
                    + ", ".join(matches[:8])
                    + (" ..." if len(matches) > 8 else "")
                )
            raise ValueError(f"Unknown local label: {tok}")

        if "." in tok:
            base, local = tok.split(".", 1)
            for b in (base, "_" + base, base.lstrip("_")):
                cand = f"{b}.{local}"
                if cand in self.sym2addr:
                    return self.sym2addr[cand]

        tail = "." + tok
        matches = [n for n in self.sym2addr if n.endswith(tail)]
        if len(matches) == 1:
            return self.sym2addr[matches[0]]
        if len(matches) > 1:
            raise ValueError(
                f"Ambiguous local '{tok}'; try one of: "
                + ", ".join(matches[:8])
                + (" ..." if len(matches) > 8 else "")
            )

        if tok.lower().startswith("0x"):
            return int(tok, 16)
        if tok.isdigit():
            return int(tok)

        raise ValueError(f"Unknown symbol/address: {tok}")

    def _nearest_symbol(self, addr: int):
        i = bisect.bisect_right(self._sym_addrs, addr)
        if i == 0:
            return None
        base_addr, name = self._sym_index[i - 1]
        return name, base_addr, addr - base_addr

    def _format_symbol(
        self, addr: int, *, exact_only: bool = False, max_delta: int = 0x20
    ) -> str:
        sym = self.addr2sym.get(addr)
        if sym:
            return f"{C.CYAN}{sym}{C.RESET}"
        if exact_only:
            return f"0x{addr:08x}"
        near = self._nearest_symbol(addr)
        if near:
            name, base, off = near
            if off == 0:
                return f"{C.CYAN}{name}{C.RESET}"
            if off <= max_delta:
                return f"{C.CYAN}{name}+0x{off:x}{C.RESET}"
        return f"0x{addr:08x}"

    def _get_reg(self, regs: dict, name: str) -> int:
        n = name.upper()
        if n in regs:
            return regs[n]

        if n == "IP":
            return regs["EIP"] & 0xFFFF
        if n == "FLAGS":
            return regs["EFLAGS"] & 0xFFFF

        base_map = {
            "AX": "EAX",
            "CX": "ECX",
            "DX": "EDX",
            "BX": "EBX",
            "SP": "ESP",
            "BP": "EBP",
            "SI": "ESI",
            "DI": "EDI",
        }
        if n in base_map:
            return regs[base_map[n]] & 0xFFFF

        lohi = {
            "AL": "EAX",
            "AH": "EAX",
            "CL": "ECX",
            "CH": "ECX",
            "DL": "EDX",
            "DH": "EDX",
            "BL": "EBX",
            "BH": "EBX",
        }
        if n in lohi:
            v = regs[lohi[n]]
            if n[1] == "L":
                return v & 0xFF
            else:
                return (v >> 8) & 0xFF

        raise KeyError(f"Unknown register '{name}'")

    def print_regs(self, width: int = None):
        regs = self.rsp.get_regs()
        width = width or self.reg_width

        if width == 32:
            names = self._gp32 + ["EIP", "EFLAGS"] + self._segs
            for i in range(0, len(names), 2):
                a = names[i]
                b = names[i + 1] if i + 1 < len(names) else None
                line = f"{C.BOLD}{a:6}{C.RESET}={C.BLUE}0x{regs[a]:08x}{C.RESET}"
                if b:
                    valb = regs[b] & (0xFFFFFFFF if b not in self._segs else 0xFFFF)
                    if b in self._segs:
                        line += (
                            f"   {C.BOLD}{b:6}{C.RESET}={C.BLUE}0x{valb:04x}{C.RESET}"
                        )
                    else:
                        line += (
                            f"   {C.BOLD}{b:6}{C.RESET}={C.BLUE}0x{valb:08x}{C.RESET}"
                        )
                print(line)
        elif width == 16:
            names = [
                "AX",
                "CX",
                "DX",
                "BX",
                "SP",
                "BP",
                "SI",
                "DI",
                "IP",
                "FLAGS",
            ] + self._segs
            vals = {n: self._get_reg(regs, n) for n in names}
            for i in range(0, len(names), 2):
                a = names[i]
                b = names[i + 1] if i + 1 < len(names) else None
                line = f"{C.BOLD}{a:6}{C.RESET}={C.BLUE}0x{vals[a]&0xFFFF:04x}{C.RESET}"
                if b:
                    line += f"   {C.BOLD}{b:6}{C.RESET}={C.BLUE}0x{vals[b]&0xFFFF:04x}{C.RESET}"
                print(line)
        elif width == 8:
            names = ["AL", "CL", "DL", "BL", "AH", "CH", "DH", "BH"]
            for i in range(0, len(names), 2):
                a = names[i]
                b = names[i + 1]
                va = self._get_reg(regs, a)
                vb = self._get_reg(regs, b)
                print(
                    f"{C.BOLD}{a:6}{C.RESET}={C.BLUE}0x{va&0xFF:02x}{C.RESET}   "
                    f"{C.BOLD}{b:6}{C.RESET}={C.BLUE}0x{vb&0xFF:02x}{C.RESET}"
                )
            spl = regs["ESP"] & 0xFF
            sph = (regs["ESP"] >> 8) & 0xFF
            print(
                f"{C.BOLD}{'SPL':6}{C.RESET}={C.BLUE}0x{spl:02x}{C.RESET}   "
                f"{C.BOLD}{'SPH':6}{C.RESET}={C.BLUE}0x{sph:02x}{C.RESET}"
            )
        else:
            print("Unsupported register width; use 8, 16, or 32.")

    def _is_ctrl_flow(self, ins) -> bool:
        if hasattr(ins, "groups") and (
            X86_GRP_JUMP in ins.groups or X86_GRP_CALL in ins.groups
        ):
            return True
        m = ins.mnemonic
        return m == "call" or m == "jmp" or (m and m.startswith("j"))

    def _annotate_operands(self, ins) -> List[str]:
        anns: List[str] = []

        try:
            if self.dasm.mode == "x86_32" and self._is_ctrl_flow(ins):
                for op in getattr(ins, "operands", []):
                    if op.type == X86_OP_IMM:
                        target = int(op.imm) & 0xFFFFFFFF
                        cur = (ins.address + ins.size) & 0xFFFFFFFF
                        disp = (target - cur) & 0xFFFFFFFF

                        sign = "+" if target >= cur else "-"
                        delta = disp if sign == "+" else ((cur - target) & 0xFFFFFFFF)
                        anns.append(f"eip{sign}0x{delta:x}")
        except Exception:
            pass

        if hasattr(ins, "groups") and X86_GRP_INT in ins.groups:
            return anns
        if ins.mnemonic and ins.mnemonic.startswith("int"):
            return anns

        for op in getattr(ins, "operands", []):
            if op.type == X86_OP_IMM:
                target = int(op.imm) & 0xFFFFFFFF

                if target < 0x100:
                    lab = self.addr2sym.get(target)
                    if lab:
                        anns.append(f"→ {self._format_symbol(target, exact_only=True)}")
                    continue

                if self._is_ctrl_flow(ins):
                    anns.append(
                        f"→ {self._format_symbol(target, exact_only=False, max_delta=0x20)}"
                    )
                else:
                    lab = self.addr2sym.get(target)
                    if lab:
                        anns.append(f"→ {self._format_symbol(target, exact_only=True)}")

            elif op.type == X86_OP_MEM:
                mem = op.mem
                if mem.base == 0 and mem.index == 0:
                    addr = mem.disp & 0xFFFFFFFF
                    anns.append(
                        f"[{self._format_symbol(addr, exact_only=False, max_delta=0x100)}]"
                    )
                try:
                    if self.dasm.mode == "x86_32" and mem.base == X86_REG_EIP:
                        disp = mem.disp & 0xFFFFFFFF
                        sign = "+" if mem.disp >= 0 else "-"
                        delta = mem.disp if mem.disp >= 0 else (-mem.disp)
                        target = (ins.address + ins.size + mem.disp) & 0xFFFFFFFF
                        anns.append(f"[eip{sign}0x{delta:x}]")
                        anns.append(
                            f"→ {self._format_symbol(target, exact_only=False, max_delta=0x100)}"
                        )
                except Exception:
                    pass

        return anns

    def print_disasm(self, count=5, addr=None):
        regs = self.rsp.get_regs()
        if addr is None:
            addr = regs["EIP"]
        md = self.dasm.update_mode(regs)

        last_src_key = None
        printed = 0

        start_sym = self.addr2sym.get(addr)
        if not start_sym:
            near = self._nearest_symbol(addr)
            if near and near[2] == 0:
                start_sym = near[0]
        if start_sym:
            print(f"{C.MAGENTA}{start_sym}:{C.RESET}")

        cap = 512
        cur_addr = addr
        buf = b""
        total_read = 0
        while printed < count and total_read < cap:
            if len(buf) < 16 and total_read < cap:
                to_read = min(64, cap - total_read)
                try:
                    chunk = self.rsp.read_mem(cur_addr + len(buf), to_read)
                except Exception:
                    chunk = b""
                if not chunk:
                    break
                buf += chunk
                total_read += len(chunk)

            consumed = 0
            any_decoded = False
            for ins in md.disasm(buf, cur_addr):
                any_decoded = True
                consumed = (ins.address + ins.size) - cur_addr
                if printed >= count:
                    break

                src = (
                    self.fas.get_line_covering(ins.address)
                    or self.fas.get_line_exact(ins.address)
                    or self.fas.get_line_near(ins.address)
                )
                if src:
                    src_key = (src[0], src[1], src[2], src[3])
                    if src_key != last_src_key:
                        file_name, line_no, macro_name, generated = src
                        header = ""
                        if file_name:
                            header += f"{C.YELLOW}{file_name}:{line_no}{C.RESET}"
                        if generated and macro_name:
                            if header:
                                header += f"  {C.GRAY}(macro: {macro_name}){C.RESET}"
                            else:
                                header += (
                                    f"{C.GRAY}macro: {macro_name}#{line_no}{C.RESET}"
                                )
                        if header:
                            print(f"  ; {header}")
                        last_src_key = src_key

                mark = ""
                if ins.address in self.breakpoints.values():
                    mark = f"{C.RED}*{C.RESET}"
                elif any(ins.address == w[0] for w in self.watchpoints.values()):
                    mark = f"{C.RED}w{C.RESET}"

                sym = self.addr2sym.get(ins.address)
                if not sym:
                    near = self._nearest_symbol(ins.address)
                    if near and near[2] == 0:
                        sym = near[0]
                if sym:
                    print(f"{C.MAGENTA}{sym}:{C.RESET}")

                ann_txt = ""
                if self._show_ann:
                    anns = self._annotate_operands(ins)
                    if anns:
                        ann_txt = f"  {C.GRAY}; " + " ".join(anns) + C.RESET

                bytes_txt = ""
                if self._show_bytes:
                    try:
                        raw = bytes(ins.bytes[:8])
                        bytes_txt = " " + " ".join(f"{b:02x}" for b in raw)
                    except Exception:
                        bytes_txt = ""

                print(
                    f"  {C.DIM}0x{ins.address:08x}:{C.RESET}{bytes_txt} {C.BOLD}{ins.mnemonic}{C.RESET} {ins.op_str}{mark}{ann_txt}"
                )
                printed += 1

                if ins.id in (X86_INS_RET, X86_INS_RETF):
                    break

            if not any_decoded:
                break

            if consumed > 0:
                buf = buf[consumed:]
                cur_addr += consumed
            else:
                break

            if printed >= count:
                break

    def _read_u32(self, addr: int) -> Optional[int]:
        try:
            data = self.rsp.read_mem(addr, 4)
            return int.from_bytes(data, "little", signed=False)
        except Exception:
            return None

    def _symbol_and_src(self, addr: int) -> str:
        sym_str = self._format_symbol(addr)
        src = (
            self.fas.get_line_covering(addr)
            or self.fas.get_line_exact(addr)
            or self.fas.get_line_near(addr)
        )
        if src and src[0]:
            return f"{sym_str} {C.GRAY}({src[0]}:{src[1]}){C.RESET}"
        elif src and src[2]:
            return f"{sym_str} {C.GRAY}(macro:{src[2]}#{src[1]}){C.RESET}"
        return sym_str

    def do_bt(self, arg):
        parts = arg.split()
        maxf = int(parts[0], 0) if parts else 16

        regs = self.rsp.get_regs()
        md = self.dasm.update_mode(regs)

        if self.dasm.mode != "x86_32":
            print("bt: only 32-bit EBP-chain unwinding is supported.")
            return

        ebp = regs["EBP"]
        eip = regs["EIP"]

        frames = []
        visited = set()
        for idx in range(maxf):
            frames.append((eip, ebp))
            if ebp in visited or ebp == 0:
                break
            visited.add(ebp)
            saved_eip = self._read_u32(ebp + 4)
            next_ebp = self._read_u32(ebp)
            if saved_eip is None or next_ebp is None:
                break
            if next_ebp <= ebp or (next_ebp - ebp) > (1 << 20):
                frames.append((saved_eip, next_ebp))
                break
            eip = saved_eip
            ebp = next_ebp

        for i, (addr, frame_bp) in enumerate(frames):
            print(
                f"#{i:02d}  {self._symbol_and_src(addr)}  {C.DIM}[ebp=0x{frame_bp:08x}]{C.RESET}"
            )

    help_bt = lambda self: print("bt [max_frames] — print backtrace using EBP-chain.")

    def do_step(self, arg):
        try:
            self.rsp.step()
            self.print_disasm(1)
        except Exception as e:
            print(f"Step error: {e}")

    do_s = do_step

    def do_cont(self, arg):
        try:
            self.rsp.cont()
            self.print_disasm(1)
        except Exception as e:
            print(f"Continue error: {e}")

    do_c = do_cont

    def do_regs(self, arg):
        a = arg.strip()
        if a in ("8", "16", "32", "-8", "-16", "-32"):
            self.reg_width = int(a.lstrip("-"))
        self.print_regs()

    def help_regs(self):
        print(
            "regs [8|16|32]   - show registers; optional width switches view and becomes default"
        )

    def do_reg(self, arg):
        parts = arg.split()
        if not parts:
            print("Usage: reg <name> [8|16|32]")
            return
        name = parts[0]
        width = int(parts[1]) if len(parts) > 1 else self.reg_width
        try:
            regs = self.rsp.get_regs()
            val = self._get_reg(regs, name)
            if width == 8:
                print(f"{name.upper():>6} = 0x{val & 0xFF:02x}")
            elif width == 16:
                print(f"{name.upper():>6} = 0x{val & 0xFFFF:04x}")
            else:
                if name.upper() in regs:
                    print(f"{name.upper():>6} = 0x{val & 0xFFFFFFFF:08x}")
                else:
                    mask = (
                        0xFF
                        if len(name) == 2 and name[1].lower() in ("h", "l")
                        else 0xFFFF
                    )
                    fmt = "02x" if mask == 0xFF else "04x"
                    print(f"{name.upper():>6} = 0x{val & mask:{fmt}}")
        except Exception as e:
            print(e)

    def do_stack(self, arg):
        n = int(arg, 0) if arg else 16
        regs = self.rsp.get_regs()
        esp = regs["ESP"]
        try:
            data = self.rsp.read_mem(esp, n * 4)
        except Exception as e:
            print(f"Stack read error: {e}")
            return
        for i in range(n):
            off = esp + i * 4
            val = int.from_bytes(data[i * 4 : (i + 1) * 4], "little")
            print(
                f"{C.DIM}0x{off:08x}:{C.RESET} {C.BLUE}0x{val:08x}{C.RESET}  {C.GRAY}{self._format_symbol(val)}{C.RESET}"
            )

    def do_disasm(self, arg):
        parts = arg.split()
        addr = None
        cnt = 5
        if parts:
            if (
                parts[0].lower().startswith("0x")
                or parts[0] in self.sym2addr
                or re.match(r".+[+-](0x[0-9a-fA-F]+|\d+)$", parts[0])
            ):
                try:
                    addr = self.resolve(parts[0])
                except ValueError as e:
                    print(e)
                    return
                if len(parts) > 1:
                    cnt = int(parts[1], 0)
            else:
                try:
                    cnt = int(parts[0], 0)
                except ValueError:
                    print(f"Invalid argument: {parts[0]}")
                    return
        self.print_disasm(cnt, addr)

    def do_break(self, arg):
        if not arg:
            print("Usage: break <addr|symbol>")
            return
        try:
            addr = self.resolve(arg.strip())
        except ValueError as e:
            print(e)
            return
        try:
            self.rsp.set_break(addr)
        except Exception as e:
            print(f"Breakpoint error: {e}")
            return
        bid = self.next_bp_id
        self.next_bp_id += 1
        self.breakpoints[bid] = addr
        print(f"Breakpoint {bid} @ {C.BLUE}0x{addr:08x}{C.RESET}")

    do_b = do_break

    def do_delete(self, arg):
        if not arg.isdigit():
            print("Usage: delete <breakpoint-id>")
            return
        bid = int(arg)
        if bid not in self.breakpoints:
            print(f"No such breakpoint {bid}")
            return
        addr = self.breakpoints.pop(bid)
        self.rsp.remove_break(addr)
        print(f"Deleted breakpoint {bid}")

    def do_watch(self, arg):
        parts = arg.split()
        if not parts:
            print("Usage: watch [r|w|a] <addr|symbol> [length]")
            return
        kind_map = {"w": 1, "r": 2, "a": 3}
        kind = 3
        length = 1
        if parts[0].lower() in kind_map and len(parts) >= 2:
            kind = kind_map[parts[0].lower()]
            symtok = parts[1]
            if len(parts) >= 3:
                length = int(parts[2], 0)
        else:
            symtok = parts[0]
            if len(parts) >= 2:
                length = int(parts[1], 0)
        try:
            addr = self.resolve(symtok)
        except ValueError as e:
            print(e)
            return
        try:
            self.rsp.set_watch(addr, kind, length)
        except Exception as e:
            print(f"Watchpoint error: {e}")
            return
        wid = self.next_wp_id
        self.next_wp_id += 1
        self.watchpoints[wid] = (addr, kind, length)
        kn = {1: "write", 2: "read", 3: "access"}[kind]
        print(
            f"Watchpoint {wid} ({kn}) @ {C.BLUE}0x{addr:08x}{C.RESET} length={length}"
        )

    def do_unwatch(self, arg):
        if not arg.isdigit():
            print("Usage: unwatch <watchpoint-id>")
            return
        wid = int(arg)
        if wid not in self.watchpoints:
            print(f"No such watchpoint {wid}")
            return
        addr, kind, length = self.watchpoints.pop(wid)
        self.rsp.remove_watch(addr, kind, length)
        print(f"Deleted watchpoint {wid}")

    def do_info(self, arg):
        sub = arg.strip().lower()
        if sub in ("regs", "registers"):
            self.print_regs()
        elif sub in ("bp", "breakpoints"):
            for bid, a in sorted(self.breakpoints.items()):
                sym = self.addr2sym.get(a, "")
                print(f"{bid}: {C.DIM}0x{a:08x}{C.RESET} {sym}")
        elif sub in ("watch", "watchpoints", "watches"):
            for wid, (a, kind, length) in sorted(self.watchpoints.items()):
                sym = self.addr2sym.get(a, "")
                kn = {1: "write", 2: "read", 3: "access"}[kind]
                print(f"{wid}: {C.DIM}0x{a:08x}{C.RESET} {sym} ({kn}, len={length})")
        elif sub in ("lines", "src", "source"):
            shown = 0
            for addr in sorted(self.fas.addr2line.keys())[:50]:
                f, lno, macro, gen = self.fas.addr2line[addr]
                extra = f"{f}:{lno}" if f else (f"macro:{macro}#{lno}" if macro else "")
                print(f"{C.DIM}0x{addr:08x}{C.RESET} -> {extra}")
                shown += 1
            if shown == 0:
                print(
                    "No addr->source mappings available (likely no absolute $ addresses)."
                )
        else:
            print("Usage: info regs|bp|watch|lines")

    def do_symbols(self, arg):
        q = arg.strip()
        if q.startswith("~"):
            pat = re.compile(q[1:])
            names = [s for s in self.sym2addr if pat.search(s)]
        elif q:
            names = [s for s in self.sym2addr if s.startswith(q) or s.endswith("." + q)]
        else:
            names = sorted(self.sym2addr)
        for s in sorted(names):
            print(f"{s:40} {C.BLUE}0x{self.sym2addr[s]:08x}{C.RESET}")

    def do_peek(self, arg):
        try:
            parts = shlex.split(arg)
            if not parts:
                print("Usage: peek <addr|sym> [length] [size]")
                return
            addr = self.resolve(parts[0])
            length = int(parts[1], 0) if len(parts) >= 2 else 64
            size = int(parts[2], 0) if len(parts) >= 3 else 1
            if length > 1048576:
                print("peek: refusing to read more than 1 MiB")
                return
            data = self.rsp.read_mem(addr, length)
            if size == 1:
                hexdump(addr, data)
            else:
                if size not in (2, 4, 8):
                    print("Size must be 1,2,4, or 8")
                    return
                for off in range(0, len(data), size * 4):
                    chunk = data[off : off + size * 4]
                    vals = []
                    for i in range(0, len(chunk), size):
                        v = int.from_bytes(chunk[i : i + size], "little", signed=False)
                        vals.append(f"0x{v:0{size*2}x}")
                    print(f"{C.DIM}0x{addr+off:08x}:{C.RESET} " + " ".join(vals))
        except Exception as e:
            print(f"Peek error: {e}")

    def do_poke(self, arg):
        try:
            parts = shlex.split(arg)
            if len(parts) < 2:
                print("Usage: poke <addr|sym> <hexbytes|string>")
                return
            addr = self.resolve(parts[0])
            payload = parts[1]
            if re.fullmatch(r"[0-9a-fA-F]+", payload) and len(payload) % 2 == 0:
                data = bytes(
                    int(payload[i : i + 2], 16) for i in range(0, len(payload), 2)
                )
            else:
                data = payload.encode("utf-8", errors="surrogatepass")
            if len(data) > 1048576:
                print("poke: refusing to write more than 1 MiB")
                return
            self.rsp.write_mem(addr, data)
            print(f"Wrote {len(data)} bytes at {C.BLUE}0x{addr:08x}{C.RESET}")
        except Exception as e:
            print(f"Poke error: {e}")

    def _typed_poke(self, arg, size: int):
        try:
            parts = shlex.split(arg)
            if len(parts) < 2:
                print(
                    f"Usage: poke{ {1:'b',2:'w',4:'l',8:'q'}[size] } <addr|sym> <value> [count]"
                )
                return
            addr = self.resolve(parts[0])
            value = int(parts[1], 0)
            count = int(parts[2], 0) if len(parts) >= 3 else 1
            total = size * count
            if total > 1048576:
                print("poke: refusing to write more than 1 MiB")
                return
            data = value.to_bytes(size, "little", signed=False) * count
            self.rsp.write_mem(addr, data)
            print(f"Wrote {count} x {size}-byte value at {C.BLUE}0x{addr:08x}{C.RESET}")
        except Exception as e:
            print(f"Poke error: {e}")

    def do_pokeb(self, arg):
        self._typed_poke(arg, 1)

    def do_pokew(self, arg):
        self._typed_poke(arg, 2)

    def do_pokel(self, arg):
        self._typed_poke(arg, 4)

    def do_pokeq(self, arg):
        self._typed_poke(arg, 8)

    def do_peekf(self, arg):
        try:
            import struct as pystruct

            parts = shlex.split(arg)
            if len(parts) < 2:
                print("Usage: peekf <addr|sym> <struct-fmt> [count]")
                return
            addr = self.resolve(parts[0])
            fmt = parts[1]
            if not fmt or fmt[0] not in "@=<>!":
                fmt = "<" + fmt
            count = int(parts[2], 0) if len(parts) >= 3 else 1
            sz = pystruct.calcsize(fmt)
            if sz * count > 1048576:
                print("peekf: refusing to read more than 1 MiB")
                return
            data = self.rsp.read_mem(addr, sz * count)
            for i in range(count):
                tup = pystruct.unpack_from(fmt, data, i * sz)
                print(
                    f"{C.DIM}0x{addr+i*sz:08x}:{C.RESET} {tup if len(tup)>1 else tup[0]}"
                )
        except Exception as e:
            print(f"peekf error: {e}")

    def do_pokef(self, arg):
        try:
            import struct as pystruct

            parts = shlex.split(arg)
            if len(parts) < 3:
                print("Usage: pokef <addr|sym> <struct-fmt> <v1> [v2 ...]")
                return
            addr = self.resolve(parts[0])
            fmt = parts[1]
            if not fmt or fmt[0] not in "@=<>!":
                fmt = "<" + fmt
            vals = []
            for v in parts[2:]:
                try:
                    vals.append(int(v, 0))
                except ValueError:
                    vals.append(float(v))
            data = pystruct.pack(fmt, *vals)
            if len(data) > 1048576:
                print("pokef: refusing to write more than 1 MiB")
                return
            self.rsp.write_mem(addr, data)
            print(
                f"Wrote struct ({fmt}) of {len(data)} bytes at {C.BLUE}0x{addr:08x}{C.RESET}"
            )
        except Exception as e:
            print(f"pokef error: {e}")

    def do_set(self, arg):
        parts = arg.strip().split()
        if len(parts) != 2:
            print("Usage:\n  set asm intel|att\n  set bytes on|off\n  set ann on|off")
            return
        key, val = parts[0].lower(), parts[1].lower()
        if key == "asm":
            if val not in ("intel", "att"):
                print("set asm: value must be 'intel' or 'att'")
                return
            self.dasm.set_syntax(val)
        elif key == "bytes":
            self._show_bytes = val == "on"
        elif key == "ann":
            self._show_ann = val == "on"
        else:
            print("Unknown setting. Use: asm | bytes | ann")

    def do_q(self, arg):
        return True

    def do_quit(self, arg):
        return True

    def do_exit(self, arg):
        return True

    def help_hunt(self):
        print(
            "hunt [start|symbol|0xADDR|current] [max_steps N] [max_ms M] "
            "[region BASE+LEN | region SYMBOL+LEN] [spin_thresh K] [window W] "
            "[dot on|off] [disasm on|off]\n"
            "Defaults: start=current, max_steps=50000, max_ms=2000, spin_thresh=512, "
            "window=1024, dot=on, disasm=off"
        )

    def do_hunt(self, arg):
        try:
            parts = shlex.split(arg)
        except Exception as e:
            print(f"hunt: argument parse error: {e}")
            return

        start_mode = "current"
        max_steps = 50000
        max_ms = 2000
        spin_thresh = 512
        window = 1024
        want_dot = True
        want_disasm = False
        region: Optional[Tuple[int, int]] = None

        i = 0
        while i < len(parts):
            tok = parts[i].lower()
            if tok in ("current",):
                start_mode = "current"
                i += 1
            elif (
                tok in ("start",)
                or tok.startswith("0x")
                or tok in self.sym2addr
                or "+" in tok
            ):
                start_mode = parts[i]
                i += 1
            elif tok == "max_steps" and i + 1 < len(parts):
                try:
                    max_steps = int(parts[i + 1], 0)
                except Exception:
                    print("hunt: invalid max_steps")
                    return
                i += 2
            elif tok == "max_ms" and i + 1 < len(parts):
                try:
                    max_ms = int(parts[i + 1], 0)
                except Exception:
                    print("hunt: invalid max_ms")
                    return
                i += 2
            elif tok == "spin_thresh" and i + 1 < len(parts):
                try:
                    spin_thresh = int(parts[i + 1], 0)
                except Exception:
                    print("hunt: invalid spin_thresh")
                    return
                i += 2
            elif tok == "window" and i + 1 < len(parts):
                try:
                    window = int(parts[i + 1], 0)
                except Exception:
                    print("hunt: invalid window")
                    return
                if window < 16:
                    window = 16
                i += 2
            elif tok == "dot" and i + 1 < len(parts):
                want_dot = parts[i + 1].lower() == "on"
                i += 2
            elif tok == "disasm" and i + 1 < len(parts):
                want_disasm = parts[i + 1].lower() == "on"
                i += 2
            elif tok == "region" and i + 1 < len(parts):
                reg = parts[i + 1]
                if "+" not in reg:
                    print("hunt: region expects BASE+LEN or SYMBOL+LEN")
                    return
                base_tok, len_tok = reg.split("+", 1)
                try:
                    base = self.resolve(base_tok)
                    length = int(len_tok, 0)
                    if length <= 0:
                        print("hunt: region length must be > 0")
                        return
                    region = (base, base + length)
                except Exception as e:
                    print(f"hunt: invalid region: {e}")
                    return
                i += 2
            else:
                try:
                    _ = self.resolve(parts[i])
                    start_mode = parts[i]
                    i += 1
                except Exception:
                    print(f"hunt: unrecognized token '{parts[i]}'")
                    return

        try:
            regs0 = self.rsp.get_regs()
        except Exception as e:
            print(f"hunt: failed to read registers: {e}")
            return
        _ = self.dasm.update_mode(regs0)
        if start_mode == "current":
            start_eip = regs0["EIP"]
        else:
            try:
                start_eip = self.resolve(start_mode)
            except Exception as e:
                print(f"hunt: cannot resolve start '{start_mode}': {e}")
                return

        def in_region(addr: int) -> bool:
            if region is None:
                return True
            return region[0] <= addr < region[1]

        cfg = CFG()
        eip_window: deque = deque(maxlen=window)
        flag_window: deque = deque(maxlen=min(128, window))
        recent_edge_is_back: deque = deque(maxlen=window)
        visited_nodes: set = set()

        now = time.time()
        t_start = now
        steps = 0
        reason = ""
        reason_detail = ""
        prev_eip = start_eip
        if not in_region(prev_eip):
            print("hunt: start outside region; nothing to do.")
            return
        cfg.add_node(prev_eip, now)
        eip_window.append(prev_eip)
        flag_window.append(regs0.get("EFLAGS", 0))
        visited_nodes.add(prev_eip)

        def detect_small_cycle(seq: deque, max_period=4, min_reps=4):
            n = len(seq)
            if n < max_period * min_reps:
                return None
            arr = list(seq)
            for p in range(1, max_period + 1):
                ok = True
                for i in range(n - p):
                    if arr[i] != arr[i + p]:
                        ok = False
                        break
                if ok:
                    pattern = arr[-p:]
                    reps = n // p
                    if reps >= min_reps:
                        return pattern
            return None

        while True:
            now = time.time()
            if (now - t_start) * 1000.0 >= max_ms:
                reason = "max time"
                break
            if steps >= max_steps:
                reason = "max steps"
                break

            try:
                self.rsp.step()
                regs = self.rsp.get_regs()
            except Exception as e:
                reason = "RSP error"
                reason_detail = str(e)
                break

            _ = self.dasm.update_mode(regs)
            cur_eip = regs.get("EIP", 0)
            cur_eflags = regs.get("EFLAGS", 0)
            steps += 1

            if not in_region(cur_eip):
                cfg.add_edge(prev_eip, cur_eip, time.time())
                reason = "left region"
                break

            ts = time.time()
            cfg.add_edge(prev_eip, cur_eip, ts)
            eip_window.append(cur_eip)
            flag_window.append(cur_eflags)
            back = cur_eip in visited_nodes
            recent_edge_is_back.append(1 if back else 0)
            visited_nodes.add(cur_eip)

            if eip_window.count(cur_eip) >= spin_thresh:
                reason = "suspected tight spin"
                break

            cyc = detect_small_cycle(eip_window, max_period=4, min_reps=6)
            if cyc is not None:
                reason = "small cycle"
                reason_detail = f"pattern length {len(cyc)}"
                break

            if steps % 64 == 0:
                scc_set, has_out = extract_scc_containing(cfg, cur_eip, region)
                stayed = all(
                    e in scc_set for e in list(eip_window)[-max(1, window // 2) :]
                )
                if stayed and not has_out and len(scc_set) >= 1:
                    reason = "SCC no-exit"
                    break

            if len(recent_edge_is_back) >= 32:
                take = min(len(recent_edge_is_back), window, steps)
                last = list(recent_edge_is_back)[-take:]
                if sum(last) / float(take) >= 0.95:
                    reason = "back-edge dominance"
                    break

            if len(flag_window) >= min(128, window):
                flags_same = all(f == flag_window[0] for f in flag_window)
                few_ips = len(set(eip_window)) <= 4
                if flags_same and few_ips:
                    reason = "low state change"
                    break

            prev_eip = cur_eip

        try:
            regs_end = self.rsp.get_regs()
        except Exception:
            regs_end = {"EIP": prev_eip}
        t_end = time.time()
        cur_node = regs_end.get("EIP", prev_eip)

        print(
            f"{C.BOLD}hunt result:{C.RESET} {reason}"
            + (f" — {reason_detail}" if reason_detail else "")
        )
        if region:
            rtxt = f"[0x{region[0]:08x}..0x{region[1]-1:08x}]"
        else:
            rtxt = "(unconstrained)"
        unique_nodes = len(cfg.visits)
        unique_edges = sum(1 for _ in cfg.edges())
        print(
            f"  steps={steps}  nodes={unique_nodes}  edges={unique_edges}  "
            f"region={rtxt}  start={time.strftime('%H:%M:%S', time.localtime(t_start))}  "
            f"end={time.strftime('%H:%M:%S', time.localtime(t_end))}"
        )
        try:
            start_sym = self._format_symbol(start_eip)
            end_sym = self._format_symbol(cur_node)
        except Exception:
            start_sym = f"0x{start_eip:08x}"
            end_sym = f"0x{cur_node:08x}"
        print(f"  start @ {start_sym}")
        print(f"  end   @ {end_sym}")

        print(f"\n{C.BOLD}Top nodes by visits:{C.RESET}")
        for addr, cnt in cfg.top_nodes(10):
            print(f"  {cnt:8d}  {self._format_symbol(addr)}")

        print(f"\n{C.BOLD}Top edges by traversals:{C.RESET}")
        t_edges = cfg.top_edges(10)
        if not t_edges:
            print("  (none)")
        else:
            for u, v, c in t_edges:
                print(
                    f"  {c:8d}  {self._format_symbol(u)}  ->  {self._format_symbol(v)}"
                )

        scc_set, has_out = extract_scc_containing(cfg, cur_node, region)
        render_whole = unique_nodes <= 200
        target_nodes = set(cfg.nodes()) if render_whole else scc_set
        if not render_whole:
            print(
                f"\n{C.BOLD}Suspected SCC size:{C.RESET} {len(scc_set)}  (has_out={has_out})"
            )

        if want_dot:
            dot_nodes = target_nodes
            if len(dot_nodes) > 300:
                print("\nDOT graph skipped (too large >300 nodes).")
            else:
                print(f"\n{C.BOLD}DOT graph:{C.RESET}")
                print("```dot")
                print("digraph CFG {")
                print('  graph [rankdir=LR, bgcolor="white"];')
                print(
                    '  node [shape=box, style="rounded,filled", fillcolor="lightgray", fontname="monospace", fontsize=10];'
                )
                for a in sorted(dot_nodes):
                    mark = "bold" if a == cur_node else "solid"
                    label = self._format_symbol(a).replace('"', '\\"')
                    print(
                        f'  n{a:x} [label="{label}", penwidth=1.2, color="black", style="{mark},filled"];'
                    )
                edge_count_printed = 0
                edge_cap = 2000
                for u in sorted(dot_nodes):
                    for v, c in cfg.adj.get(u, {}).items():
                        if v in dot_nodes:
                            print(f'  n{u:x} -> n{v:x} [label="{c}", color="black"];')
                            edge_count_printed += 1
                            if edge_count_printed >= edge_cap:
                                print("  // (... truncated ...)")
                                u = None
                                break
                    if u is None:
                        break
                print("}")
                print("```")

        if want_disasm:
            print(f"\n{C.BOLD}Disassembly of suspected nodes:{C.RESET}")
            to_show = (
                list(sorted(scc_set))[:32]
                if not render_whole
                else list(sorted(target_nodes))[:32]
            )
            for a in to_show:
                print(f"{C.MAGENTA}{self._format_symbol(a)}:{C.RESET}")
                try:
                    self.print_disasm(3, a)
                except Exception as e:
                    print(f"  disasm error: {e}")

    def do_EOF(self, arg):
        print()
        return True


def main() -> int:
    parser = argparse.ArgumentParser(description="adbg_cli — simple assembly debugger")
    parser.add_argument("--host", default="127.0.0.1", help="RSP host")
    parser.add_argument("--port", type=int, default=1234, help="RSP port")
    parser.add_argument(
        "--fas-file",
        default="build/spark.fas",
        help=".fas symbolic info file; use comma to load multiple files",
    )
    parser.add_argument("--timeout", type=float, default=0.5, help="socket timeout (s)")
    parser.add_argument(
        "--reg-width",
        choices=["8", "16", "32"],
        default="32",
        help="default register view width for `regs`/`reg`",
    )
    parser.add_argument(
        "--color",
        choices=["auto", "always", "never"],
        default="auto",
        help="color output",
    )
    vq = parser.add_mutually_exclusive_group()
    vq.add_argument("--quiet", action="store_true", help="only warnings and errors")
    vq.add_argument("--verbose", action="store_true", help="debug logging")
    args = parser.parse_args()

    level = logging.INFO
    if args.quiet:
        level = logging.WARNING
    elif args.verbose:
        level = logging.DEBUG
    logging.getLogger().setLevel(level)
    for h in logging.getLogger().handlers:
        try:
            h.setLevel(level)
        except Exception:
            pass
    logger.setLevel(level)

    global C
    if args.color == "always":
        C = _Colors(True)
    elif args.color == "never":
        C = _Colors(False)
    else:
        C = _Colors(_color_enabled())

    paths = [p.strip() for p in args.fas_file.split(",") if p.strip()]
    if not paths:
        print("No .fas files specified")
        return 1

    merged_sym2addr: Dict[str, int] = {}
    merged_addr2sym: Dict[int, str] = {}
    fas_list: List[FasFile] = []
    loaded_any = False
    merged_conflicts: Dict[str, List[int]] = {}

    for p in paths:
        try:
            s2a, a2s, fas = parse_fas(p)
            loaded_any = True
            for name, addr in s2a.items():
                if name not in merged_sym2addr:
                    merged_sym2addr[name] = addr
                elif merged_sym2addr[name] != addr:
                    merged_conflicts.setdefault(name, []).append(addr)
                    logger.warning(
                        "Symbol '%s' address conflict: 0x%x vs 0x%x (keeping first)",
                        name,
                        merged_sym2addr[name],
                        addr,
                    )
            for addr, name in a2s.items():
                merged_addr2sym.setdefault(addr, name)
            fas_list.append(fas)
            logger.info(
                "Loaded FAS: %s (symbols: %d, lines: %d)",
                p,
                len(s2a),
                len(fas.addr2line),
            )
        except FileNotFoundError:
            logger.error(".fas file not found: %s", p)
        except Exception as e:
            logger.error("Failed to parse .fas (%s): %s", p, e)

    if not loaded_any:
        print("Failed to load any .fas files.")
        return 1

    fas_merged = MergedFas(fas_list)

    try:
        rsp = RSPClient(args.host, args.port, timeout=args.timeout)
    except Exception as e:
        print(f"Failed to connect to {args.host}:{args.port}: {e}")
        return 1

    dasm = Disassembler()
    cli = ADbgCLI(
        rsp,
        dasm,
        merged_sym2addr,
        merged_addr2sym,
        fas_merged,
        default_reg_width=int(args.reg_width),
    )
    cli._sym_conflicts = merged_conflicts

    signal.signal(signal.SIGINT, lambda s, f: cli.do_quit(None))
    cli.cmdloop()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
