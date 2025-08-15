# adbg_cli

`adbg_cli` is a simple assembly debugger frontend that talks to a GDB Remote Serial Protocol (RSP) stub and integrates with [FASM](https://flatassembler.net/) [`.fas`](https://fossies.org/linux/fasm/tools/fas.txt) files for symbolic and source-level debugging.

It is designed for low-level debugging of real-mode and protected-mode x86 code, making it suitable for OS/kernel developers, emulator developers, or anyone working close to the metal.

---

## Features

- **Interactive CLI**.
- **Disassembly** using [Capstone](http://www.capstone-engine.org/).
- **Registers view** (`regs`, `reg`) with selectable width; 8/16/32-bit.
- **Breakpoints** (`break`, `delete`) and **watchpoints** (`watch`, `unwatch`).
- **Stack view** (`stack`) with live memory reads.
- **Memory inspection** (`peek`, `peekf`) and modification (`poke`, `pokeb`, `pokew`, `pokel`, `pokeq`, `pokef`).
- **Symbol/line awareness** via `.fas` files (`symbols`, `info lines`).
- **Source mapping** (addr -> filename:line) from FASM symbolic info.
- **Lightweight**: pure Python, minimal dependencies.
