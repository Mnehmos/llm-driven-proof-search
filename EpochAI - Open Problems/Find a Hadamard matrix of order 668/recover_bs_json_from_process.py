"""Read-only recovery of a recently loaded BS JSON string from a local process.

This is used only to recover a mathematical checkpoint after a shared filename
was accidentally overwritten while an exact solver still retains the input in
memory.  It scans committed readable memory for JSON objects and validates any
BS(84,83) sequence arrays by exact integer autocorrelation.
"""

from __future__ import annotations

import argparse
import ctypes
import json
from ctypes import wintypes
from pathlib import Path


PROCESS_QUERY_INFORMATION = 0x0400
PROCESS_VM_READ = 0x0010
MEM_COMMIT = 0x1000
PAGE_GUARD = 0x100
PAGE_NOACCESS = 0x01


class MemoryBasicInformation(ctypes.Structure):
    _fields_ = [
        ("BaseAddress", ctypes.c_void_p),
        ("AllocationBase", ctypes.c_void_p),
        ("AllocationProtect", wintypes.DWORD),
        ("PartitionId", wintypes.WORD),
        ("RegionSize", ctypes.c_size_t),
        ("State", wintypes.DWORD),
        ("Protect", wintypes.DWORD),
        ("Type", wintypes.DWORD),
    ]


def residual(sequences: list[list[int]]) -> list[int]:
    return [
        sum(
            sum(seq[i] * seq[i + d] for i in range(len(seq) - d))
            for seq in sequences
        )
        for d in range(1, 84)
    ]


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("pid", type=int)
    parser.add_argument("--energy", type=int, default=576)
    parser.add_argument("--output", type=Path, default=Path("agent_bsd_recovered_576.json"))
    args = parser.parse_args()

    kernel32 = ctypes.WinDLL("kernel32", use_last_error=True)
    kernel32.OpenProcess.argtypes = [wintypes.DWORD, wintypes.BOOL, wintypes.DWORD]
    kernel32.OpenProcess.restype = wintypes.HANDLE
    kernel32.VirtualQueryEx.argtypes = [
        wintypes.HANDLE, ctypes.c_void_p,
        ctypes.POINTER(MemoryBasicInformation), ctypes.c_size_t,
    ]
    kernel32.VirtualQueryEx.restype = ctypes.c_size_t
    kernel32.ReadProcessMemory.argtypes = [
        wintypes.HANDLE, ctypes.c_void_p, ctypes.c_void_p,
        ctypes.c_size_t, ctypes.POINTER(ctypes.c_size_t),
    ]
    kernel32.ReadProcessMemory.restype = wintypes.BOOL
    kernel32.CloseHandle.argtypes = [wintypes.HANDLE]

    handle = kernel32.OpenProcess(
        PROCESS_QUERY_INFORMATION | PROCESS_VM_READ, False, args.pid
    )
    if not handle:
        raise ctypes.WinError(ctypes.get_last_error())

    seen: set[bytes] = set()
    scanned = 0
    address = 0
    marker = b'"sequences"'
    try:
        while True:
            mbi = MemoryBasicInformation()
            got = kernel32.VirtualQueryEx(
                handle, ctypes.c_void_p(address), ctypes.byref(mbi), ctypes.sizeof(mbi)
            )
            if not got:
                break
            base = int(mbi.BaseAddress or 0)
            size = int(mbi.RegionSize)
            if size <= 0:
                break
            if (mbi.State == MEM_COMMIT and not (mbi.Protect & PAGE_GUARD)
                    and not (mbi.Protect & PAGE_NOACCESS)):
                offset = 0
                overlap = b""
                while offset < size:
                    take = min(1 << 20, size - offset)
                    buffer = ctypes.create_string_buffer(take)
                    count = ctypes.c_size_t()
                    ok = kernel32.ReadProcessMemory(
                        handle, ctypes.c_void_p(base + offset), buffer, take,
                        ctypes.byref(count),
                    )
                    if ok and count.value:
                        data = overlap + buffer.raw[:count.value]
                        scanned += count.value
                        start = 0
                        while True:
                            hit = data.find(marker, start)
                            if hit < 0:
                                break
                            left = data.rfind(b"{", max(0, hit - 2048), hit)
                            # Generated checkpoint JSON is under 8 KiB.
                            right = data.find(b"}\n", hit, min(len(data), hit + 8192))
                            if right < 0:
                                right = data.find(b"}", hit, min(len(data), hit + 8192))
                            if left >= 0 and right >= 0:
                                raw = data[left:right + 1]
                                if raw not in seen:
                                    seen.add(raw)
                                    try:
                                        obj = json.loads(raw.decode("utf-8"))
                                        seq = obj.get("sequences")
                                        if tuple(map(len, seq or [])) == (84, 84, 83, 83):
                                            rr = residual(seq)
                                            energy = sum(x * x for x in rr)
                                            print(json.dumps({
                                                "found_energy": energy,
                                                "l1": sum(map(abs, rr)),
                                                "rows": list(map(sum, seq)),
                                            }), flush=True)
                                            if energy == args.energy:
                                                recovered = dict(obj)
                                                recovered["recovery"] = {
                                                    "source_pid": args.pid,
                                                    "independently_recomputed": True,
                                                }
                                                recovered["energy"] = energy
                                                recovered["residual"] = rr
                                                args.output.write_text(
                                                    json.dumps(recovered, indent=2) + "\n",
                                                    encoding="utf-8",
                                                )
                                                print(json.dumps({
                                                    "recovered": str(args.output),
                                                    "scanned_bytes": scanned,
                                                }))
                                                return 0
                                    except (UnicodeDecodeError, json.JSONDecodeError,
                                            TypeError, ValueError):
                                        pass
                            start = hit + len(marker)
                        overlap = data[-16384:]
                    else:
                        overlap = b""
                    offset += take
            address = base + size
    finally:
        kernel32.CloseHandle(handle)
    print(json.dumps({"recovered": None, "scanned_bytes": scanned,
                      "json_fragments": len(seen)}))
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
