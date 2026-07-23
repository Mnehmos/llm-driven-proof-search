"""Recover live CPython BS(84,83) sign lists from a same-user process.

The target process retains four Python lists of the singleton integers -1/+1.
We locate PyListObject headers in committed private memory, reconstruct lists
with the required row sums, and accept only an exact independently recomputed
energy match.
"""

from __future__ import annotations

import argparse
import bisect
import ctypes
import itertools
import json
import struct
from ctypes import wintypes
from pathlib import Path

from recover_bs_json_from_process import (
    MEM_COMMIT, PAGE_GUARD, PAGE_NOACCESS, PROCESS_QUERY_INFORMATION,
    PROCESS_VM_READ, MemoryBasicInformation, residual,
)


MEM_PRIVATE = 0x20000
TARGET_ROWS = (10, 8, -1, -13)
TARGET_LENGTHS = (84, 84, 83, 83)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("pid", type=int)
    parser.add_argument("--energy", type=int, default=576)
    parser.add_argument("--output", type=Path, default=Path("agent_bsd_recovered_576.json"))
    args = parser.parse_args()

    kernel32 = ctypes.WinDLL("kernel32", use_last_error=True)
    kernel32.OpenProcess.argtypes = [wintypes.DWORD, wintypes.BOOL, wintypes.DWORD]
    kernel32.OpenProcess.restype = wintypes.HANDLE
    kernel32.VirtualQueryEx.argtypes = [wintypes.HANDLE, ctypes.c_void_p,
        ctypes.POINTER(MemoryBasicInformation), ctypes.c_size_t]
    kernel32.VirtualQueryEx.restype = ctypes.c_size_t
    kernel32.ReadProcessMemory.argtypes = [wintypes.HANDLE, ctypes.c_void_p,
        ctypes.c_void_p, ctypes.c_size_t, ctypes.POINTER(ctypes.c_size_t)]
    kernel32.ReadProcessMemory.restype = wintypes.BOOL
    kernel32.CloseHandle.argtypes = [wintypes.HANDLE]
    handle = kernel32.OpenProcess(PROCESS_QUERY_INFORMATION | PROCESS_VM_READ,
                                  False, args.pid)
    if not handle:
        raise ctypes.WinError(ctypes.get_last_error())

    chunks: list[tuple[int, bytes]] = []
    address = 0
    try:
        while True:
            mbi = MemoryBasicInformation()
            if not kernel32.VirtualQueryEx(handle, ctypes.c_void_p(address),
                    ctypes.byref(mbi), ctypes.sizeof(mbi)):
                break
            base = int(mbi.BaseAddress or 0); size = int(mbi.RegionSize)
            if size <= 0:
                break
            if (mbi.State == MEM_COMMIT and mbi.Type == MEM_PRIVATE
                    and not (mbi.Protect & (PAGE_GUARD | PAGE_NOACCESS))):
                for offset in range(0, size, 1 << 20):
                    take = min(1 << 20, size - offset)
                    buffer = ctypes.create_string_buffer(take)
                    count = ctypes.c_size_t()
                    if kernel32.ReadProcessMemory(handle,
                            ctypes.c_void_p(base + offset), buffer, take,
                            ctypes.byref(count)) and count.value:
                        chunks.append((base + offset, buffer.raw[:count.value]))
            address = base + size
    finally:
        kernel32.CloseHandle(handle)

    chunks.sort()
    bases = [base for base, _ in chunks]

    def read_at(pointer: int, size: int) -> bytes | None:
        index = bisect.bisect_right(bases, pointer) - 1
        if index < 0:
            return None
        base, data = chunks[index]
        offset = pointer - base
        if offset < 0 or offset + size > len(data):
            return None
        return data[offset:offset + size]

    candidates: dict[tuple[int, int, int], list[list[int]]] = {}
    headers = 0
    for base, data in chunks:
        for length in (83, 84):
            needle = struct.pack("<Q", length)
            start = 0
            while True:
                hit = data.find(needle, start)
                if hit < 0:
                    break
                object_offset = hit - 16
                start = hit + 1
                if object_offset < 0 or object_offset + 40 > len(data):
                    continue
                if (base + object_offset) % 8:
                    continue
                refcnt, type_ptr, size_value, item_ptr, allocated = struct.unpack_from(
                    "<QQqQQ", data, object_offset
                )
                if size_value != length or allocated < length or allocated > length + 16:
                    continue
                raw_items = read_at(item_ptr, length * 8)
                if raw_items is None:
                    continue
                pointers = list(struct.unpack(f"<{length}Q", raw_items))
                unique = set(pointers)
                if len(unique) != 2 or 0 in unique:
                    continue
                headers += 1
                first, second = tuple(unique)
                for negative, positive in ((first, second), (second, first)):
                    sequence = [-1 if pointer == negative else 1 for pointer in pointers]
                    row = sum(sequence)
                    for index, (wanted_length, wanted_row) in enumerate(
                            zip(TARGET_LENGTHS, TARGET_ROWS)):
                        if length == wanted_length and row == wanted_row:
                            key = (negative, positive, index)
                            if sequence not in candidates.setdefault(key, []):
                                candidates[key].append(sequence)

    pointer_pairs = {(negative, positive) for negative, positive, _ in candidates}
    combinations = 0
    for negative, positive in pointer_pairs:
        groups = [candidates.get((negative, positive, index), []) for index in range(4)]
        if any(not group for group in groups):
            continue
        for sequences in itertools.product(*groups):
            combinations += 1
            rr = residual(list(sequences))
            energy = sum(value * value for value in rr)
            if energy == args.energy:
                result = {
                    "construction": "base sequences BS(84,83)",
                    "recovery": {"source_pid": args.pid, "method": "CPython PyList scan"},
                    "solved": not any(rr),
                    "energy": energy,
                    "l1": sum(map(abs, rr)),
                    "row_sums": list(map(sum, sequences)),
                    "residual": rr,
                    "sequences": sequences,
                }
                args.output.write_text(json.dumps(result, indent=2) + "\n",
                                       encoding="utf-8")
                print(json.dumps({"recovered": str(args.output), "headers": headers,
                                  "combinations": combinations}))
                return 0
    print(json.dumps({"recovered": None, "headers": headers,
                      "candidate_groups": len(candidates),
                      "combinations": combinations,
                      "private_bytes": sum(len(data) for _, data in chunks)}))
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
