#!/usr/bin/env python3
"""Extract a small, reproducible NOAA GlobalTemp anomaly slice for tests.

The test resource format is deliberately plain text:

    # provenance comments
    latIdx lonIdx anomaly

Example:

    python3 tools/extract_noaa_slice.py \
      NOAAGlobalTemp_v6.1.0_gridded_s185001_e202605_c20260608T115341.nc \
      src/test/resources/noaa_slice.txt

The script expects an HDF5/NetCDF4 file readable by h5py. It picks the last
time step by default because the fixture tracks the current release slice.
"""

from __future__ import annotations

import argparse
import hashlib
from pathlib import Path


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--dataset", default="anom")
    parser.add_argument("--time-index", type=int, default=-1)
    args = parser.parse_args()

    try:
        import h5py
    except ImportError as exc:  # pragma: no cover - only exercised by operators.
        raise SystemExit("h5py is required: python3 -m pip install h5py") from exc

    with h5py.File(args.input, "r") as f:
        data = f[args.dataset]
        time_index = args.time_index if args.time_index >= 0 else data.shape[0] - 1
        arr = data[time_index]
        while arr.ndim > 2:
            arr = arr[0]
        fill = data.attrs.get("_FillValue")

    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open("w", encoding="utf-8") as out:
        out.write(
            f"# NOAAGlobalTemp slice from {args.input.name}; "
            f"sha256={sha256(args.input)}; dataset={args.dataset}; "
            f"time index {time_index}; anomaly[lat,lon] in degrees C.\n"
        )
        out.write("# Columns: latIdx(0-based) lonIdx(0-based) anomaly.\n")
        for lat in range(arr.shape[0]):
            for lon in range(arr.shape[1]):
                value = float(arr[lat, lon])
                if fill is not None and value == float(fill):
                    continue
                if value != value:
                    continue
                out.write(f"{lat} {lon} {value:.4f}\n")


if __name__ == "__main__":
    main()
