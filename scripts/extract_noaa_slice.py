#!/usr/bin/env python3
"""Reproducibly extract one NOAA gridded anomaly slice into the committed test fixture.

Source : NOAAGlobalTemp v6.1.0 gridded NetCDF4/HDF5 (variable `anom[time, z, lat, lon]`,
         missing/fill value -999.9, 36 lat x 72 lon, monthly from 1850-01).
Output : src/test/resources/noaa_slice.txt  ->  lines "latIdx lonIdx anomaly" (degrees C),
         skipping fill cells, with a two-line provenance header.

Usage  : python3 scripts/extract_noaa_slice.py [NetCDF path] [time index, default = last]
Deps   : h5py (the .nc is HDF5).  ncdump is NOT required.

The MORKL temperature example buckets `anomaly` into VC/C/N/W/VW at thresholds
[-1, -0.2, 0.2, 1] and indexes (latIdx, lonIdx) in a binary trie; see NOAA in
src/test/scala/Examples.scala.
"""
import sys, os, hashlib
import h5py  # type: ignore

DEFAULT_NC = "NOAAGlobalTemp_v6.1.0_gridded_s185001_e202605_c20260608T115341.nc"
FILL = -999.9

def main():
    nc = sys.argv[1] if len(sys.argv) > 1 else DEFAULT_NC
    with h5py.File(nc, "r") as f:
        anom = f["anom"]                       # (time, z, lat, lon)
        ti = int(sys.argv[2]) if len(sys.argv) > 2 else anom.shape[0] - 1
        grid = anom[ti, 0, :, :]               # (lat, lon)
    out_path = os.path.join("src", "test", "resources", "noaa_slice.txt")
    lines = [f"{i} {j} {float(grid[i, j]):.4f}"
             for i in range(grid.shape[0]) for j in range(grid.shape[1])
             if abs(float(grid[i, j]) - FILL) > 1e-3]
    body = "\n".join(lines) + "\n"
    header = (f"# NOAAGlobalTemp v6.1.0 gridded, time index {ti}; anom[lat,lon] in degrees C.\n"
              f"# Extracted via h5py from {os.path.basename(nc)}. Columns: latIdx(0..35) lonIdx(0..71) anomaly.\n")
    with open(out_path, "w") as o:
        o.write(header + body)
    digest = hashlib.sha256((header + body).encode()).hexdigest()
    print(f"wrote {len(lines)} cells to {out_path}")
    print(f"sha256={digest}")

if __name__ == "__main__":
    main()
