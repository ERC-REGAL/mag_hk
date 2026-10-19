#!/usr/bin/env python3
"""Run the pinned Lean directly against already installed Lake dependencies.

This avoids Lake trying to write metadata in a shared, read-only cache.
Run from this project directory, for example
    python3 lean_local.py MagHK/TimeReversal.lean
It does not download, update, or build any dependency.
"""

import json
import os
from pathlib import Path
import subprocess
import sys

project = Path(__file__).resolve().parent
os.chdir(project)
manifest = json.loads((project / "lake-manifest.json").read_text(encoding="utf-8"))
package_dir = project / manifest["packagesDir"]
search_paths = [project / ".lake/build/lib/lean", project]
for package in manifest["packages"]:
    path = package_dir / package["name"] / ".lake/build/lib/lean"
    if not path.is_dir() and package["name"] == "mathlib":
        sys.exit(f"Missing compiled dependency {path}. Install dependencies with Lake first.")
    if path.is_dir():
        search_paths.append(path.resolve())
environment = dict(os.environ)
environment["LEAN_PATH"] = os.pathsep.join(map(str, search_paths))
environment["ELAN_TOOLCHAIN"] = (project / "lean-toolchain").read_text(encoding="utf-8").strip()
lean = subprocess.check_output(
    ["elan", "which", "lean"], text=True, encoding="utf-8", env=environment).strip()
sys.exit(subprocess.run(
    [lean, "-DautoImplicit=false", "-DrelaxedAutoImplicit=false", *sys.argv[1:]],
    env=environment).returncode)
