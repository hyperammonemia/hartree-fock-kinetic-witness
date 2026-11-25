"""Fetch the mathlib cache for each external Lean import used by this project."""
from pathlib import Path
import subprocess

root = Path(__file__).resolve().parents[1]
modules = {
    line.split()[1]
    for directory in (root, root / "supplement", root / "continuum")
    for source in directory.glob("*.lean")
    for line in source.read_text(encoding="utf8").splitlines()
    if line.startswith("import Mathlib.")
}
subprocess.run(["lake", "exe", "cache", "get", *sorted(modules)], cwd=root, check=True)
