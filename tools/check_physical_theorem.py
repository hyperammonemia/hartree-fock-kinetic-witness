"""Check a proposed proof against the fixed physical target and its axiom allowlist."""
import argparse
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
IDENTIFIER = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*")
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("module", help="Importable Lean module containing the proposed theorem")
    parser.add_argument("declaration", help="Fully qualified name of the claimed proof")
    args = parser.parse_args()
    if not all(IDENTIFIER.fullmatch(x) for x in (args.module, args.declaration)):
        parser.error("Expected Lean identifiers with optional namespace qualification")
    source = (
        f"import ContinuumHamiltonian\nimport {args.module}\n"
        f"theorem CheckedPhysicalReversal : ContinuumHamiltonian.FixedRadialReversal := "
        f"{args.declaration}\n#print axioms CheckedPhysicalReversal\n"
    )
    result = subprocess.run(
        ["lake", "env", "lean", "--trust=0", "-DwarningAsError=true", "--stdin"],
        input=source, capture_output=True, text=True, encoding="utf8", cwd=ROOT,
    )
    output = result.stdout + result.stderr
    print(output, end="")
    if result.returncode:
        return result.returncode
    match = re.search(
        r"'CheckedPhysicalReversal' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",
        output,
    )
    if not match:
        raise RuntimeError("Lean did not report the axioms of the new, explicitly typed proof")
    deps = {name.strip() for name in (match.group(1) or "").split(",") if name.strip()}
    if deps - ALLOWED:
        raise RuntimeError("Additional axioms: " + ", ".join(sorted(deps - ALLOWED)))
    print("The proposed declaration proves the fixed physical reversal.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
