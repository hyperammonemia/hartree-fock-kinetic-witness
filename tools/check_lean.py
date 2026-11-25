"""Build every local module with Lake and inspect the recorded declarations."""

import argparse
import hashlib
import json
import re
import subprocess
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
MODULES = (
    "RadialCertificate",
    "ContinuumForms",
    "FinitePotential",
    "KineticAmplification",
    "FiniteOscillatoryWindow",
)
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def run(command, log, source=None):
    text = " ".join(command)
    print("$ " + text, flush=True)
    log.append("$ " + text)
    result = subprocess.run(
        command, cwd=ROOT, input=source, capture_output=True, encoding="utf8", errors="replace",
    )
    output = (result.stdout + result.stderr).strip()
    if output:
        print(output, flush=True)
        log.append(output)
    result.check_returncode()
    return output


def declarations(module):
    lines = (ROOT / (module + ".lean")).read_text(encoding="utf8").splitlines()
    namespace = next(line.split()[1] for line in lines if line.startswith("namespace "))
    names = [line.split()[2] for line in lines if line.startswith("#print axioms ")]
    if not names:
        raise RuntimeError("No recorded declarations in " + module)
    return [name if "." in name else namespace + "." + name for name in names]


def instructions_and_axioms(log):
    names = [name for module in MODULES for name in declarations(module)]
    source = "import HFNotes\n" + "".join("#print axioms " + name + "\n" for name in names)
    output = run(["lake", "env", "lean", "--trust=0", "--stdin"], log, source)
    for name in names:
        pattern = re.escape("'" + name + "'") + r"\s+(?:depends on axioms:\s*\[([^]]*)\]|does not depend on any axioms)"
        match = re.search(pattern, output)
        if match is None:
            raise RuntimeError("No axiom report for " + name)
        axioms = {field.strip() for field in (match.group(1) or "").split(",") if field.strip()}
        if axioms - STANDARD_AXIOMS:
            raise RuntimeError("Unexpected axiom in " + name + ": " + ", ".join(sorted(axioms)))
    message = f"Inspected {len(names)} declarations. All axioms belong to the standard set."
    print(message, flush=True)
    log.append(message)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="Write the completed verification transcript here.")
    args = parser.parse_args()
    log = []
    run(["lake", "--version"], log)
    run(["lake", "env", "lean", "--version"], log)
    manifest = json.loads((ROOT / "lake-manifest.json").read_text(encoding="utf8"))
    pin = next(package["rev"] for package in manifest["packages"] if package["name"] == "mathlib")
    if run(["git", "-C", ".lake/packages/mathlib", "rev-parse", "HEAD"], log) != pin:
        raise RuntimeError("The mathlib checkout differs from the manifest revision")
    print("SHA-256 of checked source inputs", flush=True)
    log.append("SHA-256 of checked source inputs")
    files = [name + ".lean" for name in (*MODULES, "HFNotes")]
    for filename in [*files, "lean-toolchain", "lakefile.toml", "lake-manifest.json"]:
        entry = hashlib.sha256((ROOT / filename).read_bytes()).hexdigest() + "  " + filename
        print(entry, flush=True)
        log.append(entry)
    for module in (*MODULES, "HFNotes"):
        run(["lake", "build", "+" + module], log)
    run(["lake", "build"], log)
    instructions_and_axioms(log)
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text("\n".join(log) + "\n", encoding="utf8")


if __name__ == "__main__":
    main()
