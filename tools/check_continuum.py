"""Build the continuum library and audit the declarations listed by its modules."""
import argparse
import hashlib
import re
from pathlib import Path

from check_lean import ROOT, STANDARD_AXIOMS, run


EXTRA = {
    "CoulombCentering": ["CoulombCentering.row_zero", "CoulombCentering.spin_singlet_single",
                         "CoulombCentering.multiplication_form_floor"],
    "SlaterGeometry": ["SlaterGeometry.inner_slater", "SlaterGeometry.slater_unit",
                       "SlaterGeometry.double_excitation_bound"],
    "ExteriorTail": ["HFExterior.exists_trace", "HFExterior.explicit_barrier_tail",
                     "HFExterior.marginal_tail_of_weak_difference"],
    "RadialBarrier": ["HFExterior.oscillator_barrier", "HFExterior.exterior_supersolution"],
    "WeakRadial": ["HFExterior.ExteriorProfile.positivePart", "HFExterior.weak_radial_maximum"],
}


def selected_names(path):
    namespace = []
    result = []
    for line in path.read_text(encoding="utf8").splitlines():
        words = line.strip().split()
        if words[:1] == ["namespace"]:
            namespace.append(words[1])
        if words[:1] == ["end"] and len(words) == 2 and namespace and namespace[-1] == words[1]:
            namespace.pop()
        if words[:2] == ["#print", "axioms"]:
            name = words[2]
            if namespace and not name.startswith(".".join(namespace) + "."):
                name = ".".join([*namespace, name])
            result.append(name)
    return list(dict.fromkeys([*result, *EXTRA.get(path.stem, [])]))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    log = []
    run(["lake", "build", "ContinuumResults"], log)
    paths = sorted((ROOT / "continuum").glob("*.lean"))
    names = list(dict.fromkeys(name for path in paths for name in selected_names(path)))
    if not names:
        raise RuntimeError("No continuum declarations were found")
    for path in paths:
        log.append(hashlib.sha256(path.read_bytes()).hexdigest() + "  " + path.relative_to(ROOT).as_posix())
    source = "import ContinuumResults\n" + "".join("#print axioms " + name + "\n" for name in names)
    output = run(["lake", "env", "lean", "-j1", "--trust=0", "-DwarningAsError=true", "--stdin"], log, source)
    for name in names:
        pattern = rf"'{re.escape(name)}'\s+(?:depends on axioms:\s*\[([^]]*)\]|does not depend on any axioms)"
        match = re.search(pattern, output)
        if not match:
            raise RuntimeError("Missing axiom report for " + name)
        used = {s.strip() for s in (match.group(1) or "").split(",") if s.strip()}
        if used - STANDARD_AXIOMS:
            raise RuntimeError(f"{name} uses additional axioms: {sorted(used - STANDARD_AXIOMS)}")
    summary = f"Checked {len(names)} declarations against the standard axiom allowlist."
    print(summary)
    log.append(summary)
    if args.output:
        args.output.write_text("\n".join(log) + "\n", encoding="utf8")


if __name__ == "__main__":
    main()
