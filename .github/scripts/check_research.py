"""Check each requested source and record errors even if a sibling fails."""
import argparse
from graphlib import TopologicalSorter
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys


REPO = Path(__file__).resolve().parents[2]
SRC = REPO / "research"
FILES = {p.stem:p for p in SRC.glob("*.lean")}


def imports(path):
    return re.findall(r"^import\s+([\w.]+)",path.read_text(encoding="utf8"),re.MULTILINE)


def closure(roots):
    graph = {}
    def visit(name):
        if name in graph:
            return
        graph[name] = [m for m in imports(FILES[name]) if m in FILES]
        for dep in graph[name]:
            visit(dep)
    for name in roots:
        visit(name)
    return graph


def escape(text):
    return text.replace("%","%25").replace("\r","%0D").replace("\n","%0A")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("group")
    parser.add_argument("--fetch",action="store_true")
    args = parser.parse_args()
    graph = closure(json.loads((SRC/"groups.json").read_text())[args.group])
    if args.fetch:
        inputs = [*REPO.glob("*.lean"),*(FILES[n] for n in graph)]
        deps = sorted({m for p in inputs for m in imports(p) if m.startswith("Mathlib.")})
        subprocess.run(["lake","exe","cache","get",*deps],check=True)
        return
    out = REPO / ".lake/research"
    out.mkdir(parents=True,exist_ok=True)
    env = os.environ.copy()
    env["LEAN_PATH"] = str(out) + os.pathsep + env.get("LEAN_PATH","")
    failures = set()
    summary = []
    reports = []
    for name in TopologicalSorter(graph).static_order():
        blocked = failures.intersection(graph[name])
        if blocked:
            failures.add(name)
            summary.append(f"| {name} | Blocked by {', '.join(sorted(blocked))} |")
            continue
        p = FILES[name]
        sha = hashlib.sha256(p.read_bytes()).hexdigest()
        print(f"::group::{name} {sha}",flush=True)
        res = subprocess.run(["lean","-j1","--trust=0","-DwarningAsError=true",
                              "-o",str(out/(name+".olean")),str(p.relative_to(REPO))],
                             env=env,capture_output=True,text=True,errors="replace")
        output = res.stdout + res.stderr
        print(output,flush=True)
        print("::endgroup::",flush=True)
        if res.returncode:
            failures.add(name)
            # Annotate complete compiler diagnostics so a separate research
            # session can retrieve them via the public Checks API.
            errors = list(re.finditer(r"(?m)^.*?\.lean:(\d+):(\d+): (?:error|warning):?",output))
            diagnostics = []
            for i,m in enumerate(errors):
                end = errors[i+1].start() if i+1<len(errors) else len(output)
                diagnostics.append(output[m.start():end].split("\n'")[0][:6000])
            if not errors:
                diagnostics.append(output[:10000])
            reports.append((name, "\n".join(diagnostics)))
        summary.append(f"| {name} | {'Failed' if res.returncode else 'Checked'} |")
    result = "| Module | Lean 4.36.0 |\n|---|---|\n"+"\n".join(summary)+"\n"
    print(result)
    print(f"::notice title=Module status::{escape(result)}",flush=True)
    # GitHub limits the number of displayed annotations per step. Group the
    # diagnostics so early errors cannot hide every subsequent proof file.
    for i in range(0,len(reports),2):
        batch = reports[i:i+2]
        names = ", ".join(item[0] for item in batch)
        body = "\n\n".join(item[0]+"\n"+item[1][:22000] for item in batch)
        print(f"::error title={names}::{escape(body)}",flush=True)
    if os.getenv("GITHUB_STEP_SUMMARY"):
        with open(os.environ["GITHUB_STEP_SUMMARY"],"a") as f:
            f.write(result)
    if failures:
        sys.exit(1)


if __name__ == "__main__":
    main()
