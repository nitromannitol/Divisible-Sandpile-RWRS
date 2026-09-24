#!/usr/bin/env python3
"""Axiom-closure gate for the registered declarations and their corollaries.

`check_manifest.py` checks the registered proof placeholders. This gate asks
Lean for the transitive axiom closure of each declaration, including every
imported proof used by that declaration.

A node may be SEALED only if `#print axioms` on its export shows no `sorryAx`.
This runs Lean and is the authority; the token count is only a fast prefilter.

Usage: check_axioms.py [--emit]   (--emit rewrites `state:` in the manifest)
"""
import io, os, re, subprocess, sys, tempfile, pathlib

from sync_docs import unconditional_names

ROOT = pathlib.Path(__file__).resolve().parent.parent
CLASSICAL = {"propext", "Classical.choice", "Quot.sound"}
man = io.open(ROOT / "ledger/manifest.yaml", encoding="utf-8").read()
nodes = []
for b in man.split("  - id: ")[1:]:
    nodes.append((b.split("\n")[0].strip(),
                  re.search(r"file: (\S+)", b).group(1),
                  re.search(r"export: (\S+)", b).group(1)))

nodes.extend((name, "RWRS/Support/Unconditional.lean", name)
             for name in unconditional_names())

mods = sorted({f[:-5].replace("/", ".") for _, f, _ in nodes})
src = "".join(f"import {m}\n" for m in mods) + \
      "".join(f"#print axioms {e}\n" for _, _, e in nodes)
# The probe has to live inside the package for `lake env lean` to resolve
# its imports.  A fresh clone has no `scratch/`, so make it.
(ROOT / "scratch").mkdir(exist_ok=True)
with tempfile.NamedTemporaryFile("w", suffix=".lean", dir=ROOT / "scratch",
                                 delete=False) as fh:
    fh.write(src); tmp = fh.name
try:
    r = subprocess.run(["lake", "env", "lean", tmp], cwd=ROOT, capture_output=True,
                       text=True, timeout=3600,
                       env={**os.environ,
                            "PATH": os.path.expanduser("~/.elan/bin") + ":" + os.environ["PATH"]})
finally:
    os.unlink(tmp)

if r.returncode != 0:
    print("check_axioms: Lean probe did not elaborate")
    print(r.stdout + r.stderr)
    sys.exit(1)

axioms = {m.group(1): m.group(2) or "" for m in re.finditer(
    r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", r.stdout)}
clean, dirty, missing, unexpected = [], [], [], []
for nid, _, exp in nodes:
    ax = axioms.get(exp)
    if ax is None:
        missing.append(nid)
    elif "sorryAx" in ax:
        dirty.append(nid)
    elif {a.strip() for a in ax.split(",") if a.strip()} - CLASSICAL:
        unexpected.append(nid)
    else:
        clean.append(nid)

for nid in clean:   print("  clean   %s" % nid)
for nid in dirty:   print("  sorryAx %s   <- NOT proved, however few `sorry`s its file has" % nid)
for nid in missing: print("  ??      %s   (no axiom line; did it elaborate?)" % nid)

for nid in unexpected: print("  extra   %s   (axiom closure exceeds Lean's classical axioms)" % nid)

if missing:
    print("check_axioms: missing axiom closures; manifest states are unchanged")
    sys.exit(1)

if "--emit" in sys.argv:
    out, head = [], man.split("  - id: ")[0]
    for b in man.split("  - id: ")[1:]:
        nid = b.split("\n")[0].strip()
        f = re.search(r"file: (\S+)", b).group(1)
        own = re.search(r"\bsorry\b", io.open(ROOT / f, encoding="utf-8").read())
        # SEALED: axiom-clean.  CONDITIONAL: a proof is written, but it leans on a
        # node that is still a draft, so `sorryAx` is in its closure.  DRAFT_SORRY:
        # no proof yet.
        kind = re.search(r"kind: (\S+)", b).group(1)
        if kind == "definition":
            # a frozen definition (an external input) has no proof to seal
            out.append(b); continue
        st = "SEALED" if nid in clean else ("DRAFT_SORRY" if own else "CONDITIONAL")
        out.append(re.sub(r"state: \w+", "state: " + st, b))
    io.open(ROOT / "ledger/manifest.yaml", "w", encoding="utf-8").write(
        head + "".join("  - id: " + b for b in out))
    print("\nmanifest states rewritten from the axiom closure")

print("\n%d clean, %d depend on sorryAx, %d unresolved" % (len(clean), len(dirty), len(missing)))
sys.exit(1 if (dirty or unexpected) and "--emit" not in sys.argv else 0)
