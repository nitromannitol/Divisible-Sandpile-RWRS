# Contributing / Building notes

This repository is primarily a finished artifact rather than an actively
solicited collaborative project, but issues and pull requests are welcome.

## Building locally

```bash
lake exe cache get   # first time: the Mathlib cache
lake build RWRS      # the library
```

At this commit `lakefile.lean` reads the shared library Lattice-Probability
from the sibling directory `../Lattice-Probability-clean`, which must be a
checkout of commit `bbe0b90`.

The production build is required to emit no Lean or linter warnings
(`python3 tools/check_warnings.py`).  The three Mathlib-only files
`Audit/*/Challenge.lean` are the sole exception: each contains one documented
statement-level `sorry`, checked against its completed solution by
`leanprover/comparator`.

A few practical notes for working with this development:

- **Never run `lake clean`.**  It wipes the Mathlib oleans and forces a
  multi-hour rebuild from source.  To force a project-only rebuild, remove the
  project build artifacts under `.lake/build/lib/lean/RWRS` (and the
  corresponding `.lake/build/ir/RWRS`) and re-run `lake build RWRS`.

- **Per-file rebuilds.**  Lake invalidates by content hash, not mtime, so
  `touch` does nothing; delete the specific `.olean` under
  `.lake/build/lib/lean/` and rebuild the module.

- **Frozen statements.**  The text between `-- FROZEN-STATEMENT-BEGIN` and
  `-- FROZEN-STATEMENT-END` in `RWRS/Frozen/` and `RWRS/External/` is pinned
  by the SHA-256 recorded in `ledger/manifest.yaml`.  A change there must be
  registered with `python3 tools/freeze.py` and shows up in
  `python3 tools/check_manifest.py`; proofs after the end marker may be changed
  freely.

- **The main results** are in `RWRS/MainTheorems.lean`; the axiom audit is
  `lake build RWRS.Meta.AxiomsAudit`, and the comparator surface is
  `lake build Audit`.
