# Comparator design memo: vocabulary, bridges, deltas

This memo records how the three comparator pairs are built, for whoever checks
or extends them.  Each theorem has a directory `RWRSAudit/<Thm>/` with the same
four files:

- `Challenge.lean` imports `Mathlib` and nothing else.  It rebuilds from Mathlib
  primitives every object the theorem mentions (the vocabulary block between
  `VOCABULARY-BEGIN` and `VOCABULARY-END`), states the theorem, and ends in a
  single `sorry`.  This file is the object of trust: a reader checks what it
  says, not how it is proved.
- `SolutionBasic.lean` is a verbatim, mechanical copy of the vocabulary block of
  `Challenge.lean`.  It imports only `Mathlib`, so the vocabulary elaborates in
  the solution exactly as in the challenge.
- `Solution.lean` imports the library together with its `SolutionBasic` and its
  bridge, restates the challenge theorem byte for byte, and proves it from the
  library's verified statement.
- `comparator.json` names the challenge module, the solution module, the theorem
  and the permitted axioms (`propext`, `Classical.choice`, `Quot.sound`), and
  enables the independent nanoda kernel.

The bridge of each pair is `RWRSAudit/Support/<Thm>Bridge.lean`; it belongs to
the solution of that pair and is imported by its `Solution.lean` only.
`check_standalone.sh` elaborates a challenge on its own with the library's
build options, and with `--vocabulary` checks that the vocabulary block of each
`Challenge.lean` is byte-identical to the one in its `SolutionBasic.lean`.

## 0. Solution architecture

The comparator checks that the solution theorem has the same elaborated type
as the challenge theorem, constant by constant through the whole dependency
closure.  So the vocabulary constants must elaborate in the solution exactly
as in the challenge.  As in the comparator pattern of the `CoarseGraining`,
`Superdiffusion` and `CERW` repositories, the vocabulary is therefore compiled
in a module that imports **only Mathlib** (`RWRSAudit/<Thm>/SolutionBasic.lean`),
and `Solution.lean` imports the repository, that module, and the pair's bridge,
and states the theorem with the challenge's bytes.  Nothing a solution imports
can change the statement the reader saw in the challenge; it can only supply a
kernel-checked proof of it.

The three challenges share one vocabulary block, byte-identical in each, so the
three `SolutionBasic.lean` files are copies of the same text.  The block
contains a few definitions that a given challenge does not use (for instance the
toppling procedure in `OptimalStopping`); they do not enter that theorem's
dependency closure.

## 1. The vocabulary has no structures

Every declaration of the vocabulary is a definition over Mathlib types, a
token-for-token copy of the repository's.  There are no structures, so no new
inductive types, and no field-by-field transport is needed.

## 2. Identifications

Each bridge `RWRSAudit/Support/<Thm>Bridge.lean` proves, for every vocabulary
constant in the dependency closure of its pair's theorem, the equation
`@RWRSAudit.c = @RWRS.c`.

- The non-recursive definitions are identified by `rfl`; the kernel checks
  each by unfolding both sides.  This is all that `ExplosionBridge.lean` and
  `StabilizationBridge.lean` contain.
- The three recursive definitions `heat`, `walkExp` and `walkPath` are
  compiled by structural recursion into auxiliary constants that differ
  between the two copies, and `rfl` does not see through them.  They are
  identified by induction on the time index (`heat_apply`, `walkExp_apply`,
  `walkPath_apply`) in `OptimalStoppingBridge.lean`.
- The definitions built on them (`green`, `stopValues`, `walkLaw`,
  `meanPayoff`, `supMeanPayoff`, `supStopValue`, `jointLaw`,
  `DoublyTransient`) are identified in `OptimalStoppingBridge.lean` by
  unfolding and rewriting with the three inductions.

The one cited-result proposition kept in the vocabulary only for provenance,
`External.CarneVaropoulos`, is in the dependency closure of none of the three
statements, so no bridge identifies it.  The voltage-function proposition is
proved outright and discharged inside the library proofs, and it is not part of
the vocabulary.

## 3. Theorem-level bridges

`OptimalStopping/Solution.lean` rewrites its goal with `supMeanPayoff_eq`,
`supStopValue_eq`, `doublyTransient_eq` and `jointLaw_eq`, then closes it with
`exact RWRS.optimalStopping` applied to the transported hypothesis.  In
`Explosion` and `Stabilization` every constant of the statement is
non-recursive, so the goal is closed by `exact` directly, the remaining
identifications being definitional.

## 4. Presentation deltas

None at the level of the displayed statements: each challenge theorem is the
statement of the corresponding theorem of `RWRS/MainTheorems.lean` with every
repository name replaced by its vocabulary copy.  `RWRS/MainTheorems.lean`
states the same theorem as its `RWRS/Frozen/` counterpart in every case: the
cited inputs `External.VonBahrEsseen`, `External.FukNagaevTail` and
`External.HeatKernelBoundedDegree G` that the paper's proof of `optimalStopping`
and `stabilization` quotes are proved outright in `RWRS/External/` and so are
not hypotheses of the frozen statements themselves.  `explosion` is the frozen
statement itself.

How each statement reads the paper is recorded in the frozen docstrings and
summarized in [`CORRESPONDENCE.md`](../CORRESPONDENCE.md).  The comparator does
not check that reading: it checks that the library proves exactly the
displayed statement, over definitions that can be read without the library.

## 5. What the comparator does not certify

- The cited results.  No challenge carries one as a hypothesis: the voltage
  function that the proofs of `OptimalStopping` and `Explosion` need is proved
  on every infinite connected graph and discharged inside the proofs, and the
  pointwise Carne–Varopoulos bound is proved outright and kept in the
  vocabulary only for provenance.  Whether each proved proposition is a
  faithful rendering of the cited theorem is the subject of `ASSUMPTIONS.md`
  and of `CORRESPONDENCE.md`.
- The faithfulness of the vocabulary to the paper.  The vocabulary is a copy
  of the repository's definitions, so the comparator shows that nothing in the
  statements depends on the library beyond what the vocabulary displays; a
  reader still has to check the vocabulary against the paper.

## 6. Notes on the check

- **Statement identity.**  The comparator itself checks, for each pair, that
  the solution theorem has the same statement as the challenge theorem and the
  same dependency closure down to Mathlib, and that the closure uses only the
  permitted axioms.  There is no separate local regression: the three
  `SolutionBasic.lean` files declare the same names in the same namespace, so
  no module can import two of them together, and the comparator's per-pair
  check is the statement check.
- **Kernels.**  `leanprover/comparator` passes on all three pairs, with the Lean
  kernel and with the independent nanoda kernel (`"enable_nanoda": true` in
  every `comparator.json`); see `RWRSAudit/COMPARATOR_RUNS.md`.
- **Import closure.**  `Challenge.lean` and `SolutionBasic.lean` import Mathlib
  alone.  The repository and its shared library Lattice-Probability enter only
  through the import closure of `Solution.lean`, and no statement mentions a
  constant of either.
