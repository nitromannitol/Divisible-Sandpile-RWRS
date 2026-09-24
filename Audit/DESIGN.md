# Comparator design memo: vocabulary, bridges, deltas

This memo records how the three comparator pairs are built, for whoever checks
or extends them.  The files are `Audit/<Thm>/Challenge.lean`,
`Audit/<Thm>/Solution.lean`, `Audit/Support/Vocabulary.lean` (the
Mathlib-only copy of the vocabulary), `Audit/Support/Bridge.lean` (the
identifications), `Audit/Support/Statements.lean` and
`Audit/StatementRegression.lean` (the local statement check).

## 0. Solution architecture

The comparator checks that the solution theorem has the same elaborated type
as the challenge theorem, constant by constant through the whole dependency
closure.  So the vocabulary constants must elaborate in the solution exactly
as in the challenge.  As in the comparator pattern of the `CoarseGraining` and
`Superdiffusion` repositories, the vocabulary is therefore compiled in a module
that imports **only Mathlib** (`Audit/Support/Vocabulary.lean`, the analogue
of their per-challenge `SolutionBasic.lean`), and `Solution.lean` imports the
repository, that module, and the bridges, and states the theorem with the
challenge's bytes.

The three challenges share one vocabulary block, byte-identical in each
(`bash Audit/check_standalone.sh --vocabulary`), so one `Vocabulary.lean`
serves all three solutions.  The block contains a few definitions that a given
challenge does not use (for instance the toppling procedure in
`OptimalStopping`); they do not enter that theorem's dependency closure.

## 1. The vocabulary has no structures

Every declaration of the vocabulary is a definition over Mathlib types, a
token-for-token copy of the repository's.  There are no structures, so no new
inductive types, and no field-by-field transport is needed.

## 2. Identifications

`Audit/Support/Bridge.lean` proves, for every vocabulary constant, the equation
`@RWRSAudit.c = @RWRS.c`.

- The non-recursive definitions are identified by `rfl`; the kernel checks
  each by unfolding both sides.  This includes the classical decidability
  instance of the `if` in `External.VoltageFunction`, which both sides obtain
  from `open scoped Classical`.
- The three recursive definitions `heat`, `walkExp` and `walkPath` are
  compiled by structural recursion into auxiliary constants that differ
  between the two copies, and `rfl` does not see through them.  They are
  identified by induction on the time index (`heat_apply`, `walkExp_apply`,
  `walkPath_apply`).
- The definitions built on them (`green`, `stopValues`, `walkLaw`,
  `meanPayoff`, `supMeanPayoff`, `supStopValue`, `jointLaw`,
  `DoublyTransient`, `External.CarneVaropoulos`) are identified by unfolding
  and rewriting with the three inductions.

From these, `voltageFunction` and `carneVaropoulos` turn each cited-result
hypothesis of the vocabulary into the repository's.

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
repository name replaced by its vocabulary copy.  Relative to the frozen
statements in `RWRS/Frozen/`, `optimalStopping` and `stabilization` omit the
hypotheses `External.VonBahrEsseen`, `External.FukNagaevTail` and
`External.HeatKernelBoundedDegree G`, which `RWRS/MainTheorems.lean`
discharges with the repository's proofs; that is a strengthening, not a
weakening.  `explosion` is the frozen statement unchanged.

How each statement reads the paper is recorded in the frozen docstrings and
summarized in [`CORRESPONDENCE.md`](../CORRESPONDENCE.md).  The comparator does
not check that reading: it checks that the library proves exactly the
displayed statement, over definitions that can be read without the library.

## 5. What the comparator does not certify

- The cited results.  The challenges take them as hypotheses, restated in the
  vocabulary.  A proof conditional on a proposition does not show that the
  proposition is a faithful rendering of the cited theorem; that reading is
  the subject of `ASSUMPTIONS.md` and of `CORRESPONDENCE.md`.
- The faithfulness of the vocabulary to the paper.  The vocabulary is a copy
  of the repository's definitions, so the comparator shows that nothing in the
  statements depends on the library beyond what the vocabulary displays; a
  reader still has to check the vocabulary against the paper.

## 6. Uncertainties

- **U1.**  Resolved.  `leanprover/comparator` was run on all three pairs on
  2026-09-24 at commit `2cfdd84`, and each pair passed with the Lean kernel
  and with the independent nanoda kernel; see `Audit/COMPARATOR_RUNS.md`.
  Before that run, the local regression compared the solution types with
  the challenge-environment types up to the auxiliary proof lemmas that a
  `def` abstracts, a weaker check than the comparator's own closure check.
- **U2.**  The repository and its shared library Lattice-Probability both
  enter the solutions' import closure.  `Audit/StatementRegression.lean`
  checks that no solution statement names a constant of the namespace `RWRS`
  or of the library namespace `LatticeProb`.
