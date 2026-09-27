# Audit Comparator Surface

This directory contains Mathlib-only comparator challenges for the three main
theorems of the formalization of *Divisible sandpiles via random walks in
random scenery* (Bou-Rabee, Peres and Sava-Huss, arXiv:2604.13968): Theorem 1.1
on random walk in random scenery, and Theorems 1.2 and 1.3 on explosion and
stabilization of the divisible sandpile.  Each comparator lives in its own
subdirectory:

| Directory | Paper statement | Checked theorem | Library theorem |
| --- | --- | --- | --- |
| `OptimalStopping/` | Theorem 1.1, `thm:OS` | `RWRSAudit.optimalStopping` | `RWRS.optimalStopping` |
| `Explosion/` | Theorem 1.2, `thm:explosion` | `RWRSAudit.explosion` | `RWRS.explosion` |
| `Stabilization/` | Theorem 1.3, `thm:stab` | `RWRSAudit.stabilization` | `RWRS.stabilization` |

Each `Challenge.lean` imports only `Mathlib`, rebuilds from scratch every
definition needed to read the theorem, states the theorem, and ends with one
`sorry`, the proof being checked.  The definitions form one vocabulary block,
between `-- VOCABULARY-BEGIN` and `-- VOCABULARY-END`, byte-identical in all
three challenges: the averaging operator and the Laplacian of a locally finite
graph, the parallel toppling procedure with its odometer `u_n` and limit
`u_∞`, stabilization, the heat kernel and the Green function, the walk payoff
`S_n` and bounded stopping times, the law of simple random walk on path space,
the i.i.d. scenery with its extended mean, positive moments, variance and
symmetry, the two optimal stopping suprema, the joint law of scenery and walk,
double transience, a degree bound, polynomial volume growth, and the one cited
result kept in the vocabulary, the pointwise Carne–Varopoulos bound, proved
outright and kept only for provenance.  The voltage function that
`OptimalStopping` and `Explosion` used to carry as a hypothesis is now proved
on every infinite connected graph and discharged inside the proofs, so it is
no longer part of the vocabulary.

## What Is Checked

All three theorems are unconditional: every result the paper cites without
proof is proved outright inside the repository, and no challenge carries one
as a hypothesis.

| Directory | Cited result once carried as a hypothesis |
| --- | --- |
| `OptimalStopping/`, `Explosion/` | `External.VoltageFunction G` (Lyons–Peres, Proposition 2.1 and equation (2.4)), proved on every infinite connected graph, recurrent or transient (`RWRS.External.voltageFunction_of_connected`), and discharged inside the proofs; no longer part of the vocabulary |
| `Stabilization/` | `External.CarneVaropoulos G` (Carne, Varopoulos, Lyons–Peres Theorem 13.4, pointwise form), proved outright; kept in the vocabulary only for provenance |

The frozen statements `RWRS.Frozen.optimalStopping` and
`RWRS.Frozen.stabilization` also take the von Bahr–Esseen inequality, the
Fuk–Nagaev tail inequality and the bounded-degree heat kernel bound as
hypotheses.  They are not hypotheses here: the repository proves the first two
outright (`RWRS.External.vonBahrEsseen`, `RWRS.External.fukNagaevTail`, from
the shared library Lattice-Probability) and the third on every infinite
connected graph (`RWRS.External.heatKernelBoundedDegree_of_connected`), and
`RWRS/MainTheorems.lean` discharges them.

- **`OptimalStopping`** (Theorem 1.1): on an infinite connected graph of degree
  at most `d`, with an i.i.d. scenery `ξ` of law `ν` and
  `S_n = ∑_{k<n} ξ(X_k)/deg(X_k)`: if `E[ξ] > 0`, then
  `sup_n E_x[S_n | ξ] = ∞` almost surely; if `E[ξ] = 0` with positive finite
  variance, or `ξ ≢ 0` symmetric, then `sup_τ E_x[S_τ | ξ] = ∞` almost surely
  over bounded stopping times, and `sup_n E_x[S_n | ξ] = ∞` if the graph is not
  doubly transient; if `E[ξ] < 0` and `E[(ξ⁺)^p] < ∞` for some `p > 3`, then
  `E_x[(sup_n S_n)^q] < ∞` for `q ∈ [1, (p-1)/2)`.
- **`Explosion`** (Theorem 1.2): i.i.d. masses of mean `μ > 1`, or of mean
  `μ = 1` with positive finite variance or with `σ - 1` symmetric and
  `σ ≢ 1`, stabilize with probability zero.
- **`Stabilization`** (Theorem 1.3): i.i.d. masses of mean `μ < 1` with
  `E[(σ⁺)^p] < ∞` for some `p > 3` have `sup_v E[u_∞(v)^q] < ∞` for
  `q ∈ [1, (p-1)/2)` and stabilize almost surely; under `|B(o,r)| ≤ C r^{d_f}`,
  `E[(σ⁺)^p] < ∞` for some `p > d_f` suffices for stabilization.

## Definition Provenance

The challenge definitions are statement-level copies of the repository
definitions needed to state the theorems, in the namespace `RWRSAudit`.  None
comes from the shared library Lattice-Probability: the statements are written
in this repository's own vocabulary, which is built on Mathlib alone.

| Challenge declaration | Repository source |
| --- | --- |
| `walkOp`, `laplacian`, `closedBall`, `emission`, `topple`, `config`, `odometer`, `odometerLimit`, `Stabilizes`, `heat`, `green` | `RWRS/Basic.lean` |
| `cons`, `walkExp`, `IsStopping`, `payoff`, `stopValues`, `stepLaw`, `driverLaw`, `stepTo`, `walkPath`, `walkLaw`, `supPayoff` | `RWRS/Walk.lean` |
| `iidLaw`, `posPart`, `negPart`, `extMean`, `HasExtMean`, `posMoment`, `IsSymmetric`, `evar` | `RWRS/Scenery.lean` |
| `meanPayoff`, `supMeanPayoff`, `supStopValue`, `jointLaw`, `DoublyTransient`, `BoundedDegree`, `VolumeGrowthUpper` | `RWRS/Setting.lean` |
| `External.CarneVaropoulos` | `RWRS/External/CarneVaropoulos.lean` |

## Solutions

Each `Solution.lean` imports the repository together with
`Audit/Support/Vocabulary.lean`, a verbatim copy of the vocabulary block that
imports only Mathlib, and proves the byte-identical statement from the
corresponding theorem of `RWRS/MainTheorems.lean` through the identifications
in `Audit/Support/Bridge.lean` (see [`DESIGN.md`](DESIGN.md)).

`Audit/StatementRegression.lean` is a local check of the statement-identity
part of the comparator: it elaborates each statement in the challenge
environment (`Audit/Support/Statements.lean`, which imports only Mathlib and
the vocabulary), checks that each solution theorem has exactly that type and
mentions no constant of the repository namespace `RWRS` or of the library
namespace `LatticeProb`, and prints the axioms
of each solution theorem.

## Reproducing The Checks

The comparator configurations permit only

```json
["propext", "Quot.sound", "Classical.choice"]
```

and set `enable_nanoda: false`.  Each challenge elaborates standalone against
this repository's Mathlib toolchain, e.g.

```bash
bash Audit/check_standalone.sh Audit/OptimalStopping/Challenge.lean
bash Audit/check_standalone.sh --vocabulary
```

with expected outcome `rc=0` and exactly one `declaration uses 'sorry'`
warning per challenge; the second command checks that the vocabulary block is
the same in every challenge and in `Audit/Support/Vocabulary.lean`.  The
solutions and the regression build with

```bash
lake build Audit.StatementRegression
```

which prints, for each of the three theorems, that it is identical to the
challenge statement and depends only on `propext`, `Classical.choice` and
`Quot.sound`.

**Status.**  All three solutions build, and the statement regression and the
axiom prints pass locally.  `leanprover/comparator` was run on all three
pairs on 2026-09-27 at commit `c7a26b9`, against the current statements, and
each pair passed with the Lean kernel and with the independent nanoda kernel;
see [`COMPARATOR_RUNS.md`](COMPARATOR_RUNS.md) for the recorded runs.  The
workflow
[`.github/workflows/comparator.yml`](../.github/workflows/comparator.yml)
runs it on request.
