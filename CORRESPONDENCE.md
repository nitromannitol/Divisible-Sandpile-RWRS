# Correspondence between the paper and the formalization

`paper/rwrs.tex` is the contract: the Annals of Probability submission of
*Divisible sandpiles via random walks in random scenery*.  Every theorem,
proposition, lemma and corollary of it is transcribed once, between the markers

```
-- FROZEN-STATEMENT-BEGIN
…
-- FROZEN-STATEMENT-END
```

in its own file under `RWRS/Frozen/`, with a docstring quoting the paper and a
line anchor, and registered in `ledger/manifest.yaml`.  The bytes between the
markers are the contract; `frozen_sha256` is their SHA-256, computed by
`tools/freeze.py` with one leading newline dropped and the trailing newline
before the end marker kept, and checked by `tools/check_manifest.py`.

A result the paper cites rather than proves is a `def … : Prop` under
`RWRS/External/`, in state `FROZEN`, and enters the results that use it as an
explicit hypothesis. Each records its mathematical source; proved witnesses
and their hypotheses are listed below.

## Transcription conventions

- **Standing hypotheses.**  `ssec:notation` fixes an infinite, locally finite,
  connected graph throughout. Statements carry these hypotheses where needed.
  Path-space and scenery laws use measurable structures, with measurable
  singletons for the discrete vertex space.
- **Quantifier order.**  A constant the paper fixes before `n` is bound before
  `n`.  A constant the paper calls universal, or says depends only on certain
  data, is bound before everything else it must not depend on.
- **Cited inputs.**  A classical theorem the paper cites rather than proves is
  stated as a proposition in `RWRS/External/` and carried as an explicit
  hypothesis by every frozen statement whose proof uses it, so that what is
  assumed is visible in the statement itself. The generated input table below
  records these hypotheses.
- **Junk values.**  A statement is written so that no junk value can satisfy it.
  Quantities the paper allows to be infinite live in `ℝ≥0∞` or `EReal`:
  `u_∞`, the Green function, `Σ_n`, `Θ_C`, `sup_n S_n`, the two optimal-stopping
  suprema, every moment, and the extended mean, which carries `HasExtMean` to
  exclude the paper's indeterminate case.  Cardinalities of balls are
  `Set.encard`.  A supremum the paper asserts is written as `IsLUB`, so an
  unattained or unbounded supremum cannot satisfy it.  Where a Bochner integral
  appears in a conclusion, its integrability is asserted with it.

- `prop:comb-estimates`(d) reads the paper's "a vertex `v` in the first half of
  the terminal pipe `P_w`, at distance at least `L_n/2` from the boundary" as
  `combFirstHalf`, the sites `(w,i)` with `1 ≤ i` and `2i ≤ L_n`.  In the
  indexing of the tree of pipes the site `(w,0)` is the FAR endpoint of the
  terminal pipe, which is on the absorbing boundary and outside the comb; the
  junction of the terminal pipe with the trunk is `b_{n-1} = (w.take (n-1), 0)`,
  a site of a different word.  So the clause `1 ≤ i` deletes exactly the
  boundary vertex, and the distance to the boundary of `(w,i)` is `L_n - i`,
  which is at least `L_n/2` precisely when `2i ≤ L_n`.

- `lem:tr-good` and `cor:rec-loc` quantify over the constants the paper fixes
  before them.  `lem:tr-good` takes any `K > 0` where the paper takes the `K` of
  `prop:comb-estimates`(d), and `cor:rec-loc` takes any `b ≥ 0` where the paper
  takes `b = E[Y] - μ_0 + 1`; in both the constant appears only in the
  hypotheses of the conclusion, so the general form specializes to the paper's.
  `cor:rec-loc` also quantifies over the flag `e`, which is the paper's "at most
  one extra boundary edge", so both cases of the paper's sentence are covered.
- `cor:rec-loc` is written `∀ v ∈ combFirstHalf, threshold ≤ Y v → conclusion`,
  and the conclusion does not mention `v`.  That is the paper's "whenever a
  vertex `v` in the first half satisfies `Y_v ≥ K L_m`", since a statement
  `∀ v, P v → Q` with `Q` free of `v` is `(∃ v, P v) → Q`.
- `lem:tr-good` does not carry the paper's `p`.  The section fixes `p ∈ (0,3)`
  and then `q` with `max(p,1) < q < 3`; the good-pipe estimate uses only the
  consequences `1 < q` and `α(q-1) < 1`, and `p` enters `thm:transient-nonstab`
  through the moment of the marginal, not here.

## Geometric and probabilistic conventions

- Divergence of `Σ_n(o)` means `Tendsto (fun n => fluct G n o) atTop (𝓝 ⊤)`:
  convergence to infinity in the order topology of `[0,∞]`.
- Finite-volume exit-payoff identities include integrability. Polynomial growth
  uses finite balls and their cardinalities. The recurrent construction carries
  the section's full condition `0 < ρ < δ/(d_f+1)`.
- Invariant events of a marked network may depend on both graph and marks.
  Ergodic decomposition is a conditional law given the invariant sigma algebra
  of the rooted graph, with stationary ergodic components supported on connected
  graphs. Heat-kernel decay is required on those connected graphs.
- `prop:poly-growth` carries the uniform walk-dimension hypothesis (H3).
  The proof of stabilization part (ii) uses `PolynomialExitBoundAt`, which
  requires exit control at one origin and radii strictly above the diffusive
  scale. Rooted volume growth transfers to each starting vertex with a
  vertex-dependent constant; countability gives simultaneous stabilization.

## Cited inputs and proved witnesses

<!-- CITED-INPUTS-BEGIN (generated by tools/sync_docs.py) -->

The manifest registers 9 external propositions. A proposition's
axiom closure checks its definition; a witness theorem proves the input
under the witness's stated hypotheses.

| input | proposition | source | proved witness |
|---|---|---|---|
| `X-001` | `RWRS.External.VonBahrEsseen` | rwrs.tex:1096-1098 (cited in lem:fuk-nagaev) | `RWRS.External.vonBahrEsseen` (`X-001P`) |
| `X-002` | `RWRS.External.FukNagaevTail` | rwrs.tex:1096-1098 (cited in lem:fuk-nagaev) | `RWRS.External.fukNagaevTail` (`X-002P`) |
| `X-003` | `RWRS.External.Bernstein` | rwrs.tex:1096-1098 (cited in lem:fuk-nagaev) | `RWRS.External.bernstein` (`X-003P`) |
| `X-004` | `RWRS.External.HeatKernelBoundedDegree` | rwrs.tex:144-149 (cited in thm:stab) | `RWRS.External.heatKernelBoundedDegree_of_connected` (`X-004P`) |
| `X-006` | `RWRS.External.HeatKernelVanishing` | rwrs.tex:319-322 (cited in lem:ergodic-marked-stationary) | `RWRS.External.heatKernelVanishing_of_connected` (`X-006P`) |
| `X-008` | `RWRS.External.VoltageFunction` | rwrs.tex:513-520 (cited in prop:01-law) | `RWRS.External.voltageFunction` (`X-008P`) |
| `X-007` | `RWRS.External.EfronStein` | rwrs.tex:694-699 (cited in prop:critical) | `RWRS.External.efronStein` (`X-007P`) |
| `X-009` | `RWRS.External.ErgodicDecomposition` | rwrs.tex:337-342 (cited in lem:01-stationary) | — |
| `X-005` | `RWRS.External.CarneVaropoulos` | rwrs.tex:143-149 (Carne 1985, Varopoulos 1985, Lyons-Peres Theorem 13.4) | — |

`X-005` is the pointwise transition estimate
`P_x(X_n = y) ≤ 2 sqrt(deg(y)/deg(x)) exp(-dist(x,y)^2/(2n))`,
for `n ≥ 1` on a connected, nontrivial, locally finite graph with measurable
singletons. Its sources are Carne (1985), Varopoulos (1985), and
[Lyons–Peres, Theorem 13.4](https://rdlyons.pages.iu.edu/prbtree/book_pb.pdf).
`RWRS/Support/DisplacementAtOrigin.lean` combines this input with a degree bound
and polynomial volume growth at the origin to prove the exit estimates at
radii `⌈N^(1/2+s)⌉`, `s > 0`, used in stabilization part (ii).
The constants may depend on the origin and on `s`.

<!-- CITED-INPUTS-END -->

The voltage witness is proved on transient graphs from the difference of two
normalized Green masses, shifted by a constant to make it nonnegative.
Bernstein and Efron–Stein witnesses are used at the sites where their
hypotheses hold. Frozen statements may explicitly retain a witnessed input.

<!-- INPUT-HYPOTHESES-BEGIN (generated by tools/sync_docs.py) -->

| theorem node | external propositions in the frozen statement |
|---|---|
| `N-025` | `X-003`, `X-002`, `X-001` |
| `N-014` | `X-008` |
| `N-015` | `X-006` |
| `N-018` | `X-006` |
| `N-020` | `X-007`, `X-008` |
| `N-022` | `X-008` |
| `X-003P` | `X-003` |
| `X-008P` | `X-008` |
| `N-028` | `X-002`, `X-001` |
| `N-003` | `X-005`, `X-002`, `X-004`, `X-001` |
| `N-007` | `X-006` |
| `N-008` | `X-009`, `X-006` |
| `N-005` | `X-009`, `X-006` |
| `N-002` | `X-008` |
| `N-001` | `X-002`, `X-004`, `X-008`, `X-001` |
| `X-001P` | `X-001` |
| `X-002P` | `X-002` |
| `X-004P` | `X-004` |
| `X-006P` | `X-006` |
| `X-007P` | `X-007` |

<!-- INPUT-HYPOTHESES-END -->

## Statements whose hypotheses the proof does not use

`lem:clock-no-dom` and `prop:supercritical` carry, in their frozen form, a
hypothesis their proof here does not refer to. The unreferenced-binder linter
is disabled locally, with the mathematical reason recorded there.

- `lem:clock-no-dom` assumes the vanishing of the return probability, quoted in
  the paper from Lyons and Peres.  The proof here reaches the conclusion from
  the survival probability of the walk before its first visit to a vertex, and
  the assumption is not used.
- `prop:supercritical` assumes the exclusion of the indeterminate case of
  `ssec:notation`.  The positivity of the extended mean already forces the
  negative part to be finite, so the exclusion is not used.
- `prop:critical`(a) is stated for `n ≥ 1`.  The Efron--Stein argument does not
  use it, so the variance bound is proved for every `n`, the case `n = 0` being
  the trivial one.
- `prop:convexity-reduction` assumes that the mean of the scenery vanishes.  The
  reduction builds its own bounded mean-zero scenery out of the symmetry of the
  law, and the symmetry already forces the mean to vanish wherever it is used,
  so the assumption is not referred to.

- `lem:good-walk` fixes the mean of the scenery to be negative and `δ` below
  `min(d_s/2, 1)`.  Neither is referred to: `Y_k` subtracts the nonnegative
  quantity `|m|2^k/d` whatever the sign of the mean, so parts (a), (b) and (c)
  hold for every mean; and the three bounds hold for every positive `δ` because
  the order `r` of the moment is chosen after `δ`.  The section needs the two
  restrictions when it applies the lemma, so they are carried.

- `lem:moment-sharpness` assumes the standing exclusion of the indeterminate
  case of `ssec:notation`.  The proof splits on whether the mean of the positive
  part is infinite: in the infinite case the rule that stops after one step
  already gives the conclusion, and in the finite case the strict lower bound on
  the extended mean forces the mean of the negative part to be finite as well.
  Neither branch refers to the exclusion.

- `prop:finite-vol` assumes that `K` is connected.  The four clauses are proved
  from the finiteness and properness of `K` alone, the walk leaving a finite
  proper set almost surely from every site of a connected graph, so the
  connectedness of `K` itself is carried but not referred to.

- `lem:tr-good` fixes `q < 3`, which is what makes the marginal of
  `thm:transient-nonstab` have a finite `p`-th moment.  The good-pipe estimate
  itself uses only `1 < q` and `α(q-1) < 1`, so the upper bound on `q` is
  carried but not referred to.

## The shared library

The transition kernel, the walk average and every object built from them are
defined here by the same recursions as in `LatticeProb/Graph/`.  The two are
identified once, in `RWRS/Support/LibraryBridge.lean`, by an induction on the
number of steps (`heat_eq_lib`), and every library result this repository uses
is restated there in this repository's vocabulary and proved by the library
theorem.  The two developments are therefore not two proofs of anything: the
mathematics lives in the library, and the bridge is a renaming.

Replacing the definitions here by the library's outright is not possible while
the frozen statements name them: an `export` alias is resolved by Lean only
through `open`, so the fully qualified names inside the frozen blocks would
stop resolving, and the frozen bytes are the contract.

## The frozen surface

<!-- FROZEN-SURFACE-BEGIN (generated by tools/sync_docs.py) -->

| id | Lean | paper | state |
|---|---|---|---|
| `N-004` | `RWRS.Frozen.iidStationary` | rwrs.tex:257-259 (prop:iid-stationary) | SEALED |
| `N-006` | `RWRS.Frozen.stationaryToppling` | rwrs.tex:278-284 (thm:stationary-toppling) | SEALED |
| `N-009` | `RWRS.Frozen.recursion` | rwrs.tex:377-382 (lem:recursion) | SEALED |
| `N-016` | `RWRS.Frozen.supercritical` | rwrs.tex:554-558 (prop:supercritical) | SEALED |
| `N-017` | `RWRS.Frozen.positivePart` | rwrs.tex:600-605 (lem:positive-part) | SEALED |
| `N-019` | `RWRS.Frozen.sensitivity` | rwrs.tex:636-653 (lem:sensitivity) | SEALED |
| `N-025` | `RWRS.Frozen.fukNagaev` | rwrs.tex:1077-1095 (lem:fuk-nagaev) | SEALED |
| `X-001` | `RWRS.External.VonBahrEsseen` | rwrs.tex:1096-1098 (cited in lem:fuk-nagaev) | FROZEN |
| `X-002` | `RWRS.External.FukNagaevTail` | rwrs.tex:1096-1098 (cited in lem:fuk-nagaev) | FROZEN |
| `X-003` | `RWRS.External.Bernstein` | rwrs.tex:1096-1098 (cited in lem:fuk-nagaev) | FROZEN |
| `N-010` | `RWRS.Frozen.randomWalkRepresentation` | rwrs.tex:393-400 (thm:RW) | SEALED |
| `N-013` | `RWRS.Frozen.rwInfinite` | rwrs.tex:473-478 (cor:RW-infinite) | SEALED |
| `N-033` | `RWRS.Frozen.coboundary` | rwrs.tex:1478-1480 (ex:coboundary) | SEALED |
| `N-032` | `RWRS.Frozen.finitePerturbation` | rwrs.tex:1453-1456 (ex:finite-perturbation) | SEALED |
| `X-004` | `RWRS.External.HeatKernelBoundedDegree` | rwrs.tex:144-149 (cited in thm:stab) | FROZEN |
| `X-006` | `RWRS.External.HeatKernelVanishing` | rwrs.tex:319-322 (cited in lem:ergodic-marked-stationary) | FROZEN |
| `X-008` | `RWRS.External.VoltageFunction` | rwrs.tex:513-520 (cited in prop:01-law) | FROZEN |
| `N-014` | `RWRS.Frozen.zeroOneLaw` | rwrs.tex:491-495 (prop:01-law) | SEALED |
| `N-015` | `RWRS.Frozen.clockNoDominance` | rwrs.tex:531-536 (lem:clock-no-dom) | SEALED |
| `N-023` | `RWRS.Frozen.shortClock` | rwrs.tex:997-999 (prop:short-clock) | SEALED |
| `N-030` | `RWRS.Frozen.unboundedDegreeTree` | rwrs.tex:1364-1366 (ex:counterexample) | SEALED |
| `N-018` | `RWRS.Frozen.noDominance` | rwrs.tex:629-632 (lem:no-dominance) | SEALED |
| `N-020` | `RWRS.Frozen.critical` | rwrs.tex:664-683 (prop:critical) | SEALED |
| `N-022` | `RWRS.Frozen.convexityReduction` | rwrs.tex:950-954 (prop:convexity-reduction) | SEALED |
| `X-007` | `RWRS.External.EfronStein` | rwrs.tex:694-699 (cited in prop:critical) | FROZEN |
| `N-026` | `RWRS.Frozen.dyadic` | rwrs.tex:1102-1111 (lem:dyadic) | SEALED |
| `N-038` | `RWRS.Frozen.gadgetGeometry` | rwrs.tex:1740-1747 (lem:rec-geometry) | SEALED |
| `N-041` | `RWRS.Frozen.recGoodEvents` | rwrs.tex:1946-1948 (lem:rec-good) | SEALED |
| `N-040` | `RWRS.Frozen.recVolumeGrowth` | rwrs.tex:1919-1922 (prop:rec-growth) | SEALED |
| `N-034` | `RWRS.Frozen.combEstimates` | rwrs.tex:1530-1545 (prop:comb-estimates) | SEALED |
| `N-039` | `RWRS.Frozen.recLocal` | rwrs.tex:1792-1799 (cor:rec-loc) | SEALED |
| `N-036` | `RWRS.Frozen.transientGoodPipes` | rwrs.tex:1661-1663 (lem:tr-good) | SEALED |
| `N-011` | `RWRS.Frozen.finiteVolume` | rwrs.tex:429-438 (prop:finite-vol) | SEALED |
| `N-012` | `RWRS.Frozen.nestedVolume` | rwrs.tex:448-453 (thm:nested-vol) | SEALED |
| `N-035` | `RWRS.Frozen.transientNonstabilization` | rwrs.tex:1575-1577 (thm:transient-nonstab) | SEALED |
| `N-037` | `RWRS.Frozen.recurrentNonstabilization` | rwrs.tex:1700-1708 (thm:recurrent-nonstab) | SEALED |
| `N-024` | `RWRS.Frozen.localTimeMoments` | rwrs.tex:1019-1034 (lem:local-time) | SEALED |
| `N-027` | `RWRS.Frozen.goodWalkBounds` | rwrs.tex:1124-1142 (lem:good-walk) | SEALED |
| `N-031` | `RWRS.Frozen.momentSharpness` | rwrs.tex:1385-1398 (lem:moment-sharpness) | SEALED |
| `X-003P` | `RWRS.External.bernstein` | rwrs.tex:1096-1098 (Bernstein cited in lem:fuk-nagaev, proved) | SEALED |
| `X-008P` | `RWRS.External.voltageFunction` | rwrs.tex:513-520 (voltage function cited in prop:01-law, proved on a transient graph) | SEALED |
| `N-028` | `RWRS.Frozen.subcritical` | rwrs.tex:1155-1165 (prop:subcritical) | SEALED |
| `N-029` | `RWRS.Frozen.polyGrowth` | rwrs.tex:1229-1241 (prop:poly-growth) | SEALED |
| `N-003` | `RWRS.Frozen.stabilization` | rwrs.tex:131-140 (thm:stab) | SEALED |
| `N-007` | `RWRS.Frozen.ergodicMarked` | rwrs.tex:310-312 (lem:ergodic-marked-stationary) | SEALED |
| `X-009` | `RWRS.External.ErgodicDecomposition` | rwrs.tex:337-342 (cited in lem:01-stationary) | FROZEN |
| `N-008` | `RWRS.Frozen.zeroOneStationary` | rwrs.tex:329-334 (lem:01-stationary) | SEALED |
| `N-005` | `RWRS.Frozen.stationaryPhase` | rwrs.tex:268-274 (thm:stationary-phase) | SEALED |
| `N-021` | `RWRS.Frozen.doublyTransient` | rwrs.tex:777-781 (prop:doubly-transient-really-general) | SEALED |
| `N-002` | `RWRS.Frozen.explosion` | rwrs.tex:117-127 (thm:explosion) | SEALED |
| `N-001` | `RWRS.Frozen.optimalStopping` | rwrs.tex:94-101 (thm:OS) | SEALED |
| `X-005` | `RWRS.External.CarneVaropoulos` | rwrs.tex:143-149 (Carne 1985, Varopoulos 1985, Lyons-Peres Theorem 13.4) | FROZEN |
| `X-001P` | `RWRS.External.vonBahrEsseen` | rwrs.tex:1096-1098 (von Bahr--Esseen cited in lem:fuk-nagaev, proved) | SEALED |
| `X-002P` | `RWRS.External.fukNagaevTail` | rwrs.tex:1096-1098 (Fuk--Nagaev cited in lem:fuk-nagaev, proved) | SEALED |
| `X-004P` | `RWRS.External.heatKernelBoundedDegree_of_connected` | rwrs.tex:144-149 (bounded-degree heat kernel bound, proved on infinite connected graphs) | SEALED |
| `X-006P` | `RWRS.External.heatKernelVanishing_of_connected` | rwrs.tex:319-322 (heat kernel vanishing, proved on infinite connected graphs) | SEALED |
| `X-007P` | `RWRS.External.efronStein` | rwrs.tex:694-699 (Efron--Stein inequality, proved for countable index sets) | SEALED |

<!-- FROZEN-SURFACE-END -->
