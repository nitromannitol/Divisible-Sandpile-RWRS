import RWRS.Frozen.OptimalStopping
import RWRS.Frozen.Explosion
import RWRS.Frozen.Stabilization

/-!
# Main results

The main theorems of the formalization of *Divisible sandpiles via random walks
in random scenery* (Bou-Rabee, Peres and Sava-Huss, arXiv:2604.13968), stated
here in full: Theorem 1.1 (`thm:OS`), explosion and stabilization for random
walk in random scenery; Theorem 1.2 (`thm:explosion`), explosion of the
divisible sandpile; and Theorem 1.3 (`thm:stab`), its stabilization.

Each theorem below restates its certified counterpart in `RWRS/Frozen/` and is
proved by direct application of it, so the statements displayed in this file
are byte-faithful to the certified ones.  Four cited inputs the paper quotes
for these theorems are proved outright, as ordinary `SEALED` theorems, in
`RWRS/External/`, and so already carry no hypothesis in the certified
statements themselves: the von Bahr–Esseen inequality
(`RWRS.External.vonBahrEsseen`), the Fuk–Nagaev tail inequality
(`RWRS.External.fukNagaevTail`), the bounded-degree heat kernel bound
(`RWRS.External.heatKernelBoundedDegree_of_connected`, which needs only that
`G` is infinite and connected), and the pointwise Carne–Varopoulos bound
(`RWRS.External.carneVaropoulos`, unconditional).

`External.VoltageFunction G`, the existence of a bounded voltage between two
vertices, is proved on every infinite connected graph, recurrent or transient,
by `RWRS.External.voltageFunction_of_connected`.  It is discharged inside the
proofs, so it is not a hypothesis of Theorems 1.1 and 1.2.

* `RWRS.optimalStopping`: Theorem 1.1.  With `S_n = ∑_{k<n} ξ(X_k)/deg(X_k)`
  for an i.i.d. scenery `ξ` of law `ν`: if `E[ξ] > 0` then
  `sup_n E_x[S_n | ξ] = ∞` almost surely; if `E[ξ] = 0` with positive finite
  variance, or with `ξ ≢ 0` symmetric, then `sup_τ E_x[S_τ | ξ] = ∞` almost
  surely over bounded stopping times, and `sup_n E_x[S_n | ξ] = ∞` if `G` is not
  doubly transient; if `E[ξ] < 0` and `E[(ξ⁺)^p] < ∞` for some `p > 3`, then
  `E_x[(sup_n S_n)^q] < ∞` for `q ∈ [1, (p-1)/2)`.
* `RWRS.explosion`: Theorem 1.2.  I.i.d. masses of mean `μ > 1`, or of mean
  `μ = 1` with positive finite variance or with `σ - 1` symmetric and
  `σ ≢ 1`, stabilize with probability zero.
* `RWRS.stabilization`: Theorem 1.3.  For i.i.d. masses of mean `μ < 1` with
  `E[(σ⁺)^p] < ∞` for some `p > 3`, `sup_v E[u_∞(v)^q] < ∞` for
  `q ∈ [1, (p-1)/2)` and the configuration stabilizes almost surely; under the
  volume growth bound `|B(o,r)| ≤ C r^{d_f}`, `E[(σ⁺)^p] < ∞` for some
  `p > d_f` suffices for stabilization.

All three reduce to the standard axioms (`propext`, `Classical.choice`,
`Quot.sound`); see `RWRS/Meta/AxiomsAudit.lean`.
-/

open MeasureTheory
open scoped ENNReal

universe u

/-- **Theorem 1.1** (`thm:OS`), explosion and stabilization for random walk in
random scenery.  The certified statement is `RWRS.Frozen.optimalStopping`,
restated unchanged (the von Bahr–Esseen, Fuk–Nagaev and bounded-degree heat
kernel inputs it needs are already proved, not carried). -/
theorem RWRS.optimalStopping {V : Type u} {G : SimpleGraph V} [G.LocallyFinite]
    [Infinite V] [MeasurableSpace V] [MeasurableSingletonClass V]
    (hG : G.Connected)
    (d : ℕ) (hd : RWRS.BoundedDegree G d) (ν : Measure ℝ) (hν : IsProbabilityMeasure ν)
    (hdet : RWRS.HasExtMean ν) :
    (0 < RWRS.extMean ν →
      ∀ x : V, ∀ᵐ ξ ∂(RWRS.iidLaw V ν), RWRS.supMeanPayoff G ξ x = ⊤) ∧
    (RWRS.extMean ν = 0 →
      ((0 < RWRS.evar ν ∧ RWRS.evar ν < ⊤) ∨ (ν ≠ Measure.dirac 0 ∧ RWRS.IsSymmetric ν)) →
      (∀ x : V, ∀ᵐ ξ ∂(RWRS.iidLaw V ν), RWRS.supStopValue G ξ x = ⊤) ∧
      (¬ RWRS.DoublyTransient G →
        ∀ x : V, ∀ᵐ ξ ∂(RWRS.iidLaw V ν), RWRS.supMeanPayoff G ξ x = ⊤)) ∧
    (RWRS.extMean ν < 0 → ∀ p : ℝ, 3 < p → RWRS.posMoment ν p ≠ ⊤ →
      ∀ q : ℝ, 1 ≤ q → q < (p - 1) / 2 → ∀ x : V,
        (∫⁻ z, RWRS.supPayoff G z.1 z.2 ^ q ∂(RWRS.jointLaw G ν x)) ≠ ⊤) := by
  exact RWRS.Frozen.optimalStopping hG d hd ν hν hdet

/-- **Theorem 1.2** (`thm:explosion`), explosion of the divisible sandpile.  The
certified statement is `RWRS.Frozen.explosion`, restated unchanged. -/
theorem RWRS.explosion {V : Type u} {G : SimpleGraph V} [G.LocallyFinite]
    [Infinite V] [MeasurableSpace V]
    (hG : G.Connected)
    (d : ℕ) (hd : RWRS.BoundedDegree G d) (ν : Measure ℝ) (hν : IsProbabilityMeasure ν)
    (hdet : RWRS.HasExtMean ν) :
    (1 < RWRS.extMean ν → RWRS.iidLaw V ν {σ : V → ℝ | RWRS.Stabilizes G σ} = 0) ∧
    (RWRS.extMean ν = 1 →
      ((0 < RWRS.evar ν ∧ RWRS.evar ν < ⊤) ∨
        (ν ≠ Measure.dirac 1 ∧ RWRS.IsSymmetric (ν.map (fun z => z - 1)))) →
      RWRS.iidLaw V ν {σ : V → ℝ | RWRS.Stabilizes G σ} = 0) := by
  exact RWRS.Frozen.explosion hG d hd ν hν hdet

/-- **Theorem 1.3** (`thm:stab`), stabilization of the divisible sandpile.  The
certified statement is `RWRS.Frozen.stabilization`, restated unchanged (the
bounded-degree heat kernel, von Bahr–Esseen, Fuk–Nagaev and pointwise
Carne–Varopoulos inputs it needs are already proved, not carried). -/
theorem RWRS.stabilization {V : Type u} {G : SimpleGraph V} [G.LocallyFinite]
    [Infinite V] [MeasurableSpace V] [MeasurableSingletonClass V]
    (hG : G.Connected)
    (d : ℕ) (hd : RWRS.BoundedDegree G d) (ν : Measure ℝ) (hν : IsProbabilityMeasure ν)
    (hdet : RWRS.HasExtMean ν) (hmean : RWRS.extMean ν < 1) :
    (∀ p : ℝ, 3 < p → RWRS.posMoment ν p ≠ ⊤ →
      (∀ q : ℝ, 1 ≤ q → q < (p - 1) / 2 →
        (⨆ v : V, ∫⁻ σ, RWRS.odometerLimit G σ v ^ q ∂(RWRS.iidLaw V ν)) ≠ ⊤) ∧
      RWRS.iidLaw V ν {σ : V → ℝ | RWRS.Stabilizes G σ} = 1) ∧
    (∀ (o : V) (C d_f : ℝ), 0 < C → 1 ≤ d_f → RWRS.VolumeGrowthUpper G o C d_f →
      ∀ p : ℝ, d_f < p → RWRS.posMoment ν p ≠ ⊤ →
        RWRS.iidLaw V ν {σ : V → ℝ | RWRS.Stabilizes G σ} = 1) := by
  exact RWRS.Frozen.stabilization hG d hd ν hν hdet hmean
