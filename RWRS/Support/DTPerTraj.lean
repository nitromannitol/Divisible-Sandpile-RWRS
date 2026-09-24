/-
The two per-trajectory bounds of Step 1: on the walk-good event the conditional
estimate gains `-8m` on a set of scenery of mass at least three quarters, and on
every trajectory that leaves `K` before the horizon it is at most zero.  On the
remaining trajectories the estimate is bounded by a constant of `K`.
-/
import RWRS.Support.DTTrajectory
import RWRS.Support.DTHitSum
import RWRS.Support.DTNoHit
import RWRS.Support.DTWalkGood
import RWRS.Support.DTRuleBound
import RWRS.Support.WeakLaw

open scoped Classical ENNReal
open MeasureTheory

namespace RWRS.Support

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]
  [DecidableEq V] [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]

omit [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] [DecidableEq V] in
/-- **The crude bound**: the conditional estimate never exceeds the size of the
killed potential on `K`. -/
theorem integral_trapPotential_cappedRule_le_const (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (hint : Integrable (fun z : ℝ => z) ν)
    (r : ℕ) (C : V → Finset V) (ℓ : ℕ) (K : Finset V) (N : ℕ) (ε : ℝ) (X : ℕ → V)
    (hescK : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ (K : Set V))
    (hdeg : ∀ v ∈ K, 0 < G.degree v) :
    ∫ ξ : V → ℝ, trapPotential G K ξ (X (trapRuleCapped G r C ℓ K N ε ξ X))
        ∂(RWRS.iidLaw V ν)
      ≤ (∑ v ∈ K, RWRS.killedGreenReal G (K : Set V) v v)
          * ((K.card : ℝ) * ∫ z, |z| ∂ν) := by
  have habs : Integrable (fun z : ℝ => |z|) ν := hint.abs
  have hF : Integrable (fun ξ : V → ℝ =>
      trapPotential G K ξ (X (trapRuleCapped G r C ℓ K N ε ξ X))) (RWRS.iidLaw V ν) :=
    integrable_trapPotential_cappedRule ν hint r C ℓ K N ε X
  have hsum : Integrable (fun ξ : V → ℝ =>
      (∑ v ∈ K, RWRS.killedGreenReal G (K : Set V) v v) * ∑ v ∈ K, |ξ v|)
      (RWRS.iidLaw V ν) :=
    (integrable_finsetSum _ fun v _ => integrable_coord ν v habs).const_mul _
  have hbound : ∀ ξ : V → ℝ,
      trapPotential G K ξ (X (trapRuleCapped G r C ℓ K N ε ξ X))
        ≤ (∑ v ∈ K, RWRS.killedGreenReal G (K : Set V) v v) * ∑ v ∈ K, |ξ v| := fun ξ =>
    le_trans (le_abs_self _) (abs_trapPotential_le K hescK hdeg ξ _)
  refine le_trans (integral_mono hF hsum hbound) (le_of_eq ?_)
  rw [integral_const_mul, integral_finsetSum _ fun v _ => integrable_coord ν v habs]
  congr 1
  rw [Finset.sum_congr rfl fun v _ => integral_coord ν v habs.aestronglyMeasurable]
  rw [Finset.sum_const, nsmul_eq_mul]

omit [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] [DecidableEq V] in
/-- **The estimate is nonpositive once the walk leaves `K` before the
horizon.** -/
theorem integral_trapPotential_cappedRule_nonpos (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (h0 : RWRS.extMean ν = 0)
    (hint : Integrable (fun z : ℝ => z) ν)
    (r : ℕ) (C : V → Finset V) (ℓ : ℕ) (K : Finset V) {N : ℕ} (hN : 0 < N) (ε : ℝ)
    (X : ℕ → V) (m : ℝ)
    (hCball : ∀ y : V, ((C y : Finset V) : Set V) ⊆ RWRS.closedBall G y r)
    (hCself : ∀ y : V, y ∈ C y)
    (hescK : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ (K : Set V))
    (hescC : ∀ y x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ (C y : Set V))
    (hΘ : ∀ y : V, ENNReal.ofReal (8 * m / ε) ≤ RWRS.thetaExit G (C y : Set V) y)
    (hdeg : ∀ w : V, 0 < G.degree w) (hε : 0 < ε) (hm : 0 ≤ m) {q : ℝ} (hq : 0 < q)
    (hcompl : ∀ y : V, ENNReal.ofReal q
      ≤ RWRS.iidLaw V ν ((trapEvent (C y) ε)ᶜ))
    (hexit : ∃ n, n < N ∧ X n ∉ K)
    (hgain : (∫ z, |z| ∂ν) / q ≤ 8 * m) :
    ∫ ξ : V → ℝ, trapPotential G K ξ (X (trapRuleCapped G r C ℓ K N ε ξ X))
        ∂(RWRS.iidLaw V ν) ≤ 0 := by
  refine le_trans (integral_trapPotential_cappedRule_le ν h0 hint r C ℓ K hN ε X m
    hCball hCself hescK hescC hΘ hdeg hε hm hq hcompl hexit) ?_
  refine Finset.sum_nonpos fun i _ => ?_
  set P := (RWRS.iidLaw V ν
    (hitEvent (fun j => C (X ((uncTime G r C X j).toNat))) ε i)).toReal with hP
  have hP0 : 0 ≤ P := ENNReal.toReal_nonneg
  have hrw : (-8 * m) * P + (∫ z, |z| ∂ν) * (P / q)
      = P * ((∫ z, |z| ∂ν) / q - 8 * m) := by
    ring
  rw [hrw]
  exact mul_nonpos_of_nonneg_of_nonpos hP0 (by linarith)

omit [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] [DecidableEq V] in
/-- **The gain on the walk-good event**: at least three quarters of the scenery
mass carries the `-8m` gain. -/
theorem integral_trapPotential_cappedRule_good_le (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (h0 : RWRS.extMean ν = 0)
    (hint : Integrable (fun z : ℝ => z) ν)
    (r : ℕ) (C : V → Finset V) (ℓ : ℕ) (K : Finset V) {N : ℕ} (hN : 0 < N) (ε : ℝ)
    (X : ℕ → V) (hgood : X ∈ walkGoodEvent G r C ℓ K N) (m : ℝ)
    (hCball : ∀ y : V, ((C y : Finset V) : Set V) ⊆ RWRS.closedBall G y r)
    (hCself : ∀ y : V, y ∈ C y)
    (hescK : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ (K : Set V))
    (hescC : ∀ y x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ (C y : Set V))
    (hΘ : ∀ y : V, ENNReal.ofReal (8 * m / ε) ≤ RWRS.thetaExit G (C y : Set V) y)
    (hdeg : ∀ w : V, 0 < G.degree w) (hε : 0 < ε) (hm : 0 ≤ m) {q : ℝ} (hq : 0 < q)
    (hcompl : ∀ y : V, ENNReal.ofReal q
      ≤ RWRS.iidLaw V ν ((trapEvent (C y) ε)ᶜ))
    (hfail : RWRS.iidLaw V ν {ξ : V → ℝ | ∀ j < ℓ + 1,
        ξ ∉ trapEvent (C (X ((uncTime G r C X j).toNat))) ε} ≤ ENNReal.ofReal (1 / 4))
    (hgain : (∫ z, |z| ∂ν) / q ≤ 8 * m) :
    ∫ ξ : V → ℝ, trapPotential G K ξ (X (trapRuleCapped G r C ℓ K N ε ξ X))
        ∂(RWRS.iidLaw V ν)
      ≤ (3 / 4) * ((∫ z, |z| ∂ν) / q - 8 * m) := by
  have hcnt : stageCnt G r C ℓ K N X = ℓ + 1 :=
    stageCnt_eq_of_walkGood r C ℓ K hN X hgood
  have hmain := integral_trapPotential_cappedRule_le ν h0 hint r C ℓ K hN ε X m
    hCball hCself hescK hescC hΘ hdeg hε hm hq hcompl (exitEvent_of_walkGood hgood)
  rw [hcnt] at hmain
  have heq : (∑ i ∈ Finset.range (ℓ + 1),
        ((-8 * m) * ((RWRS.iidLaw V ν
          (hitEvent (fun j => C (X ((uncTime G r C X j).toNat))) ε i)).toReal)
          + (∫ z, |z| ∂ν) * ((RWRS.iidLaw V ν
            (hitEvent (fun j => C (X ((uncTime G r C X j).toNat))) ε i)).toReal / q)))
      = (∑ i ∈ Finset.range (ℓ + 1), (RWRS.iidLaw V ν
          (hitEvent (fun j => C (X ((uncTime G r C X j).toNat))) ε i)).toReal)
        * ((∫ z, |z| ∂ν) / q - 8 * m) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  refine le_trans hmain ?_
  rw [heq]
  have htotal := sum_measure_hitEvent_add_noHit (RWRS.iidLaw V ν)
    (fun j => C (X ((uncTime G r C X j).toNat))) ε (ℓ + 1)
  have hfailR : (RWRS.iidLaw V ν {ξ : V → ℝ | ∀ j < ℓ + 1,
      ξ ∉ trapEvent (C (X ((uncTime G r C X j).toNat))) ε}).toReal ≤ 1 / 4 := by
    have h := ENNReal.toReal_mono (by simp) hfail
    simpa using h
  have hge : (3 : ℝ) / 4 ≤ ∑ i ∈ Finset.range (ℓ + 1), (RWRS.iidLaw V ν
      (hitEvent (fun j => C (X ((uncTime G r C X j).toNat))) ε i)).toReal := by
    linarith
  have hneg : (∫ z, |z| ∂ν) / q - 8 * m ≤ 0 := by linarith
  exact mul_le_mul_of_nonpos_right hge hneg

end RWRS.Support
