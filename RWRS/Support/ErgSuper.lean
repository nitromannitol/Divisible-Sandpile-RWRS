/-
The conserved mass of an i.i.d. marked network, and the integrability of the
mark law it forces.

The paper reads the conserved degree-weighted mass as `E[σ] E[1/deg(ρ)]`, and
gets `E|σ| < ∞` from `E[|σ(ρ)|/deg(ρ)] < ∞` because the two factors are
independent and the second is positive (`rwrs.tex:357`).
-/
import RWRS.Support.ErgCondNet
import RWRS.Support.ErgFactor
import RWRS.Support.ProbHelpers

namespace RWRS.Support

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- On a connected rooted graph the reciprocal degree at the root is positive. -/
theorem degWeight_pos {N : RWRS.Net 0} (hN : RWRS.NetGood N) : 0 < degWeight N := by
  have hdeg : 0 < (RWRS.netGraph N).degree (RWRS.netRoot N) := degree_pos hN (RWRS.netRoot N)
  rw [degWeight, inv_pos]
  exact_mod_cast hdeg

/-- The mean reciprocal degree at the root is positive. -/
theorem integral_degWeight_pos (Q : Measure (RWRS.Net 0)) [IsProbabilityMeasure Q]
    (hgood : ∀ᵐ N ∂Q, RWRS.NetGood N) : 0 < ∫ N, degWeight N ∂Q := by
  have hsupp : MeasurableSet (Function.support degWeight) :=
    measurableSet_support measurable_degWeight
  have hae : ∀ᵐ N ∂Q, N ∈ Function.support degWeight := by
    filter_upwards [hgood] with N hN
    exact ne_of_gt (degWeight_pos hN)
  have hcompl : Q (Function.support degWeight)ᶜ = 0 := ae_iff.mp hae
  have hone : Q (Function.support degWeight) = 1 := (prob_compl_eq_zero_iff hsupp).mp hcompl
  refine (integral_pos_iff_support_of_nonneg_ae ?_ (integrable_degWeight Q)).mpr ?_
  · exact Filter.Eventually.of_forall degWeight_nonneg
  · rw [hone]; exact zero_lt_one

/-- The mean reciprocal degree at the root is positive, in `ℝ≥0∞`. -/
theorem lintegral_degWeight_ne_zero (Q : Measure (RWRS.Net 0)) [IsProbabilityMeasure Q]
    (hgood : ∀ᵐ N ∂Q, RWRS.NetGood N) : (∫⁻ N, ‖degWeight N‖ₑ ∂Q) ≠ 0 := by
  intro hzero
  have hae0 : ∀ᵐ N ∂Q, ‖degWeight N‖ₑ = 0 := by
    have := (lintegral_eq_zero_iff measurable_degWeight.enorm).mp hzero
    filter_upwards [this] with N hN using hN
  have hfalse : ∀ᵐ N ∂Q, False := by
    filter_upwards [hgood, hae0] with N hN h0
    exact absurd (by simpa using h0) (ne_of_gt (degWeight_pos hN))
  obtain ⟨_, h⟩ := hfalse.exists
  exact h

/-- The conserved mass factorizes. -/
theorem integral_netWeightedMass_markIid (Q : Measure (RWRS.Net 0)) [IsProbabilityMeasure Q]
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν1 : Integrable (fun z : ℝ => z) ν) :
    (∫ M, RWRS.netWeightedMass M ∂(RWRS.markIid Q ν))
      = (∫ z, z ∂ν) * ∫ N, degWeight N ∂Q := by
  have hrw : ∀ M : RWRS.Net 1, RWRS.netWeightedMass M
      = (fun z : ℝ => z) (RWRS.netConfig M (RWRS.netRoot M)) * degWeight (RWRS.forgetMarks M) :=
    netWeightedMass_eq_mul
  simp only [hrw]
  exact integral_markIid_mark_mul Q ν measurable_id measurable_degWeight hν1 (integrable_degWeight Q)

/-- The integrability hypothesis of `thm:stationary-toppling` forces the mark law
to have a finite first moment. -/
theorem integrable_id_of_integrable_netWeightedMass (Q : Measure (RWRS.Net 0))
    [IsProbabilityMeasure Q] (hgood : ∀ᵐ N ∂Q, RWRS.NetGood N) (ν : Measure ℝ)
    [IsProbabilityMeasure ν]
    (hint : Integrable (fun M => |RWRS.netWeightedMass M|) (RWRS.markIid Q ν)) :
    Integrable (fun z : ℝ => z) ν := by
  refine ⟨measurable_id.aestronglyMeasurable, ?_⟩
  have hfac : (∫⁻ M, ‖RWRS.netConfig M (RWRS.netRoot M)‖ₑ * ‖degWeight (RWRS.forgetMarks M)‖ₑ
      ∂(RWRS.markIid Q ν)) = (∫⁻ z, ‖z‖ₑ ∂ν) * ∫⁻ N, ‖degWeight N‖ₑ ∂Q :=
    lintegral_markIid_mark_mul Q ν (f := fun z => ‖z‖ₑ) measurable_id.enorm
      (w := fun N => ‖degWeight N‖ₑ) measurable_degWeight.enorm
  have hlt : (∫⁻ z, ‖z‖ₑ ∂ν) * (∫⁻ N, ‖degWeight N‖ₑ ∂Q) < ⊤ := by
    rw [← hfac]
    have heq : ∀ M : RWRS.Net 1, ‖RWRS.netConfig M (RWRS.netRoot M)‖ₑ
        * ‖degWeight (RWRS.forgetMarks M)‖ₑ = ‖|RWRS.netWeightedMass M|‖ₑ := by
      intro M
      rw [← enorm_mul, ← netWeightedMass_eq_mul]
      simp
    simp only [heq]
    exact hint.2
  by_contra hcon
  rw [HasFiniteIntegral] at hcon
  push Not at hcon
  have htop : (∫⁻ z, ‖z‖ₑ ∂ν) = ⊤ := top_le_iff.mp hcon
  rw [htop, ENNReal.top_mul (lintegral_degWeight_ne_zero Q hgood)] at hlt
  exact absurd hlt (by simp)

/-- Every mark of an i.i.d. marked network almost surely lies where the mark law
does. -/
theorem ae_netConfig_mem (Q : Measure (RWRS.Net 0)) [IsProbabilityMeasure Q]
    (ν : Measure ℝ) [IsProbabilityMeasure ν] {s : Set ℝ} (hs : MeasurableSet s)
    (h : ∀ᵐ z ∂ν, z ∈ s) :
    ∀ᵐ M ∂(RWRS.markIid Q ν), ∀ v : ℕ, RWRS.netConfig M v ∈ s := by
  haveI := instIsProbabilityMeasureIidLaw (V := ℕ) ν
  have hset : MeasurableSet {M : RWRS.Net 1 | ∀ v : ℕ, RWRS.netConfig M v ∈ s} := by
    have : {M : RWRS.Net 1 | ∀ v : ℕ, RWRS.netConfig M v ∈ s}
        = ⋂ v : ℕ, {M : RWRS.Net 1 | RWRS.netConfig M v ∈ s} := by
      ext M; simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rw [this]
    refine MeasurableSet.iInter fun v => ?_
    exact ((measurable_pi_apply (0 : Fin 1)).comp
      ((measurable_pi_apply v).comp (measurable_snd.comp measurable_snd))) hs
  rw [markIid_eq_map, ae_map_iff measurable_markMap.aemeasurable hset]
  have hprod : ∀ᵐ p ∂(Q.prod (RWRS.iidLaw ℕ ν)), ∀ v : ℕ, p.2 v ∈ s :=
    Measure.quasiMeasurePreserving_snd.ae (ae_all_mem (ι := ℕ) ν hs h)
  filter_upwards [hprod] with p hp using hp

end RWRS.Support
