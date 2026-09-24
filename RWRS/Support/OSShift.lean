/-
The change of variable between a mass field and its excess, which is what turns
the optimal stopping theorem into the explosion theorem.
-/
import RWRS.Support.OSParts
import RWRS.Frozen.RWInfinite
import RWRS.Support.ErgSubFinal
import RWRS.Support.Explosion
import RWRS.Support.Truncation
import RWRS.Support.SubStab

namespace RWRS.Support

open MeasureTheory Filter
open scoped ENNReal Topology

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

theorem measurable_excess : Measurable (fun σ : V → ℝ => RWRS.excess σ) :=
  measurable_pi_lambda _ fun v => (measurable_pi_apply v).sub_const 1

/-- **The excess of an i.i.d. field is i.i.d. with the shifted marginal.** -/
theorem map_excess_iidLaw (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    Measure.map (fun σ : V → ℝ => RWRS.excess σ) (RWRS.iidLaw V ν)
      = RWRS.iidLaw V (ν.map (fun z : ℝ => z - 1)) := by
  have hfun : (fun σ : V → ℝ => RWRS.excess σ)
      = fun (x : V → ℝ) (_i : V) => (fun z : ℝ => z - 1) (x _i) := rfl
  rw [RWRS.iidLaw, RWRS.iidLaw, hfun]
  exact Measure.infinitePi_map_pi _ fun _ => measurable_id.sub_const 1

/-- **Explosion of the excess is non-stabilization.** -/
theorem measure_stabilizes_eq_zero [Infinite V] (hG : G.Connected) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (x : V)
    (h : ∀ᵐ ξ ∂(RWRS.iidLaw V (ν.map (fun z : ℝ => z - 1))), RWRS.supStopValue G ξ x = ⊤) :
    RWRS.iidLaw V ν {σ : V → ℝ | RWRS.Stabilizes G σ} = 0 := by
  set A : Set (V → ℝ) := {ξ : V → ℝ | RWRS.supStopValue G ξ x = ⊤} with hA
  have hAm : MeasurableSet A :=
    (measurable_supStopValue hG x) (measurableSet_singleton ⊤)
  have hsub : {σ : V → ℝ | RWRS.Stabilizes G σ}
      ⊆ (fun σ : V → ℝ => RWRS.excess σ) ⁻¹' Aᶜ := by
    intro σ hσ
    have h1 : RWRS.odometerLimit G σ x ≠ ⊤ := hσ x
    rw [RWRS.Frozen.rwInfinite hG σ x] at h1
    exact h1
  have hzero : RWRS.iidLaw V (ν.map (fun z : ℝ => z - 1)) Aᶜ = 0 := by
    rw [MeasureTheory.ae_iff] at h
    exact h
  refine le_antisymm ?_ bot_le
  calc RWRS.iidLaw V ν {σ : V → ℝ | RWRS.Stabilizes G σ}
      ≤ RWRS.iidLaw V ν ((fun σ : V → ℝ => RWRS.excess σ) ⁻¹' Aᶜ) := measure_mono hsub
    _ = (Measure.map (fun σ : V → ℝ => RWRS.excess σ) (RWRS.iidLaw V ν)) Aᶜ :=
        (Measure.map_apply measurable_excess hAm.compl).symm
    _ = RWRS.iidLaw V (ν.map (fun z : ℝ => z - 1)) Aᶜ := by rw [map_excess_iidLaw]
    _ = 0 := hzero

/-! ### The extended mean of the shifted law -/

variable {ν : Measure ℝ}

theorem measurable_sub_one : Measurable (fun z : ℝ => z - 1) := by fun_prop

theorem negPart_map_ne_top [IsProbabilityMeasure ν] (h : RWRS.negPart ν ≠ ⊤) :
    RWRS.negPart (ν.map (fun z : ℝ => z - 1)) ≠ ⊤ := negPart_map_sub_one_ne_top ν h

theorem posPart_le_map_sub_one [IsProbabilityMeasure ν] :
    RWRS.posPart ν ≤ RWRS.posPart (ν.map (fun z : ℝ => z - 1)) + 1 := by
  rw [posPart_map_sub_one]
  calc RWRS.posPart ν = ∫⁻ z, ENNReal.ofReal z ∂ν := rfl
    _ ≤ ∫⁻ z, (ENNReal.ofReal (z - 1) + 1) ∂ν := by
        refine lintegral_mono fun z => ?_
        have hz : ENNReal.ofReal z ≤ ENNReal.ofReal (z - 1) + ENNReal.ofReal 1 := by
          have he : z = (z - 1) + 1 := by ring
          calc ENNReal.ofReal z = ENNReal.ofReal ((z - 1) + 1) := by rw [← he]
            _ ≤ _ := ENNReal.ofReal_add_le
        rwa [ENNReal.ofReal_one] at hz
    _ = (∫⁻ z, ENNReal.ofReal (z - 1) ∂ν) + 1 := by
        rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]

theorem posPart_ne_top_of_extMean_coe {c : ℝ} (h : RWRS.extMean ν = (c : EReal)) :
    RWRS.posPart ν ≠ ⊤ := by
  intro hp
  rw [RWRS.extMean, hp, EReal.coe_ennreal_top] at h
  rcases eq_or_ne (RWRS.negPart ν) ⊤ with hn | hn
  · rw [hn, EReal.coe_ennreal_top] at h; simp at h
  · rw [EReal.top_sub (by simpa using hn)] at h; simp at h

theorem negPart_ne_top_of_extMean_coe {c : ℝ} (h : RWRS.extMean ν = (c : EReal)) :
    RWRS.negPart ν ≠ ⊤ := by
  intro hn
  rw [RWRS.extMean, hn, EReal.coe_ennreal_top] at h
  rcases eq_or_ne (RWRS.posPart ν) ⊤ with hp | hp
  · rw [hp, EReal.coe_ennreal_top] at h; simp at h
  · rw [EReal.sub_top] at h; simp at h

theorem isProbabilityMeasure_map_sub_one [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (ν.map (fun z : ℝ => z - 1)) := by
  constructor
  rw [Measure.map_apply measurable_sub_one MeasurableSet.univ]
  simp

theorem integrable_map_sub_one [IsProbabilityMeasure ν] (hint : Integrable (fun z : ℝ => z) ν) :
    Integrable (fun z : ℝ => z) (ν.map (fun z : ℝ => z - 1)) := by
  have hmm : AEStronglyMeasurable (fun z : ℝ => z) (ν.map (fun z : ℝ => z - 1)) :=
    aestronglyMeasurable_id
  rw [integrable_map_measure hmm measurable_sub_one.aemeasurable]
  exact hint.sub (integrable_const 1)

theorem integral_map_sub_one [IsProbabilityMeasure ν] (hint : Integrable (fun z : ℝ => z) ν) :
    ∫ z, z ∂(ν.map (fun z : ℝ => z - 1)) = (∫ z, z ∂ν) - 1 := by
  have hmm : AEStronglyMeasurable (fun z : ℝ => z) (ν.map (fun z : ℝ => z - 1)) :=
    aestronglyMeasurable_id
  rw [integral_map measurable_sub_one.aemeasurable hmm,
    integral_sub hint (integrable_const 1)]
  simp

/-- **The excess of a law of mean one is centred.** -/
theorem extMean_map_sub_one_eq_zero [IsProbabilityMeasure ν] (h : RWRS.extMean ν = 1) :
    RWRS.extMean (ν.map (fun z : ℝ => z - 1)) = 0 := by
  have hc : RWRS.extMean ν = ((1 : ℝ) : EReal) := by rw [h]; rfl
  have hp := posPart_ne_top_of_extMean_coe hc
  have hn := negPart_ne_top_of_extMean_coe hc
  have hint := integrable_id_of_finite hp hn
  have hm : ∫ z, z ∂ν = 1 := by
    have hh := extMean_eq_integral_of_integrable ν hint
    rw [hc] at hh
    exact_mod_cast hh.symm
  haveI := isProbabilityMeasure_map_sub_one (ν := ν)
  rw [extMean_eq_integral_of_integrable _ (integrable_map_sub_one hint),
    integral_map_sub_one hint, hm]
  simp

/-- **A law of mean above one has a finite negative part.** -/
theorem negPart_ne_top_of_one_lt (hdet : RWRS.HasExtMean ν) (h : 1 < RWRS.extMean ν) :
    RWRS.negPart ν ≠ ⊤ := by
  intro hn
  rcases hdet with hp0 | hp0
  · rw [RWRS.extMean, hn, EReal.coe_ennreal_top, EReal.sub_top] at h
    simp at h
  · exact hp0 hn

/-- **The excess of a law of mean above one has positive mean.** -/
theorem extMean_map_sub_one_pos [IsProbabilityMeasure ν] (hdet : RWRS.HasExtMean ν)
    (h : 1 < RWRS.extMean ν) : 0 < RWRS.extMean (ν.map (fun z : ℝ => z - 1)) := by
  haveI := isProbabilityMeasure_map_sub_one (ν := ν)
  have hn : RWRS.negPart ν ≠ ⊤ := negPart_ne_top_of_one_lt hdet h
  by_cases hp : RWRS.posPart ν = ⊤
  · have hp' : RWRS.posPart (ν.map (fun z : ℝ => z - 1)) = ⊤ := by
      by_contra hcon
      have hfin : RWRS.posPart (ν.map (fun z : ℝ => z - 1)) + 1 ≠ ⊤ := by
        simp [hcon]
      exact absurd hp (ne_top_of_le_ne_top hfin (posPart_le_map_sub_one (ν := ν)))
    have hn' := negPart_map_ne_top (ν := ν) hn
    rw [RWRS.extMean, hp', EReal.coe_ennreal_top, EReal.top_sub (by simpa using hn')]
    simp
  · have hint := integrable_id_of_finite hp hn
    have hm : ((1 : ℝ) : EReal) < ((∫ z, z ∂ν : ℝ) : EReal) := by
      rw [← extMean_eq_integral_of_integrable ν hint]
      exact h
    have hm' : (1 : ℝ) < ∫ z, z ∂ν := by exact_mod_cast hm
    rw [extMean_eq_integral_of_integrable _ (integrable_map_sub_one hint),
      integral_map_sub_one hint]
    have hpos : (0 : ℝ) < (∫ z, z ∂ν) - 1 := by linarith
    exact_mod_cast hpos

/-! ### The variance of the shifted law -/

theorem evar_map_sub_one [IsProbabilityMeasure ν] (hsq : RWRS.evar ν < ⊤) :
    RWRS.evar (ν.map (fun z : ℝ => z - 1)) = RWRS.evar ν := by
  haveI := isProbabilityMeasure_map_sub_one (ν := ν)
  have hid : RWRS.evar ν = ProbabilityTheory.evariance (fun z : ℝ => z) ν := rfl
  have hid' : RWRS.evar (ν.map (fun z : ℝ => z - 1))
      = ProbabilityTheory.evariance (fun z : ℝ => z) (ν.map (fun z : ℝ => z - 1)) := rfl
  have hmeanmap : ∫ z, z ∂(ν.map (fun z : ℝ => z - 1)) = ∫ z, (z - 1) ∂ν := by
    have hmm : AEStronglyMeasurable (fun z : ℝ => z) (ν.map (fun z : ℝ => z - 1)) :=
      aestronglyMeasurable_id
    rw [integral_map measurable_sub_one.aemeasurable hmm]
  have hchange : ProbabilityTheory.evariance (fun z : ℝ => z) (ν.map (fun z : ℝ => z - 1))
      = ProbabilityTheory.evariance (fun z : ℝ => z - 1) ν := by
    rw [ProbabilityTheory.evariance_eq_lintegral_ofReal,
      ProbabilityTheory.evariance_eq_lintegral_ofReal, hmeanmap]
    refine lintegral_map ?_ measurable_sub_one
    exact ENNReal.measurable_ofReal.comp ((measurable_id.sub_const _).pow_const 2)
  have hasm : AEStronglyMeasurable (fun z : ℝ => z) ν := aestronglyMeasurable_id
  have hmem : MemLp (fun z : ℝ => z) 2 ν :=
    (ProbabilityTheory.evariance_lt_top_iff_memLp hasm).1 hsq
  have hmem' : MemLp (fun z : ℝ => z - 1) 2 ν := hmem.sub (memLp_const 1)
  rw [hid, hid', hchange, ← ProbabilityTheory.ofReal_variance hmem',
    ← ProbabilityTheory.ofReal_variance hmem,
    ProbabilityTheory.variance_sub_const hasm 1]

/-- **The excess of a law that is not a unit mass at one is not a unit mass at
zero.** -/
theorem map_sub_one_ne_dirac [IsProbabilityMeasure ν] (h : ν ≠ Measure.dirac 1) :
    ν.map (fun z : ℝ => z - 1) ≠ Measure.dirac 0 := by
  intro hcon
  refine h ?_
  have hback : (ν.map (fun z : ℝ => z - 1)).map (fun z : ℝ => z + 1) = ν := by
    rw [Measure.map_map (by fun_prop : Measurable fun z : ℝ => z + 1) measurable_sub_one]
    have hcomp : ((fun z : ℝ => z + 1) ∘ (fun z : ℝ => z - 1)) = id := by
      funext z
      simp
    rw [hcomp, Measure.map_id]
  rw [hcon] at hback
  rw [← hback]
  have hd := MeasureTheory.Measure.map_dirac (f := fun z : ℝ => z + 1) (0 : ℝ)
  rw [hd]
  norm_num

end RWRS.Support
