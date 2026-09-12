/-
Step 3 of `lem:moment-sharpness`: the background is above `-t` with probability
at least three quarters.

The centred marginal splits at a level `M` into a bounded part and a tail part.
The tail part has small mean absolute value, so Markov's inequality controls the
weighted tail sum; the recentred bounded part is a weighted sum of independent
centred variables of size at most `2M`, so its variance is at most `4M²` times
the sum of the squared weights and Chebyshev's inequality controls it.  The
displacement of the mean caused by the recentring is the mean of the tail part
again, so it is small as well.
-/
import RWRS.Support.Critical
import RWRS.Support.Background
import RWRS.Support.MomentIneq
import Mathlib.MeasureTheory.Function.UniformIntegrable

namespace RWRS.Support

open MeasureTheory
open scoped ENNReal

variable {V : Type*}

/-- The tail part of the centred marginal at level `M`. -/
noncomputable def tailPart (μ M : ℝ) (z : ℝ) : ℝ := if M ≤ |z - μ| then z - μ else 0

/-- The bounded part of the centred marginal at level `M`. -/
noncomputable def bddPart (μ M : ℝ) (z : ℝ) : ℝ := (z - μ) - tailPart μ M z

theorem tailPart_add_bddPart (μ M z : ℝ) : tailPart μ M z + bddPart μ M z = z - μ := by
  rw [bddPart]; ring

theorem abs_bddPart_le {M : ℝ} (hM : 0 ≤ M) (μ z : ℝ) : |bddPart μ M z| ≤ M := by
  rw [bddPart, tailPart]
  by_cases h : M ≤ |z - μ|
  · simp only [h, if_pos, sub_self, abs_zero]
    exact hM
  · simp only [h, if_false, sub_zero]
    exact le_of_lt (lt_of_not_ge h)

theorem abs_tailPart_le (μ M z : ℝ) : |tailPart μ M z| ≤ |z - μ| := by
  rw [tailPart]
  by_cases h : M ≤ |z - μ| <;> simp [h, abs_nonneg]

theorem measurable_tailPart (μ M : ℝ) : Measurable (tailPart μ M) := by
  classical
  refine Measurable.ite ?_ (measurable_id.sub_const μ) measurable_const
  exact measurableSet_le measurable_const (by fun_prop)

theorem measurable_bddPart (μ M : ℝ) : Measurable (bddPart μ M) :=
  (measurable_id.sub_const μ).sub (measurable_tailPart μ M)

theorem integrable_tailPart {ν : Measure ℝ} [IsProbabilityMeasure ν] (μ M : ℝ)
    (hint : Integrable (fun z => z - μ) ν) : Integrable (tailPart μ M) ν := by
  refine Integrable.mono' hint.abs (measurable_tailPart μ M).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs]
  exact abs_tailPart_le μ M z

theorem integrable_bddPart {ν : Measure ℝ} [IsProbabilityMeasure ν] (μ M : ℝ)
    (hint : Integrable (fun z => z - μ) ν) : Integrable (bddPart μ M) ν :=
  hint.sub (integrable_tailPart μ M hint)

/-- The recentred bounded part, of mean zero and size at most `2M`. -/
noncomputable def ctrPart (ν : Measure ℝ) (μ M : ℝ) (z : ℝ) : ℝ :=
  bddPart μ M z - ∫ y, bddPart μ M y ∂ν

theorem measurable_ctrPart (ν : Measure ℝ) (μ M : ℝ) : Measurable (ctrPart ν μ M) :=
  (measurable_bddPart μ M).sub_const _

theorem integral_ctrPart {ν : Measure ℝ} [IsProbabilityMeasure ν] (μ M : ℝ)
    (hint : Integrable (fun z => z - μ) ν) : ∫ z, ctrPart ν μ M z ∂ν = 0 := by
  simp only [ctrPart]
  rw [integral_sub (integrable_bddPart μ M hint) (integrable_const _), integral_const]
  simp

theorem abs_ctrPart_le {ν : Measure ℝ} [IsProbabilityMeasure ν] {M : ℝ} (hM : 0 ≤ M) (μ : ℝ)
    (hint : Integrable (fun z => z - μ) ν) (z : ℝ) : |ctrPart ν μ M z| ≤ 2 * M := by
  have hc : |∫ y, bddPart μ M y ∂ν| ≤ M := by
    refine le_trans (abs_integral_le_integral_abs) ?_
    have := integral_mono (integrable_bddPart μ M hint).abs (integrable_const M)
      (fun y => abs_bddPart_le hM μ y)
    simpa using this
  have := abs_bddPart_le hM μ z
  simp only [ctrPart]
  calc |bddPart μ M z - ∫ y, bddPart μ M y ∂ν|
      ≤ |bddPart μ M z| + |∫ y, bddPart μ M y ∂ν| := abs_sub _ _
    _ ≤ M + M := add_le_add this hc
    _ = 2 * M := by ring

/-- The mean of the bounded part is minus the mean of the tail part. -/
theorem abs_integral_bddPart_le {ν : Measure ℝ} [IsProbabilityMeasure ν] {μ : ℝ}
    (hint : Integrable (fun z => z - μ) ν) (hmean : ∫ z, (z - μ) ∂ν = 0) (M : ℝ) :
    |∫ z, bddPart μ M z ∂ν| ≤ ∫ z, |tailPart μ M z| ∂ν := by
  have hsplit : ∫ z, bddPart μ M z ∂ν = -∫ z, tailPart μ M z ∂ν := by
    have : ∫ z, bddPart μ M z ∂ν
        = (∫ z, (z - μ) ∂ν) - ∫ z, tailPart μ M z ∂ν := by
      simp only [bddPart]
      exact integral_sub hint (integrable_tailPart μ M hint)
    rw [this, hmean, zero_sub]
  rw [hsplit, abs_neg]
  exact abs_integral_le_integral_abs

theorem exists_tailPart_le {ν : Measure ℝ} [IsProbabilityMeasure ν] (μ : ℝ)
    (hint : Integrable (fun z => z - μ) ν) {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ, 0 ≤ M ∧ ∫ z, |tailPart μ M z| ∂ν ≤ ε := by
  have hmem : MemLp (fun z : ℝ => z - μ) 1 ν := (memLp_one_iff_integrable).2 hint
  obtain ⟨M, hM0, hM⟩ := hmem.integral_indicator_norm_ge_nonneg_le hε
  refine ⟨M, hM0, ?_⟩
  have hid : ∀ z : ℝ,
      ({z : ℝ | M ≤ ‖z - μ‖₊}.indicator (fun z => z - μ)) z = tailPart μ M z := by
    intro z
    have hmemset : (z ∈ {z : ℝ | M ≤ ‖z - μ‖₊}) ↔ M ≤ |z - μ| := by
      simp [Set.mem_setOf_eq, ← Real.norm_eq_abs]
    by_cases h : M ≤ |z - μ|
    · rw [Set.indicator_of_mem (hmemset.2 h)]
      simp [tailPart, h]
    · rw [Set.indicator_of_notMem (fun hc => h (hmemset.1 hc))]
      simp [tailPart, h]
  simp only [hid] at hM
  have hmeas : AEStronglyMeasurable (fun z => tailPart μ M z) ν :=
    (measurable_tailPart μ M).aestronglyMeasurable
  have heq : ∫ z, ‖tailPart μ M z‖ ∂ν = (∫⁻ z, ‖tailPart μ M z‖ₑ ∂ν).toReal :=
    integral_norm_eq_lintegral_enorm hmeas
  have : ∫ z, |tailPart μ M z| ∂ν = (∫⁻ z, ‖tailPart μ M z‖ₑ ∂ν).toReal := by
    rw [← heq]
    exact integral_congr_ae (Filter.Eventually.of_forall fun z => (Real.norm_eq_abs _).symm)
  rw [this]
  exact ENNReal.toReal_le_of_le_ofReal hε.le hM

/-- **Step 3.**  Off an event of probability at most one quarter the weighted
background is above `-t`. -/
theorem meas_background_small {ν : Measure ℝ} [IsProbabilityMeasure ν] {μ : ℝ}
    (hint : Integrable (fun z => z - μ) ν) (hmean : ∫ z, (z - μ) ∂ν = 0)
    {M : ℝ} (hM : 0 ≤ M) (htail : ∫ z, |tailPart μ M z| ∂ν ≤ 1 / 32)
    (S : Finset V) (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) {t : ℝ} (ht : 0 < t)
    (hW : ∑ v ∈ S, w v ≤ 2 * t)
    (hsq : (∑ v ∈ S, w v ^ 2) * (4 * M ^ 2) ≤ t ^ 2 / 128) :
    RWRS.iidLaw V ν {ξ | ∑ v ∈ S, w v * (ξ v - μ) < -t} ≤ ENNReal.ofReal (1 / 4) := by
  classical
  haveI : IsProbabilityMeasure (RWRS.iidLaw V ν) := instIsProbabilityMeasureIid ν
  set c : ℝ := ∫ z, bddPart μ M z ∂ν with hc
  set T : (V → ℝ) → ℝ := fun ξ => ∑ v ∈ S, w v * tailPart μ M (ξ v) with hT
  set B : (V → ℝ) → ℝ := fun ξ => ∑ v ∈ S, w v * ctrPart ν μ M (ξ v) with hB
  have hWnn : 0 ≤ ∑ v ∈ S, w v := Finset.sum_nonneg fun v _ => hw v
  have hcabs : |c| ≤ 1 / 32 :=
    le_trans (abs_integral_bddPart_le hint hmean M) htail
  -- the pointwise decomposition
  have hdecomp : ∀ ξ : V → ℝ,
      ∑ v ∈ S, w v * (ξ v - μ) = T ξ + B ξ + (∑ v ∈ S, w v) * c := by
    intro ξ
    rw [hT, hB, Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    have h := tailPart_add_bddPart μ M (ξ v)
    simp only [ctrPart, ← hc]
    rw [← h]; ring
  -- the subset relation
  have hsub : {ξ : V → ℝ | ∑ v ∈ S, w v * (ξ v - μ) < -t}
      ⊆ {ξ : V → ℝ | t / 2 ≤ |T ξ|} ∪ {ξ : V → ℝ | t / 4 ≤ |B ξ|} := by
    intro ξ hξ
    by_contra hcon
    rw [Set.mem_union, not_or] at hcon
    have h1 : |T ξ| < t / 2 := lt_of_not_ge (by simpa using hcon.1)
    have h2 : |B ξ| < t / 4 := lt_of_not_ge (by simpa using hcon.2)
    have h3 : |(∑ v ∈ S, w v) * c| ≤ t / 16 := by
      rw [abs_mul, abs_of_nonneg hWnn]
      calc (∑ v ∈ S, w v) * |c| ≤ (2 * t) * (1 / 32) := by
            refine mul_le_mul hW hcabs (abs_nonneg c) (by linarith)
        _ = t / 16 := by ring
    have hlt : ∑ v ∈ S, w v * (ξ v - μ) < -t := hξ
    rw [hdecomp ξ] at hlt
    have := abs_le.1 (le_of_lt h1)
    have := abs_le.1 (le_of_lt h2)
    have := abs_le.1 h3
    linarith [this]
  refine le_trans (measure_mono hsub) ?_
  refine le_trans (measure_union_le _ _) ?_
  have hmT : Measurable T := measurable_weighted_sum S w (measurable_tailPart μ M)
  have hmB : Measurable B := measurable_weighted_sum S w (measurable_ctrPart ν μ M)
  have hiT : Integrable T (RWRS.iidLaw V ν) :=
    integrable_weighted_sum S w (integrable_tailPart μ M hint)
  have hctr2 : Integrable (fun z => ctrPart ν μ M z ^ 2) ν := by
    refine Integrable.mono' (integrable_const ((2 * M) ^ 2))
      ((measurable_ctrPart ν μ M).pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h := abs_ctrPart_le hM μ hint z
    nlinarith [abs_nonneg (ctrPart ν μ M z), sq_abs (ctrPart ν μ M z)]
  have hiB2 : Integrable (fun ξ : V → ℝ => B ξ ^ 2) (RWRS.iidLaw V ν) :=
    (memLp_weighted_sum S w (measurable_ctrPart ν μ M) hctr2).integrable_sq
  -- Markov on the tail part
  have hbd1 : RWRS.iidLaw V ν {ξ : V → ℝ | t / 2 ≤ |T ξ|} ≤ ENNReal.ofReal (1 / 8) := by
    refine le_trans (meas_ge_le_abs_integral T hmT hiT (by linarith)) ?_
    refine ENNReal.ofReal_le_ofReal ?_
    have hint1 : ∫ ξ, |T ξ| ∂(RWRS.iidLaw V ν) ≤ (∑ v ∈ S, w v) * ∫ z, |tailPart μ M z| ∂ν :=
      integral_abs_weighted_le S w hw (integrable_tailPart μ M hint)
    have habs : ∫ z, |tailPart μ M z| ∂ν ≥ 0 := integral_nonneg fun z => abs_nonneg _
    have : ∫ ξ, |T ξ| ∂(RWRS.iidLaw V ν) ≤ (2 * t) * (1 / 32) :=
      le_trans hint1 (mul_le_mul hW htail habs (by linarith))
    rw [div_le_iff₀ (by linarith : (0:ℝ) < t / 2)]
    linarith
  -- Chebyshev on the bounded part
  have hbd2 : RWRS.iidLaw V ν {ξ : V → ℝ | t / 4 ≤ |B ξ|} ≤ ENNReal.ofReal (1 / 8) := by
    refine le_trans (meas_ge_le_sq_integral B hmB hiB2 (by linarith)) ?_
    refine ENNReal.ofReal_le_ofReal ?_
    have hvar : ∫ ξ, B ξ ^ 2 ∂(RWRS.iidLaw V ν) = (∑ v ∈ S, w v ^ 2) * ∫ z, ctrPart ν μ M z ^ 2 ∂ν :=
      integral_weighted_sq S w (measurable_ctrPart ν μ M) hctr2 (integral_ctrPart μ M hint)
    have hbound : ∫ z, ctrPart ν μ M z ^ 2 ∂ν ≤ 4 * M ^ 2 := by
      have := integral_mono hctr2 (integrable_const ((2 * M) ^ 2)) (fun z => by
        have h := abs_ctrPart_le hM μ hint z
        nlinarith [abs_nonneg (ctrPart ν μ M z), sq_abs (ctrPart ν μ M z)])
      simpa using le_trans this (by simp; nlinarith)
    have hsqnn : 0 ≤ ∑ v ∈ S, w v ^ 2 := Finset.sum_nonneg fun v _ => sq_nonneg _
    have hfin : ∫ ξ, B ξ ^ 2 ∂(RWRS.iidLaw V ν) ≤ t ^ 2 / 128 := by
      rw [hvar]
      exact le_trans (mul_le_mul_of_nonneg_left hbound hsqnn) hsq
    rw [div_le_iff₀ (by positivity : (0:ℝ) < (t / 4) ^ 2)]
    nlinarith
  refine le_trans (add_le_add hbd1 hbd2) ?_
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num

end RWRS.Support
