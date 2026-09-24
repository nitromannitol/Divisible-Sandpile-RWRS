/-
Summation over the scales for `prop:poly-growth`, and the two bridges the
assembly needs.

`rwrs.tex:1341`: "which is summable in `k`".  Both contributions at the `k`-th
scale are a polynomial in the block length `N = 2^{k+1}` against a factor that
decays: a stretched exponential `exp(-cN^θ)` for the good walk and for the
displacement, and a negative power for the local-time failure.  Each is below a
constant multiple of `2^{-k}`, so the series converges.  The two bridges are the
mean of the truncated marginal, which dominates the mean of every level-capped
coordinate, and the walk average of the payoff on the scenery event.
-/
import RWRS.Support.SubPolyExit

namespace RWRS.Support

open MeasureTheory
open scoped ENNReal Classical

/-- **A polynomial in the block length against a stretched exponential is
geometrically small in the scale.** -/
theorem exists_geom_bound {A CB c θ : ℝ} (hCB : 0 ≤ CB) (hc : 0 < c) (hθ : 0 < θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) (Y E : ℝ),
      Y ≤ CB * (2 ^ (k + 1) : ℝ) ^ A * Real.exp (-E) →
      c * (2 ^ (k + 1) : ℝ) ^ θ ≤ E →
      Y ≤ C * (1 / 2 : ℝ) ^ k := by
  obtain ⟨C0, hC00, hC0⟩ := rpow_mul_exp_neg_le (A := A) hc hθ
  refine ⟨CB * C0, by positivity, fun k Y E hY hE => ?_⟩
  have hN1 : (1:ℝ) ≤ (2 ^ (k + 1) : ℝ) := one_le_pow₀ (by norm_num)
  have hN0 : (0:ℝ) < (2 ^ (k + 1) : ℝ) := lt_of_lt_of_le zero_lt_one hN1
  have h1 : Real.exp (-E) ≤ Real.exp (-(c * (2 ^ (k + 1) : ℝ) ^ θ)) :=
    Real.exp_le_exp.2 (by linarith)
  have h2 : (2 ^ (k + 1) : ℝ) ^ A * Real.exp (-E)
      ≤ (2 ^ (k + 1) : ℝ) ^ A * Real.exp (-(c * (2 ^ (k + 1) : ℝ) ^ θ)) :=
    mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hN0.le A)
  have h3 : (2 ^ (k + 1) : ℝ) ^ A * Real.exp (-(c * (2 ^ (k + 1) : ℝ) ^ θ))
      ≤ C0 * (2 ^ (k + 1) : ℝ) ^ (-(1:ℝ)) := hC0 _ hN1
  have hpk : (0:ℝ) < (2:ℝ) ^ k := by positivity
  have he : ((2:ℝ)) ^ k ≤ (2:ℝ) ^ (k + 1) := by
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have h4 : (2 ^ (k + 1) : ℝ) ^ (-(1:ℝ)) ≤ (1 / 2 : ℝ) ^ k := by
    rw [Real.rpow_neg_one, one_div, inv_pow]
    exact inv_anti₀ hpk he
  calc Y ≤ CB * (2 ^ (k + 1) : ℝ) ^ A * Real.exp (-E) := hY
    _ = CB * ((2 ^ (k + 1) : ℝ) ^ A * Real.exp (-E)) := by ring
    _ ≤ CB * (C0 * (2 ^ (k + 1) : ℝ) ^ (-(1:ℝ))) :=
        mul_le_mul_of_nonneg_left (le_trans h2 h3) hCB
    _ = CB * C0 * (2 ^ (k + 1) : ℝ) ^ (-(1:ℝ)) := by ring
    _ ≤ CB * C0 * (1 / 2 : ℝ) ^ k := mul_le_mul_of_nonneg_left h4 (by positivity)

/-- **A power of the block length below `-1` is geometrically small in the
scale.** -/
theorem rpow_le_geom {A : ℝ} (hA : A ≤ -1) (k : ℕ) :
    (2 ^ (k + 1) : ℝ) ^ A ≤ (1 / 2 : ℝ) ^ k := by
  have hN1 : (1:ℝ) ≤ (2 ^ (k + 1) : ℝ) := one_le_pow₀ (by norm_num)
  have hpk : (0:ℝ) < (2:ℝ) ^ k := by positivity
  have he : ((2:ℝ)) ^ k ≤ (2:ℝ) ^ (k + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have h1 : (2 ^ (k + 1) : ℝ) ^ A ≤ (2 ^ (k + 1) : ℝ) ^ (-(1:ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  refine le_trans h1 ?_
  rw [Real.rpow_neg_one, one_div, inv_pow]
  exact inv_anti₀ hpk he

/-- The lower truncation puts no mass below its level. -/
theorem ae_neg_le_map_lowTrunc (ν : Measure ℝ) (M : ℝ) :
    ∀ᵐ z ∂(ν.map (lowTrunc M)), -M ≤ z := by
  rw [MeasureTheory.ae_iff]
  have hs : {z : ℝ | ¬ (-M ≤ z)} = Set.Iio (-M) := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_Iio, not_le]
  rw [hs, MeasureTheory.Measure.map_apply (measurable_lowTrunc M) measurableSet_Iio]
  have hpre : (lowTrunc M) ⁻¹' (Set.Iio (-M)) = (∅ : Set ℝ) := by
    ext z
    simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_empty_iff_false, iff_false, not_lt,
      lowTrunc]
    exact le_max_right z (-M)
  rw [hpre, MeasureTheory.measure_empty]

/-- **The recentring is legitimate**: capping a coordinate of the truncated
marginal at any level can only lower its mean. -/
theorem siteMean_le_of_lowTrunc (ν : Measure ℝ) [IsProbabilityMeasure ν] {M m t : ℝ}
    (ht : -M ≤ t) (hint : Integrable (fun z : ℝ => z) (ν.map (lowTrunc M)))
    (hm : ∫ z, z ∂(ν.map (lowTrunc M)) = m) :
    siteMean (ν.map (lowTrunc M)) M t ≤ m := by
  haveI : IsProbabilityMeasure (ν.map (lowTrunc M)) :=
    Measure.isProbabilityMeasure_map (measurable_lowTrunc M).aemeasurable
  have hae : ∀ᵐ z ∂(ν.map (lowTrunc M)), siteVal M t z ≤ z := by
    filter_upwards [ae_neg_le_map_lowTrunc ν M] with z hz
    have hlt : lowTrunc M z = z := max_eq_left hz
    rw [siteVal, hlt]
    exact min_le_left z t
  rw [siteMean, ← hm]
  exact integral_mono_ae (integrable_siteVal _ ht) hint hae

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite] {ρ : Measure ℝ}
variable [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]

/-- **The walk average of the payoff is finite on the scenery event.** -/
theorem ae_lintegral_supPayoff_ne_top_of_lintegral [Infinite V] [IsProbabilityMeasure ρ]
    (_hG : G.Connected) {M m : ℝ} {t : V → ℝ} (hc : ∀ v : V, siteMean ρ M (t v) ≤ m) (o : V)
    (hfin : (∫⁻ z, RWRS.supPayoff G (zetaField ρ M m t z.1) z.2
        ∂(RWRS.jointLaw G ρ o)) ≠ ⊤) :
    ∀ᵐ ξ ∂(RWRS.iidLaw V ρ), (∀ v : V, ξ v ≤ t v) →
      (∫⁻ X, RWRS.supPayoff G ξ X ∂(RWRS.walkLaw G o)) ≠ ⊤ := by
  haveI : IsProbabilityMeasure (RWRS.walkLaw G o) := by rw [walkLaw_eq_lib]; infer_instance
  haveI : IsProbabilityMeasure (RWRS.iidLaw V ρ) := instIsProbabilityMeasureIid ρ
  have hmeas : Measurable fun z : (V → ℝ) × (ℕ → V) =>
      RWRS.supPayoff G (zetaField ρ M m t z.1) z.2 := by
    have h := (measurable_supPayoff_prod (G := G)).comp (measurable_zetaField_prod ρ M m t)
    simpa [Function.comp_def] using h
  have hswap := lintegral_jointLaw_eq (G := G) ρ o hmeas
  rw [hswap] at hfin
  have hmeasg : Measurable fun ξ : V → ℝ =>
      ∫⁻ X, RWRS.supPayoff G (zetaField ρ M m t ξ) X ∂(RWRS.walkLaw G o) := by
    have h := hmeas.lintegral_prod_right' (ν := RWRS.walkLaw G o)
    exact h
  have h4 := ae_lt_top hmeasg hfin
  filter_upwards [h4] with ξ hξ
  intro hle
  have h2 : (∫⁻ X, RWRS.supPayoff G ξ X ∂(RWRS.walkLaw G o))
      ≤ ∫⁻ X, RWRS.supPayoff G (zetaField ρ M m t ξ) X ∂(RWRS.walkLaw G o) :=
    lintegral_mono fun X => supPayoff_le_zetaField hc hle X
  exact ne_of_lt (lt_of_le_of_lt h2 hξ)

end RWRS.Support
