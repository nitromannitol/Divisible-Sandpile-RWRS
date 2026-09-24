/-
The Paley--Zygmund inequality, used twice in `rwrs.tex`: in
`lem:positive-part` and again in `prop:critical`.
-/
import RWRS.Setting
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory

namespace RWRS.Support

theorem paley_zygmund {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (Z : Ω → ℝ) (hZ0 : ∀ ω, 0 ≤ Z ω)
    (hZ : Integrable Z P) (hZ2 : Integrable (fun ω => Z ω ^ 2) P)
    (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hA : MeasurableSet {ω | θ * ∫ ω, Z ω ∂P ≤ Z ω}) :
    (1 - θ) ^ 2 * (∫ ω, Z ω ∂P) ^ 2
      ≤ (∫ ω, Z ω ^ 2 ∂P) * (P {ω | θ * ∫ ω, Z ω ∂P ≤ Z ω}).toReal := by
  classical
  set m := ∫ ω, Z ω ∂P with hm
  set A := {ω | θ * m ≤ Z ω} with hAdef
  have hm0 : 0 ≤ m := integral_nonneg hZ0
  have hPA : (0 : ℝ) ≤ (P A).toReal := ENNReal.toReal_nonneg
  -- (a) the event carries at least `(1-θ)m`
  have hsplit : ∫ ω in A, Z ω ∂P + ∫ ω in Aᶜ, Z ω ∂P = m := integral_add_compl hA hZ
  have hcompl : ∫ ω in Aᶜ, Z ω ∂P ≤ θ * m := by
    have hle : ∀ ω ∈ Aᶜ, Z ω ≤ θ * m := by
      intro ω hω
      simp only [hAdef, Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hω
      exact hω.le
    calc ∫ ω in Aᶜ, Z ω ∂P ≤ ∫ _ω in Aᶜ, θ * m ∂P :=
          setIntegral_mono_on hZ.integrableOn integrableOn_const hA.compl hle
      _ = (P Aᶜ).toReal * (θ * m) := by rw [setIntegral_const, smul_eq_mul, measureReal_def]
      _ ≤ 1 * (θ * m) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact ENNReal.toReal_le_of_le_ofReal (by norm_num)
            (by rw [ENNReal.ofReal_one]; exact prob_le_one)
      _ = θ * m := by ring
  have ha : (1 - θ) * m ≤ ∫ ω in A, Z ω ∂P := by nlinarith [hsplit, hcompl]
  -- (b) Cauchy-Schwarz against the indicator
  have hind : (fun ω => Set.indicator A (fun _ => (1 : ℝ)) ω) = A.indicator 1 := rfl
  have hg2 : ∀ ω, (A.indicator (fun _ => (1 : ℝ)) ω) ^ 2
      = A.indicator (fun _ => (1 : ℝ)) ω := by
    intro ω
    by_cases h : ω ∈ A <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]
  have hgint : Integrable (A.indicator fun _ => (1 : ℝ)) P :=
    (integrable_const (1 : ℝ)).indicator hA
  have hgmem : MemLp (A.indicator fun _ => (1 : ℝ)) 2 P := by
    refine (memLp_two_iff_integrable_sq hgint.aestronglyMeasurable).mpr ?_
    exact hgint.congr (by filter_upwards with ω using (hg2 ω).symm)
  have hZmem : MemLp Z 2 P := (memLp_two_iff_integrable_sq hZ.aestronglyMeasurable).mpr hZ2
  have hprod : ∫ ω, Z ω * A.indicator (fun _ => (1 : ℝ)) ω ∂P = ∫ ω in A, Z ω ∂P := by
    rw [← integral_indicator hA]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    by_cases h : ω ∈ A <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]
  have hCS : ∫ ω in A, Z ω ∂P
      ≤ (∫ ω, Z ω ^ (2 : ℝ) ∂P) ^ (1 / (2 : ℝ))
        * (∫ ω, (A.indicator (fun _ => (1 : ℝ)) ω) ^ (2 : ℝ) ∂P) ^ (1 / (2 : ℝ)) := by
    rw [← hprod]
    refine integral_mul_le_Lp_mul_Lq_of_nonneg (Real.HolderConjugate.two_two)
      (Filter.Eventually.of_forall hZ0)
      (Filter.Eventually.of_forall fun ω => Set.indicator_nonneg (fun _ _ => zero_le_one) ω)
      (by simpa using hZmem) (by simpa using hgmem)
  have hE2 : ∫ ω, Z ω ^ (2 : ℝ) ∂P = ∫ ω, Z ω ^ 2 ∂P := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    show Z ω ^ (2 : ℝ) = Z ω ^ 2
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
  have hIA : ∫ ω, (A.indicator (fun _ => (1 : ℝ)) ω) ^ (2 : ℝ) ∂P = (P A).toReal := by
    have hpt : ∀ ω, (A.indicator (fun _ => (1 : ℝ)) ω) ^ (2 : ℝ)
        = A.indicator (fun _ => (1 : ℝ)) ω := by
      intro ω
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
      exact hg2 ω
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_indicator hA,
      setIntegral_const, smul_eq_mul, mul_one, measureReal_def]
  rw [hE2, hIA] at hCS
  have hnn1 : (0 : ℝ) ≤ ∫ ω, Z ω ^ 2 ∂P := integral_nonneg fun ω => sq_nonneg _
  have hfin : (1 - θ) * m
      ≤ (∫ ω, Z ω ^ 2 ∂P) ^ (1 / (2 : ℝ)) * ((P A).toReal) ^ (1 / (2 : ℝ)) := ha.trans hCS
  have hlhs : (0 : ℝ) ≤ (1 - θ) * m := mul_nonneg (by linarith) hm0
  have hsq : ((∫ ω, Z ω ^ 2 ∂P) ^ (1 / (2 : ℝ)) * ((P A).toReal) ^ (1 / (2 : ℝ))) ^ 2
      = (∫ ω, Z ω ^ 2 ∂P) * (P A).toReal := by
    rw [mul_pow, ← Real.rpow_natCast ((∫ ω, Z ω ^ 2 ∂P) ^ (1 / (2 : ℝ))) 2,
      ← Real.rpow_natCast (((P A).toReal) ^ (1 / (2 : ℝ))) 2,
      ← Real.rpow_mul hnn1, ← Real.rpow_mul hPA]
    norm_num
  have hpow : ((1 - θ) * m) ^ 2
      ≤ ((∫ ω, Z ω ^ 2 ∂P) ^ (1 / (2 : ℝ)) * ((P A).toReal) ^ (1 / (2 : ℝ))) ^ 2 := by
    have hb : (0 : ℝ) ≤ (∫ ω, Z ω ^ 2 ∂P) ^ (1 / (2 : ℝ)) * ((P A).toReal) ^ (1 / (2 : ℝ)) :=
      le_trans hlhs hfin
    nlinarith [hfin, hlhs, hb]
  rw [hsq, mul_pow] at hpow
  exact hpow

end RWRS.Support
