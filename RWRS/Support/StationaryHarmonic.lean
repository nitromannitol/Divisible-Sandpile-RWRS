import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# Bounded harmonic functions of stationary kernels

A bounded harmonic function has equal values at consecutive states under a
stationary law.
-/

namespace RWRS.Support

open MeasureTheory ProbabilityTheory

/-- A bounded harmonic function is constant across almost every stationary transition. -/
theorem ae_eq_of_stationary_harmonic {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν] (P : Kernel α α) [IsMarkovKernel P]
    (hstat : P ∘ₘ ν = ν) {f : α → ℝ} (hf : Measurable f)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ x, |f x| ≤ C)
    (hharm : ∀ x, f x = ∫ y, f y ∂P x) :
    ∀ᵐ p ∂(ν ⊗ₘ P), f p.2 = f p.1 := by
  let J := ν ⊗ₘ P
  haveI : IsProbabilityMeasure J := inferInstance
  let a : α × α → ℝ := fun p => f p.1
  let b : α × α → ℝ := fun p => f p.2
  have ha : Measurable a := hf.comp measurable_fst
  have hb : Measurable b := hf.comp measurable_snd
  have habound (p : α × α) : |a p| ≤ C := hbound p.1
  have hbbound (p : α × α) : |b p| ≤ C := hbound p.2
  have hsqA : Integrable (fun p => a p ^ 2) J := by
    apply Integrable.of_bound (ha.pow_const 2).aestronglyMeasurable (C ^ 2)
    filter_upwards with p
    simp only [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (habound p) 2
  have hsqB : Integrable (fun p => b p ^ 2) J := by
    apply Integrable.of_bound (hb.pow_const 2).aestronglyMeasurable (C ^ 2)
    filter_upwards with p
    simp only [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hbbound p) 2
  have hmul : Integrable (fun p => a p * b p) J := by
    apply Integrable.of_bound (ha.mul hb).aestronglyMeasurable (C ^ 2)
    filter_upwards with p
    change |a p * b p| ≤ C ^ 2
    rw [abs_mul, sq]
    exact mul_le_mul (habound p) (hbbound p) (abs_nonneg _) hC
  have hdiff : Integrable (fun p => (b p - a p) ^ 2) J := by
    have hpoint : (fun p => (b p - a p) ^ 2) =
        ((fun p => b p ^ 2) - (fun p => 2 * (a p * b p))) + (fun p => a p ^ 2) := by
      funext p
      simp only [Pi.add_apply, Pi.sub_apply]
      ring
    rw [hpoint]
    exact (hsqB.sub (hmul.const_mul 2)).add hsqA
  have hf2 : Measurable (fun x => f x ^ 2) := hf.pow_const 2
  have hfirst : (∫ p, a p ^ 2 ∂J) = ∫ x, f x ^ 2 ∂ν := by
    have hi := integral_map (μ := J) measurable_fst.aemeasurable hf2.aestronglyMeasurable
    change (∫ x, f x ^ 2 ∂J.map Prod.fst) = (∫ p, a p ^ 2 ∂J) at hi
    rw [← Measure.fst, Measure.fst_compProd] at hi
    exact hi.symm
  have hsecond : (∫ p, b p ^ 2 ∂J) = ∫ x, f x ^ 2 ∂ν := by
    have hi := integral_map (μ := J) measurable_snd.aemeasurable hf2.aestronglyMeasurable
    change (∫ x, f x ^ 2 ∂J.map Prod.snd) = (∫ p, b p ^ 2 ∂J) at hi
    rw [← Measure.snd, Measure.snd_compProd, hstat] at hi
    exact hi.symm
  have hcross : (∫ p, a p * b p ∂J) = ∫ x, f x ^ 2 ∂ν := by
    rw [Measure.integral_compProd hmul]
    apply integral_congr_ae
    filter_upwards with x
    change (∫ y, f x * f y ∂P x) = f x ^ 2
    rw [integral_const_mul, ← hharm x]
    ring
  have hzero : (∫ p, (b p - a p) ^ 2 ∂J) = 0 := by
    have hpoint : (fun p => (b p - a p) ^ 2) =
        ((fun p => b p ^ 2) - (fun p => 2 * (a p * b p))) + (fun p => a p ^ 2) := by
      funext p
      simp only [Pi.add_apply, Pi.sub_apply]
      ring
    rw [hpoint]
    change (∫ p, (((fun p => b p ^ 2) - (fun p => 2 * (a p * b p))) p +
      (fun p => a p ^ 2) p) ∂J) = 0
    rw [integral_add (hsqB.sub (hmul.const_mul 2)) hsqA]
    change (∫ p, (fun p => b p ^ 2) p - (fun p => 2 * (a p * b p)) p ∂J) +
      (∫ p, a p ^ 2 ∂J) = 0
    rw [integral_sub hsqB (hmul.const_mul 2), integral_const_mul, hfirst, hsecond, hcross]
    ring
  have hae := (integral_eq_zero_iff_of_nonneg (fun p => sq_nonneg (b p - a p)) hdiff).1 hzero
  filter_upwards [hae] with p hp
  change (b p - a p) ^ 2 = 0 at hp
  have : b p - a p = 0 := sq_eq_zero_iff.mp hp
  exact sub_eq_zero.mp this

end RWRS.Support
