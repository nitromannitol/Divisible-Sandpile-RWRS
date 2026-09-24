/-
The Gaussian half of `eq:w-tail` for `prop:subcritical`.

Part (b) of `lem:fuk-nagaev` fixes the variance of the weighted sum exactly;
the chaining needs it in the form of an upper bound on the variance, which is
what the good-walk event supplies.  The passage from one to the other is a case
split on whether the variance vanishes, and when it does the weighted sum is
almost surely zero.
-/
import RWRS.Support.FukNagaevWeighted
import RWRS.Support.SubTail

namespace RWRS.Support

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {V : Type*} {ν : Measure ℝ}


/-- A weighted sum whose variance vanishes is almost surely zero. -/
theorem ae_weighted_sum_eq_zero_of_var_zero [IsProbabilityMeasure ν] (S : Finset V) (w : V → ℝ)
    {f : ℝ → ℝ} (hfsq : Integrable (fun z => f z ^ 2) ν)
    (hD : ∑ v ∈ S, w v ^ 2 * ∫ z, f z ^ 2 ∂ν = 0) :
    ∀ᵐ ξ ∂(RWRS.iidLaw V ν), ∑ v ∈ S, w v * f (ξ v) = 0 := by
  have hsq0 : (0:ℝ) ≤ ∫ z, f z ^ 2 ∂ν := integral_nonneg fun z => sq_nonneg _
  have hterm : ∀ v ∈ S, w v ^ 2 * ∫ z, f z ^ 2 ∂ν = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun v _ => by positivity)).1 hD
  have hae : ∀ v ∈ S, ∀ᵐ ξ ∂(RWRS.iidLaw V ν), w v * f (ξ v) = 0 := by
    intro v hv
    rcases mul_eq_zero.1 (hterm v hv) with h | h
    · have hw : w v = 0 := by
        have := sq_eq_zero_iff.1 h
        simpa using this
      exact Filter.Eventually.of_forall fun ξ => by rw [hw, zero_mul]
    · have hf0 : ∀ᵐ z ∂ν, f z = 0 := by
        have h2 := (integral_eq_zero_iff_of_nonneg (fun z => sq_nonneg (f z)) hfsq).1 h
        filter_upwards [h2] with z hz
        exact pow_eq_zero_iff (two_ne_zero) |>.1 hz
      have hmap : (RWRS.iidLaw V ν).map (fun ξ : V → ℝ => ξ v) = ν := map_eval_iidLaw ν v
      have h3 : ∀ᵐ ξ ∂(RWRS.iidLaw V ν), f (ξ v) = 0 :=
        MeasureTheory.ae_of_ae_map (measurable_pi_apply v).aemeasurable (by rw [hmap]; exact hf0)
      filter_upwards [h3] with ξ hξ
      rw [hξ, mul_zero]
  have hall : ∀ᵐ ξ ∂(RWRS.iidLaw V ν), ∀ v ∈ S, w v * f (ξ v) = 0 :=
    (Filter.eventually_all_finset S).2 hae
  filter_upwards [hall] with ξ hξ
  exact Finset.sum_eq_zero hξ

/-- **The polynomial and Gaussian tail with the variance bounded above.** -/
theorem meas_weighted_sum_ge_gaussian_le [IsProbabilityMeasure ν] {p c Cp : ℝ}
    (hFN : ∀ {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι] (P : Measure Ω),
      IsProbabilityMeasure P → ∀ (Y : ι → Ω → ℝ), iIndepFun Y P →
        (∀ i, Integrable (Y i) P) → (∀ i, ∫ ω, Y i ω ∂P = 0) →
        ∀ Mp B : ℝ, Mp = ∑ i, (∫⁻ ω, ENNReal.ofReal (|Y i ω| ^ p) ∂P).toReal →
          (∀ i, (∫⁻ ω, ENNReal.ofReal (|Y i ω| ^ p) ∂P) ≠ ⊤) →
          0 < B → B ^ 2 = ∑ i, ∫ ω, Y i ω ^ 2 ∂P →
          (∀ i, Integrable (fun ω => Y i ω ^ 2) P) →
          ∀ t : ℝ, 0 < t →
            P {ω | t ≤ |∑ i, Y i ω|}
              ≤ ENNReal.ofReal (Cp * Mp / t ^ p + 2 * Real.exp (-c * t ^ 2 / B ^ 2)))
    (S : Finset V) (w : V → ℝ) {f : ℝ → ℝ} (hf : Measurable f)
    (hfint : Integrable f ν) (hfsq : Integrable (fun z => f z ^ 2) ν)
    (hf0 : ∫ z, f z ∂ν = 0)
    (hfp : (∫⁻ y, ENNReal.ofReal (|f y| ^ p) ∂ν) ≠ ⊤)
    (hc : 0 < c) (Bb : ℝ)
    (hvar : ∑ v ∈ S, w v ^ 2 * ∫ z, f z ^ 2 ∂ν ≤ Bb ^ 2)
    (t : ℝ) (ht : 0 < t) :
    RWRS.iidLaw V ν {ξ : V → ℝ | t ≤ |∑ v ∈ S, w v * f (ξ v)|}
      ≤ ENNReal.ofReal (Cp * (∑ v ∈ S, |w v| ^ p
          * (∫⁻ y, ENNReal.ofReal (|f y| ^ p) ∂ν).toReal) / t ^ p
        + 2 * Real.exp (-c * t ^ 2 / Bb ^ 2)) := by
  set D : ℝ := ∑ v ∈ S, w v ^ 2 * ∫ z, f z ^ 2 ∂ν with hDdef
  have hsq0 : (0:ℝ) ≤ ∫ z, f z ^ 2 ∂ν := integral_nonneg fun z => sq_nonneg _
  have hD0 : (0:ℝ) ≤ D := Finset.sum_nonneg fun v _ => by positivity
  rcases eq_or_lt_of_le hD0 with hD | hD
  · have hzero : ∀ᵐ ξ ∂(RWRS.iidLaw V ν), ∑ v ∈ S, w v * f (ξ v) = 0 :=
      ae_weighted_sum_eq_zero_of_var_zero S w hfsq hD.symm
    have hsub : {ξ : V → ℝ | t ≤ |∑ v ∈ S, w v * f (ξ v)|}
        ⊆ {ξ : V → ℝ | ¬ (∑ v ∈ S, w v * f (ξ v) = 0)} := by
      intro ξ hξ h0
      rw [Set.mem_setOf_eq, h0, abs_zero] at hξ
      exact absurd hξ (not_le.mpr ht)
    have hnull : RWRS.iidLaw V ν {ξ : V → ℝ | t ≤ |∑ v ∈ S, w v * f (ξ v)|} = 0 :=
      measure_mono_null hsub hzero
    rw [hnull]
    exact bot_le
  · have hBpos : 0 < Real.sqrt D := Real.sqrt_pos.2 hD
    have hB2 : Real.sqrt D ^ 2 = D := Real.sq_sqrt hD.le
    have hmain := meas_weighted_sum_ge_gaussian hFN S w hf hfint hfsq hf0 hfp
      (Real.sqrt D) hBpos (by rw [hB2]) t ht
    refine le_trans hmain (ENNReal.ofReal_le_ofReal ?_)
    have hnum : (0:ℝ) < c * t ^ 2 := by positivity
    have hle : -c * t ^ 2 / Real.sqrt D ^ 2 ≤ -c * t ^ 2 / Bb ^ 2 := by
      rw [hB2, neg_mul, neg_div, neg_div, neg_le_neg_iff]
      exact div_le_div_of_nonneg_left hnum.le hD hvar
    have hexp : Real.exp (-c * t ^ 2 / Real.sqrt D ^ 2)
        ≤ Real.exp (-c * t ^ 2 / Bb ^ 2) := Real.exp_le_exp.2 hle
    linarith



/-- The Gaussian remainder of `eq:w-tail` as a polynomial tail of order `2n`. -/
theorem two_exp_neg_le (n : ℕ) {c t B2 : ℝ} (hc : 0 < c) (ht : 0 < t) (hB : 0 < B2) :
    2 * Real.exp (-c * t ^ 2 / B2)
      ≤ 2 * (Nat.factorial n : ℝ) * (B2 / c) ^ n / t ^ (2 * n) := by
  have hx : (0:ℝ) < c * t ^ 2 / B2 := by positivity
  have h1 : Real.exp (-(c * t ^ 2 / B2)) ≤ (Nat.factorial n : ℝ) / (c * t ^ 2 / B2) ^ n :=
    exp_neg_le_factorial_div_pow n hx
  have heq : -c * t ^ 2 / B2 = -(c * t ^ 2 / B2) := by ring
  have h2 : (c * t ^ 2 / B2) ^ n = c ^ n * t ^ (2 * n) / B2 ^ n := by
    rw [div_pow, mul_pow, pow_mul]
  have hcn : (0:ℝ) < c ^ n := by positivity
  have htn : (0:ℝ) < t ^ (2 * n) := by positivity
  have hBn : (0:ℝ) < B2 ^ n := by positivity
  have h3 : (Nat.factorial n : ℝ) / (c * t ^ 2 / B2) ^ n
      = (Nat.factorial n : ℝ) * (B2 / c) ^ n / t ^ (2 * n) := by
    rw [h2, div_pow]
    field_simp
  rw [h3] at h1
  calc 2 * Real.exp (-c * t ^ 2 / B2)
      = 2 * Real.exp (-(c * t ^ 2 / B2)) := by rw [heq]
    _ ≤ 2 * ((Nat.factorial n : ℝ) * (B2 / c) ^ n / t ^ (2 * n)) := by linarith
    _ = 2 * (Nat.factorial n : ℝ) * (B2 / c) ^ n / t ^ (2 * n) := by ring


end RWRS.Support
