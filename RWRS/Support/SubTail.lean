/-
The tail integration of `prop:subcritical`.

The proof of the proposition bounds `E_x[Y_k^q]` by integrating a tail estimate
of the form `P(Y_k > t) ≤ K/(a+t)^s` against `q t^{q-1} dt`.  The value of that
integral is `q K a^{q-s}(1/q + 1/(s-q))`: below the shift `a` the tail is at
most `K/a^s`, above it at most `K/t^s`, and the two elementary integrals are
computed here.  The Gaussian remainder of `eq:w-tail` is turned into a tail of
the same shape by `exp_neg_le_factorial_div_pow`, and the logarithmic factor of
the critical spectral dimension by `log_le_rpow_div`.
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import RWRS.Support.LocalTimeMoment

namespace RWRS.Support

open MeasureTheory
open scoped ENNReal

/-! ### Two elementary domination bounds -/

/-- A Gaussian factor is dominated by any polynomial: `exp (-x) ≤ n ! / x ^ n`. -/
theorem exp_neg_le_factorial_div_pow (n : ℕ) {x : ℝ} (hx : 0 < x) :
    Real.exp (-x) ≤ (Nat.factorial n : ℝ) / x ^ n := by
  have hx0 : (0:ℝ) < x ^ n := pow_pos hx n
  have hfac : (0:ℝ) < (Nat.factorial n : ℝ) := by positivity
  have h1 : x ^ n / (Nat.factorial n : ℝ) ≤ Real.exp x := by
    refine le_trans ?_ (Real.sum_le_exp_of_nonneg hx.le (n + 1))
    exact Finset.single_le_sum (f := fun i : ℕ => x ^ i / (Nat.factorial i : ℝ))
      (fun i _ => by positivity) (Finset.self_mem_range_succ n)
  have h2 : x ^ n ≤ (Nat.factorial n : ℝ) * Real.exp x := by
    rw [div_le_iff₀ hfac] at h1; linarith
  rw [Real.exp_neg, le_div_iff₀ hx0, inv_mul_eq_div, div_le_iff₀ (Real.exp_pos x)]
  linarith

/-- The logarithm is dominated by any positive power. -/
theorem log_le_rpow_div {x η : ℝ} (hx : 1 ≤ x) (hη : 0 < η) :
    Real.log x ≤ x ^ η / η := by
  have hx0 : (0:ℝ) < x := lt_of_lt_of_le zero_lt_one hx
  have h1 : Real.log (x ^ η) ≤ x ^ η - 1 :=
    Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx0 η)
  rw [Real.log_rpow hx0] at h1
  rw [le_div_iff₀ hη]
  linarith

/-! ### The two halves of the layer-cake integral -/

/-- The layer-cake weight below the shift. -/
theorem lintegral_ofReal_rpow_Ioc {a q : ℝ} (ha : 0 < a) (hq : 0 < q) :
    ∫⁻ t in Set.Ioc (0:ℝ) a, ENNReal.ofReal (t ^ (q - 1))
      = ENNReal.ofReal (a ^ q / q) := by
  have hr : (-1:ℝ) < q - 1 := by linarith
  have hint : IntegrableOn (fun t : ℝ => t ^ (q - 1)) (Set.Ioc 0 a) volume := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le ha.le]
    exact intervalIntegral.intervalIntegrable_rpow' hr
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioc (0:ℝ) a)] fun t : ℝ => t ^ (q - 1) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact Real.rpow_nonneg ht.1.le _
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
  congr 1
  rw [← intervalIntegral.integral_of_le ha.le, integral_rpow (Or.inl hr)]
  have h0 : (0:ℝ) ^ (q - 1 + 1) = 0 := Real.zero_rpow (by linarith)
  have h1 : q - 1 + 1 = q := by ring
  rw [h0, h1]
  ring

/-- The layer-cake weight above the shift. -/
theorem lintegral_ofReal_rpow_Ioi {a r : ℝ} (ha : 0 < a) (hr : r < -1) :
    ∫⁻ t in Set.Ioi a, ENNReal.ofReal (t ^ r)
      = ENNReal.ofReal (-a ^ (r + 1) / (r + 1)) := by
  have hint : IntegrableOn (fun t : ℝ => t ^ r) (Set.Ioi a) volume :=
    integrableOn_Ioi_rpow_of_lt hr ha
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioi a)] fun t : ℝ => t ^ r := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact Real.rpow_nonneg (ha.trans ht).le _
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, integral_Ioi_rpow_of_lt hr ha]


/-! ### The two pieces of a shifted polynomial tail -/

/-- The layer-cake integral below the shift. -/
theorem lintegral_tail_Ioc {a K q s : ℝ} (ha : 0 < a) (hK : 0 ≤ K) (hq : 0 < q) (hs : 0 < s) :
    (∫⁻ t in Set.Ioc (0:ℝ) a,
        ENNReal.ofReal (t ^ (q - 1)) * ENNReal.ofReal (K / (a + t) ^ s))
      ≤ ENNReal.ofReal (a ^ q / q) * ENNReal.ofReal (K / a ^ s) := by
  have hmeas : Measurable fun t : ℝ => ENNReal.ofReal (t ^ (q - 1)) :=
    (measurable_id.pow_const (q - 1)).ennreal_ofReal
  have hstep : ∀ t ∈ Set.Ioc (0:ℝ) a,
      ENNReal.ofReal (t ^ (q - 1)) * ENNReal.ofReal (K / (a + t) ^ s)
        ≤ ENNReal.ofReal (t ^ (q - 1)) * ENNReal.ofReal (K / a ^ s) := by
    intro t ht
    refine mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal ?_)
    have h1 : (0:ℝ) < a ^ s := Real.rpow_pos_of_pos ha s
    have h2 : a ^ s ≤ (a + t) ^ s :=
      Real.rpow_le_rpow ha.le (by linarith [ht.1]) hs.le
    exact div_le_div_of_nonneg_left hK h1 h2
  calc (∫⁻ t in Set.Ioc (0:ℝ) a,
      ENNReal.ofReal (t ^ (q - 1)) * ENNReal.ofReal (K / (a + t) ^ s))
    ≤ ∫⁻ t in Set.Ioc (0:ℝ) a,
        ENNReal.ofReal (t ^ (q - 1)) * ENNReal.ofReal (K / a ^ s) :=
      setLIntegral_mono' measurableSet_Ioc hstep
  _ = (∫⁻ t in Set.Ioc (0:ℝ) a, ENNReal.ofReal (t ^ (q - 1)))
        * ENNReal.ofReal (K / a ^ s) := by
      rw [lintegral_mul_const _ hmeas]
  _ = ENNReal.ofReal (a ^ q / q) * ENNReal.ofReal (K / a ^ s) := by
      rw [lintegral_ofReal_rpow_Ioc ha hq]

/-- The layer-cake integral above the shift. -/
theorem lintegral_tail_Ioi {a K q s : ℝ} (ha : 0 < a) (hK : 0 ≤ K) (hq : 0 < q) (hqs : q < s) :
    (∫⁻ t in Set.Ioi a,
        ENNReal.ofReal (t ^ (q - 1)) * ENNReal.ofReal (K / (a + t) ^ s))
      ≤ ENNReal.ofReal K * ENNReal.ofReal (a ^ (q - s) / (s - q)) := by
  have hs : 0 < s := lt_trans hq hqs
  have hr : q - 1 - s < -1 := by linarith
  have hstep : ∀ t ∈ Set.Ioi a,
      ENNReal.ofReal (t ^ (q - 1)) * ENNReal.ofReal (K / (a + t) ^ s)
        ≤ ENNReal.ofReal K * ENNReal.ofReal (t ^ (q - 1 - s)) := by
    intro t ht
    have ht0 : (0:ℝ) < t := lt_trans ha ht
    have h1 : (0:ℝ) < t ^ s := Real.rpow_pos_of_pos ht0 s
    have h2 : t ^ s ≤ (a + t) ^ s := Real.rpow_le_rpow ht0.le (by linarith) hs.le
    have h3 : K / (a + t) ^ s ≤ K / t ^ s := div_le_div_of_nonneg_left hK h1 h2
    have h4 : t ^ (q - 1) * (K / t ^ s) = K * t ^ (q - 1 - s) := by
      have hrw : t ^ (q - 1 - s) = t ^ (q - 1) / t ^ s := Real.rpow_sub ht0 (q - 1) s
      rw [hrw]
      ring
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg ht0.le _), ← ENNReal.ofReal_mul hK]
    refine ENNReal.ofReal_le_ofReal ?_
    calc t ^ (q - 1) * (K / (a + t) ^ s)
        ≤ t ^ (q - 1) * (K / t ^ s) :=
          mul_le_mul_of_nonneg_left h3 (Real.rpow_nonneg ht0.le _)
      _ = K * t ^ (q - 1 - s) := h4
  calc (∫⁻ t in Set.Ioi a,
      ENNReal.ofReal (t ^ (q - 1)) * ENNReal.ofReal (K / (a + t) ^ s))
      ≤ ∫⁻ t in Set.Ioi a, ENNReal.ofReal K * ENNReal.ofReal (t ^ (q - 1 - s)) :=
        setLIntegral_mono' measurableSet_Ioi hstep
    _ = ENNReal.ofReal K * ∫⁻ t in Set.Ioi a, ENNReal.ofReal (t ^ (q - 1 - s)) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = ENNReal.ofReal K * ENNReal.ofReal (-a ^ (q - 1 - s + 1) / (q - 1 - s + 1)) := by
        rw [lintegral_ofReal_rpow_Ioi ha hr]
    _ = ENNReal.ofReal K * ENNReal.ofReal (a ^ (q - s) / (s - q)) := by
        congr 2
        have he : q - 1 - s + 1 = q - s := by ring
        have hne : q - s ≠ 0 := ne_of_lt (by linarith)
        have hne2 : s - q ≠ 0 := ne_of_gt (by linarith)
        rw [he]
        field_simp
        ring


/-- The whole layer-cake integral of a shifted polynomial tail. -/
theorem lintegral_tail_full {a K q s : ℝ} (ha : 0 < a) (hK : 0 ≤ K) (hq : 0 < q) (hqs : q < s) :
    (∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (t ^ (q - 1)) * ENNReal.ofReal (K / (a + t) ^ s))
      ≤ ENNReal.ofReal (a ^ q / q) * ENNReal.ofReal (K / a ^ s)
        + ENNReal.ofReal K * ENNReal.ofReal (a ^ (q - s) / (s - q)) := by
  have hs : 0 < s := lt_trans hq hqs
  have hsplit : Set.Ioi (0:ℝ) = Set.Ioc (0:ℝ) a ∪ Set.Ioi a := by
    ext t
    simp only [Set.mem_Ioi, Set.mem_Ioc, Set.mem_union]
    constructor
    · intro ht
      rcases le_or_gt t a with h | h
      · exact Or.inl ⟨ht, h⟩
      · exact Or.inr h
    · rintro (⟨h, -⟩ | h)
      · exact h
      · exact lt_trans ha h
  have hdisj : Disjoint (Set.Ioc (0:ℝ) a) (Set.Ioi a) := by
    rw [Set.disjoint_left]
    rintro t ⟨-, h1⟩ h2
    rw [Set.mem_Ioi] at h2
    exact absurd h2 (not_lt.mpr h1)
  rw [hsplit, lintegral_union measurableSet_Ioi hdisj]
  exact add_le_add (lintegral_tail_Ioc ha hK hq hs) (lintegral_tail_Ioi ha hK hq hqs)

/-- **Tail integration for a two-term shifted polynomial tail.** -/
theorem lintegral_rpow_le_of_tail2 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (Y : Ω → ℝ)
    (hY0 : ∀ ω, 0 ≤ Y ω) (hYm : AEMeasurable Y μ)
    {q a K₁ s₁ K₂ s₂ : ℝ} (hq : 0 < q) (ha : 0 < a)
    (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂) (hqs₁ : q < s₁) (hqs₂ : q < s₂)
    (htail : ∀ t : ℝ, 0 < t → μ {ω | t < Y ω}
      ≤ ENNReal.ofReal (K₁ / (a + t) ^ s₁) + ENNReal.ofReal (K₂ / (a + t) ^ s₂)) :
    (∫⁻ ω, ENNReal.ofReal (Y ω ^ q) ∂μ)
      ≤ ENNReal.ofReal q *
          ((ENNReal.ofReal (a ^ q / q) * ENNReal.ofReal (K₁ / a ^ s₁)
              + ENNReal.ofReal K₁ * ENNReal.ofReal (a ^ (q - s₁) / (s₁ - q)))
            + (ENNReal.ofReal (a ^ q / q) * ENNReal.ofReal (K₂ / a ^ s₂)
              + ENNReal.ofReal K₂ * ENNReal.ofReal (a ^ (q - s₂) / (s₂ - q)))) := by
  rw [MeasureTheory.lintegral_rpow_eq_lintegral_meas_lt_mul μ
    (Filter.Eventually.of_forall hY0) hYm hq]
  refine mul_le_mul' le_rfl ?_
  have hstep : ∀ t ∈ Set.Ioi (0:ℝ),
      μ {ω | t < Y ω} * ENNReal.ofReal (t ^ (q - 1))
        ≤ ENNReal.ofReal (t ^ (q - 1)) * ENNReal.ofReal (K₁ / (a + t) ^ s₁)
          + ENNReal.ofReal (t ^ (q - 1)) * ENNReal.ofReal (K₂ / (a + t) ^ s₂) := by
    intro t ht
    rw [mul_comm, ← mul_add]
    exact mul_le_mul' le_rfl (htail t ht)
  refine le_trans (setLIntegral_mono' measurableSet_Ioi hstep) ?_
  have hmeas1 : Measurable fun t : ℝ =>
      ENNReal.ofReal (t ^ (q - 1)) * ENNReal.ofReal (K₁ / (a + t) ^ s₁) :=
    ((measurable_id.pow_const (q - 1)).ennreal_ofReal).mul
      ((measurable_const.div ((measurable_const.add measurable_id).pow_const s₁)).ennreal_ofReal)
  rw [lintegral_add_left hmeas1]
  exact add_le_add (lintegral_tail_full ha hK₁ hq hqs₁) (lintegral_tail_full ha hK₂ hq hqs₂)

/-! ### The growth of the clock -/

/-- **The clock grows more slowly than `n^{α+η}`**, uniformly in the three
regimes of the spectral dimension, with `α = (1-d_s/2)⁺`.  The logarithm of the
critical case is absorbed by the arbitrarily small extra exponent. -/
theorem clockH_le_rpow (A d_s η : ℝ) (hds : 0 < d_s) (hη : 0 < η) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 1 ≤ n →
      clockH A d_s n ≤ K * (n : ℝ) ^ (max (1 - d_s / 2) 0 + η) := by
  have hA : (1:ℝ) ≤ max A 1 := le_max_right _ _
  have hA0 : (0:ℝ) < max A 1 := lt_of_lt_of_le zero_lt_one hA
  rcases lt_trichotomy d_s 2 with hlt | heq | hgt
  · -- below the critical exponent
    have hβ1 : d_s / 2 < 1 := by linarith
    have hβ0 : (0:ℝ) ≤ d_s / 2 := by linarith
    have hpos : (0:ℝ) < 1 - d_s / 2 := by linarith
    refine ⟨max A 1 * (1 + 1 / (1 - d_s / 2)), by positivity, fun n hn => ?_⟩
    have hn1 : (1:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hcl := clockSum_le_of_lt_one hβ0 hβ1 hn
    have hmax : max (1 - d_s / 2) 0 = 1 - d_s / 2 := max_eq_left hpos.le
    have hstep : ((n : ℝ)) ^ (1 - d_s / 2) ≤ ((n : ℝ)) ^ (max (1 - d_s / 2) 0 + η) := by
      rw [hmax]
      exact Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
    rw [clockH]
    calc max A 1 * clockSum (d_s / 2) n
        ≤ max A 1 * ((1 + 1 / (1 - d_s / 2)) * ((n : ℝ)) ^ (1 - d_s / 2)) :=
          mul_le_mul_of_nonneg_left hcl hA0.le
      _ ≤ max A 1 * ((1 + 1 / (1 - d_s / 2)) * ((n : ℝ)) ^ (max (1 - d_s / 2) 0 + η)) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hstep ?_) hA0.le
          positivity
      _ = max A 1 * (1 + 1 / (1 - d_s / 2)) * ((n : ℝ)) ^ (max (1 - d_s / 2) 0 + η) := by ring
  · -- the critical exponent
    have hβ : d_s / 2 = 1 := by rw [heq]; norm_num
    have hmax : max (1 - d_s / 2) 0 = 0 := by rw [hβ]; norm_num
    refine ⟨max A 1 * (2 + 1 / η), by positivity, fun n hn => ?_⟩
    have hn1 : (1:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hcl : clockSum (d_s / 2) n ≤ 2 + Real.log n := by
      rw [hβ]; exact clockSum_le_of_eq_one hn
    have hlog : Real.log n ≤ ((n : ℝ)) ^ η / η := log_le_rpow_div hn1 hη
    have hne : (1:ℝ) ≤ ((n : ℝ)) ^ η := Real.one_le_rpow hn1 hη.le
    have hbound : clockSum (d_s / 2) n ≤ (2 + 1 / η) * ((n : ℝ)) ^ η := by
      have h1 : (2:ℝ) ≤ 2 * ((n : ℝ)) ^ η := by nlinarith
      have h2 : Real.log n ≤ (1 / η) * ((n : ℝ)) ^ η := by
        rw [one_div, inv_mul_eq_div]; exact hlog
      nlinarith
    rw [clockH, hmax, zero_add]
    calc max A 1 * clockSum (d_s / 2) n
        ≤ max A 1 * ((2 + 1 / η) * ((n : ℝ)) ^ η) :=
          mul_le_mul_of_nonneg_left hbound hA0.le
      _ = max A 1 * (2 + 1 / η) * ((n : ℝ)) ^ η := by ring
  · -- above the critical exponent
    have hβ : (1:ℝ) < d_s / 2 := by linarith
    have hmax : max (1 - d_s / 2) 0 = 0 := max_eq_right (by linarith)
    set T : ℝ := ∑' k : ℕ, 1 / (k : ℝ) ^ (d_s / 2) with hT
    refine ⟨max A 1 * (1 + max T 0), by positivity, fun n hn => ?_⟩
    have hn1 : (1:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hne : (1:ℝ) ≤ ((n : ℝ)) ^ η := Real.one_le_rpow hn1 hη.le
    have hcl : clockSum (d_s / 2) n ≤ 1 + max T 0 := by
      refine le_trans (clockSum_le_of_one_lt hβ n) ?_
      have : T ≤ max T 0 := le_max_left _ _
      linarith
    rw [clockH, hmax, zero_add]
    have hK : (0:ℝ) < max A 1 * (1 + max T 0) := by
      have : (0:ℝ) ≤ max T 0 := le_max_right _ _
      positivity
    calc max A 1 * clockSum (d_s / 2) n
        ≤ max A 1 * (1 + max T 0) := mul_le_mul_of_nonneg_left hcl hA0.le
      _ ≤ max A 1 * (1 + max T 0) * ((n : ℝ)) ^ η := by nlinarith


end RWRS.Support
