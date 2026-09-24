/-
The arithmetic of the tree of pipes (`ssec:comb-estimates` and
`sec:recurrent-nonstab`).

The pipe lengths are `L_j = ⌊B^{αj}⌋`, so `B^{αj}/2 ≤ L_j ≤ B^{αj}` for `j ≥ 1`
under the standing conditions on `B` and `α`.  Both the radius
`R_m = ∑_{j≤m} L_j` and the size `N_m = ∑_{j≤m} B^j L_j` are geometric sums
whose last term dominates, so `R_m ≍ L_m ≍ B^{αm}` and `N_m ≍ B^m L_m`, and
since `α(1 + 1/α) = α + 1` this makes `N_m ≍ R_m^{d_f}` with `d_f = 1 + 1/α`.
-/
import RWRS.Support.PipeTree
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

open scoped ENNReal

namespace RWRS.Support

variable {B : ℕ} {α : ℝ}

/-! ### The base `b = B^α` -/

theorem cast_B_ge (hc : CombCond B α) : (2 : ℝ) ≤ (B : ℝ) := by
  exact_mod_cast hc.1

theorem cast_B_pos (hc : CombCond B α) : (0 : ℝ) < (B : ℝ) := by
  have := cast_B_ge hc; linarith

theorem base_ge (hc : CombCond B α) : (4 : ℝ) ≤ (B : ℝ) ^ α := hc.2.2.2.1

theorem base_pos (hc : CombCond B α) : (0 : ℝ) < (B : ℝ) ^ α := by
  have := base_ge hc; linarith

theorem alpha_pos (hc : CombCond B α) : 0 < α := lt_trans (by norm_num) hc.2.1

/-- `B^{αj}` written as the `j`-th power of `B^α`. -/
theorem base_pow (hc : CombCond B α) (j : ℕ) :
    ((B : ℝ) ^ α) ^ j = (B : ℝ) ^ (α * (j : ℝ)) := by
  rw [← Real.rpow_natCast ((B : ℝ) ^ α) j, ← Real.rpow_mul (le_of_lt (cast_B_pos hc))]

theorem base_pow_ge (hc : CombCond B α) {j : ℕ} (hj : 1 ≤ j) :
    (4 : ℝ) ≤ ((B : ℝ) ^ α) ^ j := by
  have h1 : (4 : ℝ) ^ j ≤ ((B : ℝ) ^ α) ^ j :=
    pow_le_pow_left₀ (by norm_num) (base_ge hc) j
  have h2 : (4 : ℝ) ≤ (4 : ℝ) ^ j := le_self_pow₀ (by norm_num) (Nat.one_le_iff_ne_zero.1 hj)
  linarith

/-! ### The pipe lengths -/

theorem combLen_le (hc : CombCond B α) (j : ℕ) :
    (combLen B α j : ℝ) ≤ ((B : ℝ) ^ α) ^ j := by
  rw [base_pow hc, combLen]
  exact Nat.floor_le (le_of_lt (Real.rpow_pos_of_pos (cast_B_pos hc) _))

theorem combLen_ge (hc : CombCond B α) {j : ℕ} (hj : 1 ≤ j) :
    ((B : ℝ) ^ α) ^ j / 2 ≤ (combLen B α j : ℝ) := by
  have h4 := base_pow_ge hc hj
  have hlt : (B : ℝ) ^ (α * (j : ℝ)) < (combLen B α j : ℝ) + 1 := by
    rw [combLen]
    exact Nat.lt_floor_add_one _
  rw [← base_pow hc] at hlt
  linarith

/-- Every pipe is nonempty, the zeroth one having length `⌊B^0⌋ = 1`. -/
theorem combLen_pos' (hc : CombCond B α) (j : ℕ) : 0 < combLen B α j := by
  have hB1 : (1 : ℝ) ≤ (B : ℝ) := by
    have := cast_B_ge hc; linarith
  have hexp : (0 : ℝ) ≤ α * (j : ℝ) := mul_nonneg (alpha_pos hc).le (Nat.cast_nonneg j)
  have h1 : (1 : ℝ) ≤ (B : ℝ) ^ (α * (j : ℝ)) := Real.one_le_rpow hB1 hexp
  rw [combLen]
  exact Nat.le_floor (by exact_mod_cast h1)

theorem combLen_pos (hc : CombCond B α) {j : ℕ} (hj : 1 ≤ j) : 0 < combLen B α j := by
  have h := combLen_ge hc hj
  have h4 := base_pow_ge hc hj
  have : (0 : ℝ) < (combLen B α j : ℝ) := by linarith
  exact_mod_cast this

/-! ### The radius -/

theorem combLen_le_gadgetRadius {m : ℕ} (hm : 1 ≤ m) :
    combLen B α m ≤ gadgetRadius (combLen B α) m :=
  Finset.single_le_sum (f := fun j => combLen B α j) (fun _ _ => Nat.zero_le _)
    (Finset.mem_Icc.2 ⟨hm, le_rfl⟩)

theorem sum_pow_Icc_le (hc : CombCond B α) (m : ℕ) :
    (∑ j ∈ Finset.Icc 1 m, ((B : ℝ) ^ α) ^ j)
      ≤ ((B : ℝ) ^ α) ^ (m + 1) / ((B : ℝ) ^ α - 1) := by
  have hb4 := base_ge hc
  have hb1 : (1 : ℝ) < (B : ℝ) ^ α := by linarith
  have hden : (0 : ℝ) < (B : ℝ) ^ α - 1 := by linarith
  induction m with
  | zero => simp; positivity
  | succ m ih =>
      rw [Finset.sum_Icc_succ_top (Nat.le_add_left 1 m)]
      have hpow : (0 : ℝ) < ((B : ℝ) ^ α) ^ (m + 1) := by positivity
      have hgoal : ((B : ℝ) ^ α) ^ (m + 1) / ((B : ℝ) ^ α - 1)
            + ((B : ℝ) ^ α) ^ (m + 1)
          = ((B : ℝ) ^ α) ^ (m + 1 + 1) / ((B : ℝ) ^ α - 1) := by
        field_simp
        ring
      linarith [ih, hgoal]

theorem gadgetRadius_le (hc : CombCond B α) {m : ℕ} (hm : 1 ≤ m) :
    (gadgetRadius (combLen B α) m : ℝ)
      ≤ 2 / (1 - (B : ℝ) ^ (-α)) * (combLen B α m : ℝ) := by
  have hb4 := base_ge hc
  have hden : (0 : ℝ) < (B : ℝ) ^ α - 1 := by linarith
  have hneg : (B : ℝ) ^ (-α) = ((B : ℝ) ^ α)⁻¹ :=
    Real.rpow_neg (le_of_lt (cast_B_pos hc)) α
  have hone : 1 - (B : ℝ) ^ (-α) = ((B : ℝ) ^ α - 1) / (B : ℝ) ^ α := by
    rw [hneg]; field_simp
  have hsum : (gadgetRadius (combLen B α) m : ℝ)
      ≤ ((B : ℝ) ^ α) ^ (m + 1) / ((B : ℝ) ^ α - 1) := by
    refine le_trans ?_ (sum_pow_Icc_le hc m)
    rw [gadgetRadius, Nat.cast_sum]
    exact Finset.sum_le_sum fun j _ => combLen_le hc j
  have hL := combLen_ge hc hm
  rw [hone]
  rw [div_div_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hden]
  have hbpos : (0 : ℝ) < (B : ℝ) ^ α := by linarith
  have hstep : (gadgetRadius (combLen B α) m : ℝ) * ((B : ℝ) ^ α - 1)
      ≤ ((B : ℝ) ^ α) ^ (m + 1) := by
    rw [← le_div_iff₀ hden]
    exact hsum
  calc (gadgetRadius (combLen B α) m : ℝ) * ((B : ℝ) ^ α - 1)
      ≤ ((B : ℝ) ^ α) ^ (m + 1) := hstep
    _ = (B : ℝ) ^ α * ((B : ℝ) ^ α) ^ m := by ring
    _ ≤ (B : ℝ) ^ α * (2 * (combLen B α m : ℝ)) :=
        mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hbpos)
    _ = 2 * (B : ℝ) ^ α * (combLen B α m : ℝ) := by ring

/-! ### The size -/

theorem gadgetSize_ge {m : ℕ} (hm : 1 ≤ m) :
    B ^ m * combLen B α m ≤ gadgetSize B (combLen B α) m :=
  Finset.single_le_sum (f := fun j => B ^ j * combLen B α j) (fun _ _ => Nat.zero_le _)
    (Finset.mem_Icc.2 ⟨hm, le_rfl⟩)

theorem gadgetSize_step (hc : CombCond B α) {j : ℕ} (hj : 2 ≤ j) :
    2 * ((B : ℝ) ^ (j - 1) * (combLen B α (j - 1) : ℝ))
      ≤ (B : ℝ) ^ j * (combLen B α j : ℝ) := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, (Nat.succ_pred_eq_of_pos (by omega)).symm⟩
  have hi : 1 ≤ i := by omega
  simp only [Nat.add_sub_cancel]
  have hb4 := base_ge hc
  have hB2 := cast_B_ge hc
  have hupper := combLen_le hc i
  have hlower := combLen_ge hc (j := i + 1) (by omega)
  have hbpos : (0 : ℝ) < (B : ℝ) ^ α := by linarith
  have hBpow : (0 : ℝ) < (B : ℝ) ^ i := by positivity
  have hpow : ((B : ℝ) ^ α) ^ (i + 1) = ((B : ℝ) ^ α) ^ i * (B : ℝ) ^ α := by ring
  have hLi : (0 : ℝ) ≤ (combLen B α i : ℝ) := Nat.cast_nonneg _
  have hbi : (0 : ℝ) < ((B : ℝ) ^ α) ^ i := pow_pos hbpos i
  have hP : (0 : ℝ) ≤ (B : ℝ) ^ i * ((B : ℝ) ^ α) ^ i := by positivity
  have hBb : (0 : ℝ) ≤ (B : ℝ) * (B : ℝ) ^ α - 4 := by nlinarith
  have hL : ((B : ℝ) ^ α) ^ i * (B : ℝ) ^ α / 2 ≤ (combLen B α (i + 1) : ℝ) := by
    rw [← hpow]; exact hlower
  calc 2 * ((B : ℝ) ^ i * (combLen B α i : ℝ))
      ≤ 2 * ((B : ℝ) ^ i * ((B : ℝ) ^ α) ^ i) := by nlinarith [hBpow, hupper]
    _ ≤ (B : ℝ) * (B : ℝ) ^ i * (((B : ℝ) ^ α) ^ i * (B : ℝ) ^ α / 2) := by
        nlinarith [mul_nonneg hP hBb]
    _ ≤ (B : ℝ) ^ (i + 1) * (combLen B α (i + 1) : ℝ) := by
        rw [show (B : ℝ) ^ (i + 1) = (B : ℝ) * (B : ℝ) ^ i by ring]
        exact mul_le_mul_of_nonneg_left hL (by positivity)

theorem gadgetSize_le (hc : CombCond B α) {m : ℕ} (hm : 1 ≤ m) :
    (gadgetSize B (combLen B α) m : ℝ) ≤ 2 * ((B : ℝ) ^ m * (combLen B α m : ℝ)) := by
  induction m with
  | zero => omega
  | succ m ih =>
      rcases Nat.eq_zero_or_pos m with hm0 | hm0
      · subst hm0
        rw [gadgetSize, Finset.Icc_self, Finset.sum_singleton]
        push_cast
        have : (0 : ℝ) ≤ (B : ℝ) ^ 1 * (combLen B α 1 : ℝ) := by positivity
        linarith
      · have hstep := gadgetSize_step hc (j := m + 1) (by omega)
        simp only [Nat.add_sub_cancel] at hstep
        have hih := ih hm0
        rw [gadgetSize, Finset.sum_Icc_succ_top (Nat.le_add_left 1 m)]
        push_cast
        rw [gadgetSize] at hih
        push_cast at hih
        linarith

/-! ### The size against the radius -/

/-- `α (1 + 1/α) = α + 1`, so the `d_f`-th power of `B^{αm}` is `B^m B^{αm}`. -/
theorem base_pow_rpow (hc : CombCond B α) {d_f : ℝ} (hdf : d_f = 1 + 1 / α) (m : ℕ) :
    (((B : ℝ) ^ α) ^ m) ^ d_f = (B : ℝ) ^ m * ((B : ℝ) ^ α) ^ m := by
  have hB0 : (0 : ℝ) ≤ (B : ℝ) := (cast_B_pos hc).le
  have hα : α ≠ 0 := (alpha_pos hc).ne'
  have hexp : α * (m : ℝ) * d_f = (m : ℝ) + α * (m : ℝ) := by
    rw [hdf]; field_simp; ring
  rw [← Real.rpow_natCast ((B : ℝ) ^ α) m, ← Real.rpow_mul hB0, ← Real.rpow_mul hB0,
    hexp, Real.rpow_add (cast_B_pos hc), Real.rpow_natCast, Real.rpow_mul hB0,
    Real.rpow_natCast]

theorem df_pos (hc : CombCond B α) {d_f : ℝ} (hdf : d_f = 1 + 1 / α) : 0 < d_f := by
  have := alpha_pos hc
  rw [hdf]
  positivity

/-- **Part (a) of `lem:rec-geometry`.** -/
theorem gadgetRadius_bounds (hc : CombCond B α) {m : ℕ} (hm : 1 ≤ m) :
    (combLen B α m : ℝ) ≤ (gadgetRadius (combLen B α) m : ℝ) ∧
      (gadgetRadius (combLen B α) m : ℝ)
        ≤ 2 / (1 - (B : ℝ) ^ (-α)) * (combLen B α m : ℝ) :=
  ⟨by exact_mod_cast combLen_le_gadgetRadius (B := B) (α := α) hm, gadgetRadius_le hc hm⟩

/-- The radius is between `B^{αm}/2` and `A B^{αm}`, where `A = b/(b-1)`. -/
theorem gadgetRadius_between (hc : CombCond B α) {m : ℕ} (hm : 1 ≤ m) :
    ((B : ℝ) ^ α) ^ m / 2 ≤ (gadgetRadius (combLen B α) m : ℝ) ∧
      (gadgetRadius (combLen B α) m : ℝ)
        ≤ (B : ℝ) ^ α / ((B : ℝ) ^ α - 1) * ((B : ℝ) ^ α) ^ m := by
  have hb4 := base_ge hc
  have hden : (0 : ℝ) < (B : ℝ) ^ α - 1 := by linarith
  constructor
  · exact le_trans (combLen_ge hc hm)
      (by exact_mod_cast combLen_le_gadgetRadius (B := B) (α := α) hm)
  · have h1 : (gadgetRadius (combLen B α) m : ℝ)
        ≤ ((B : ℝ) ^ α) ^ (m + 1) / ((B : ℝ) ^ α - 1) := by
      refine le_trans ?_ (sum_pow_Icc_le hc m)
      rw [gadgetRadius, Nat.cast_sum]
      exact Finset.sum_le_sum fun j _ => combLen_le hc j
    have h2 : ((B : ℝ) ^ α) ^ (m + 1) / ((B : ℝ) ^ α - 1)
        = (B : ℝ) ^ α / ((B : ℝ) ^ α - 1) * ((B : ℝ) ^ α) ^ m := by
      field_simp; ring
    linarith [h1, h2]

/-- The size is between `B^m B^{αm}/2` and `2 B^m B^{αm}`. -/
theorem gadgetSize_between (hc : CombCond B α) {m : ℕ} (hm : 1 ≤ m) :
    (B : ℝ) ^ m * ((B : ℝ) ^ α) ^ m / 2 ≤ (gadgetSize B (combLen B α) m : ℝ) ∧
      (gadgetSize B (combLen B α) m : ℝ) ≤ 2 * ((B : ℝ) ^ m * ((B : ℝ) ^ α) ^ m) := by
  have hBpow : (0 : ℝ) < (B : ℝ) ^ m := by
    have := cast_B_pos hc; positivity
  constructor
  · have h1 : ((B : ℝ) ^ m * (combLen B α m : ℝ))
        ≤ (gadgetSize B (combLen B α) m : ℝ) := by
      have := gadgetSize_ge (B := B) (α := α) hm
      have hcast : ((B ^ m * combLen B α m : ℕ) : ℝ)
          = (B : ℝ) ^ m * (combLen B α m : ℝ) := by push_cast; ring
      rw [← hcast]
      exact_mod_cast this
    nlinarith [combLen_ge hc hm, hBpow]
  · refine le_trans (gadgetSize_le hc hm) ?_
    nlinarith [combLen_le hc m, hBpow]

/-- **Part (b) of `lem:rec-geometry`.** -/
theorem gadgetSize_asymp (hc : CombCond B α) {d_f : ℝ} (hdf : d_f = 1 + 1 / α) :
    ∀ m : ℕ,
      1 / (2 * ((B : ℝ) ^ α / ((B : ℝ) ^ α - 1)) ^ d_f)
            * (gadgetRadius (combLen B α) m : ℝ) ^ d_f
          ≤ (gadgetSize B (combLen B α) m : ℝ) ∧
        (gadgetSize B (combLen B α) m : ℝ)
          ≤ 2 * (2 : ℝ) ^ d_f * (gadgetRadius (combLen B α) m : ℝ) ^ d_f := by
  intro m
  have hb4 := base_ge hc
  have hden : (0 : ℝ) < (B : ℝ) ^ α - 1 := by linarith
  have hA : (1 : ℝ) ≤ (B : ℝ) ^ α / ((B : ℝ) ^ α - 1) := by
    rw [le_div_iff₀ hden]; linarith
  have hApos : (0 : ℝ) < (B : ℝ) ^ α / ((B : ℝ) ^ α - 1) := by linarith
  have hdfpos := df_pos hc hdf
  rcases Nat.eq_zero_or_pos m with hm0 | hm
  · subst hm0
    simp only [gadgetRadius, gadgetSize]
    rw [show Finset.Icc 1 0 = (∅ : Finset ℕ) from rfl]
    simp only [Finset.sum_empty, Nat.cast_zero]
    rw [Real.zero_rpow hdfpos.ne']
    norm_num
  · obtain ⟨hRlo, hRhi⟩ := gadgetRadius_between hc hm
    obtain ⟨hNlo, hNhi⟩ := gadgetSize_between hc hm
    have hbpos := base_pos hc
    have hbm : (0 : ℝ) < ((B : ℝ) ^ α) ^ m := by positivity
    have hE := base_pow_rpow hc hdf m
    have hR0 : (0 : ℝ) ≤ (gadgetRadius (combLen B α) m : ℝ) := Nat.cast_nonneg _
    have hup : (gadgetRadius (combLen B α) m : ℝ) ^ d_f
        ≤ ((B : ℝ) ^ α / ((B : ℝ) ^ α - 1)) ^ d_f * ((B : ℝ) ^ m * ((B : ℝ) ^ α) ^ m) := by
      calc (gadgetRadius (combLen B α) m : ℝ) ^ d_f
          ≤ ((B : ℝ) ^ α / ((B : ℝ) ^ α - 1) * ((B : ℝ) ^ α) ^ m) ^ d_f :=
            Real.rpow_le_rpow hR0 hRhi hdfpos.le
        _ = ((B : ℝ) ^ α / ((B : ℝ) ^ α - 1)) ^ d_f * (((B : ℝ) ^ α) ^ m) ^ d_f :=
            Real.mul_rpow hApos.le hbm.le
        _ = ((B : ℝ) ^ α / ((B : ℝ) ^ α - 1)) ^ d_f * ((B : ℝ) ^ m * ((B : ℝ) ^ α) ^ m) := by
            rw [hE]
    have hlow : (2 : ℝ) ^ (-d_f) * ((B : ℝ) ^ m * ((B : ℝ) ^ α) ^ m)
        ≤ (gadgetRadius (combLen B α) m : ℝ) ^ d_f := by
      have h1 : (((B : ℝ) ^ α) ^ m / 2) ^ d_f ≤ (gadgetRadius (combLen B α) m : ℝ) ^ d_f :=
        Real.rpow_le_rpow (by positivity) hRlo hdfpos.le
      have h2 : (((B : ℝ) ^ α) ^ m / 2) ^ d_f
          = (2 : ℝ) ^ (-d_f) * ((B : ℝ) ^ m * ((B : ℝ) ^ α) ^ m) := by
        rw [div_eq_mul_inv, Real.mul_rpow hbm.le (by norm_num), hE,
          show ((2 : ℝ)⁻¹) ^ d_f = (2 : ℝ) ^ (-d_f) by
            rw [← Real.rpow_neg_one, ← Real.rpow_mul (by norm_num)]; ring_nf]
        ring
      linarith [h1, h2]
    have hApow : (0 : ℝ) < ((B : ℝ) ^ α / ((B : ℝ) ^ α - 1)) ^ d_f :=
      Real.rpow_pos_of_pos hApos _
    have h2pow : (0 : ℝ) < (2 : ℝ) ^ d_f := Real.rpow_pos_of_pos (by norm_num) _
    have hnegpow : (2 : ℝ) ^ (-d_f) = ((2 : ℝ) ^ d_f)⁻¹ := by
      rw [Real.rpow_neg (by norm_num)]
    have hApos2 : (0 : ℝ) < 2 * ((B : ℝ) ^ α / ((B : ℝ) ^ α - 1)) ^ d_f := by linarith
    rw [hnegpow] at hlow
    constructor
    · rw [div_mul_eq_mul_div, div_le_iff₀ hApos2]
      have hmul := mul_le_mul_of_nonneg_right hNlo (le_of_lt hApos2)
      have hid : (B : ℝ) ^ m * ((B : ℝ) ^ α) ^ m / 2
            * (2 * ((B : ℝ) ^ α / ((B : ℝ) ^ α - 1)) ^ d_f)
          = ((B : ℝ) ^ α / ((B : ℝ) ^ α - 1)) ^ d_f
              * ((B : ℝ) ^ m * ((B : ℝ) ^ α) ^ m) := by ring
      linarith [hup, hmul, hid]
    · have h2pos : (0 : ℝ) < 2 * (2 : ℝ) ^ d_f := by linarith
      have hmul := mul_le_mul_of_nonneg_left hlow (le_of_lt h2pos)
      have hid : 2 * (2 : ℝ) ^ d_f
            * (((2 : ℝ) ^ d_f)⁻¹ * ((B : ℝ) ^ m * ((B : ℝ) ^ α) ^ m))
          = 2 * ((B : ℝ) ^ m * ((B : ℝ) ^ α) ^ m) := by
        field_simp
      linarith [hmul, hid, hNhi]

end RWRS.Support
