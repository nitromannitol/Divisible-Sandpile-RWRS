/-
The clock `H_α(n) = ∑_{k<n} (k ∨ 1)^{-α}` of `eq:local-time-ub`, and its three
regimes.

Below the critical exponent the sum grows like `n^{1-α}`, at it like `log n`,
and above it the sum converges.  The first two are telescoping comparisons,
by Bernoulli's inequality for a concave power and by `log x ≤ x-1`; the third is
the convergence of the `p`-series.
-/
import RWRS.Support.LocalTimeCount
import Mathlib.Analysis.PSeries

namespace RWRS.Support

open Finset

/-- The `k`-th term of the clock, `(k ∨ 1)^{-β}`. -/
noncomputable def clockTerm (β : ℝ) (k : ℕ) : ℝ := (max (k : ℝ) 1) ^ (-β)

/-- The clock `∑_{k<n} (k ∨ 1)^{-β}`. -/
noncomputable def clockSum (β : ℝ) (n : ℕ) : ℝ := ∑ k ∈ Finset.range n, clockTerm β k

theorem clockTerm_pos (β : ℝ) (k : ℕ) : 0 < clockTerm β k :=
  Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one (le_max_right _ _)) _

theorem clockSum_nonneg (β : ℝ) (n : ℕ) : 0 ≤ clockSum β n :=
  Finset.sum_nonneg fun k _ => (clockTerm_pos β k).le

theorem clockSum_mono (β : ℝ) {a b : ℕ} (hab : a ≤ b) : clockSum β a ≤ clockSum β b :=
  Finset.sum_le_sum_of_subset_of_nonneg
    (fun _ hx => Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hx) hab))
    fun k _ _ => (clockTerm_pos β k).le

theorem one_le_clockSum {β : ℝ} {n : ℕ} (hn : 1 ≤ n) : 1 ≤ clockSum β n := by
  refine le_trans (le_of_eq ?_) (clockSum_mono β hn)
  rw [clockSum, Finset.sum_range_one, clockTerm]
  simp

theorem clockSum_pos {β : ℝ} {n : ℕ} (hn : 1 ≤ n) : 0 < clockSum β n :=
  lt_of_lt_of_le zero_lt_one (one_le_clockSum hn)

/-! ### Below the critical exponent -/

/-- The telescoping comparison for a concave power. -/
theorem clockTerm_le_diff {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β < 1) (j : ℕ) :
    (1 - β) * clockTerm β (j + 1)
      ≤ ((j + 1 : ℕ) : ℝ) ^ (1 - β) - ((j : ℕ) : ℝ) ^ (1 - β) := by
  have hk : (1 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (by omega)
  have hkpos : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := lt_of_lt_of_le zero_lt_one hk
  have hterm : clockTerm β (j + 1) = ((j + 1 : ℕ) : ℝ) ^ (-β) := by
    rw [clockTerm, max_eq_left hk]
  have hs : (-1 : ℝ) ≤ -1 / ((j + 1 : ℕ) : ℝ) := by
    rw [neg_div, neg_le_neg_iff, div_le_one hkpos]
    exact hk
  have hbern := rpow_one_add_le_one_add_mul_self hs (by linarith : (0:ℝ) ≤ 1 - β)
    (by linarith : (1 : ℝ) - β ≤ 1)
  have hval : (1 : ℝ) + -1 / ((j + 1 : ℕ) : ℝ) = ((j : ℕ) : ℝ) / ((j + 1 : ℕ) : ℝ) := by
    field_simp
    push_cast
    ring
  rw [hval] at hbern
  have hsplit : ((j : ℕ) : ℝ) ^ (1 - β)
      = ((j + 1 : ℕ) : ℝ) ^ (1 - β) * (((j : ℕ) : ℝ) / ((j + 1 : ℕ) : ℝ)) ^ (1 - β) := by
    rw [← Real.mul_rpow hkpos.le (by positivity)]
    congr 1
    field_simp
  have hpow : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) ^ (1 - β) := Real.rpow_pos_of_pos hkpos _
  have hmul := mul_le_mul_of_nonneg_left hbern hpow.le
  rw [← hsplit] at hmul
  have hdiv : ((j + 1 : ℕ) : ℝ) ^ (-β)
      = ((j + 1 : ℕ) : ℝ) ^ (1 - β) / ((j + 1 : ℕ) : ℝ) := by
    rw [show (-β : ℝ) = (1 - β) - 1 by ring, Real.rpow_sub hkpos, Real.rpow_one]
  rw [hterm, hdiv]
  have hexpand : ((j + 1 : ℕ) : ℝ) ^ (1 - β)
      * (1 + (1 - β) * (-1 / ((j + 1 : ℕ) : ℝ)))
      = ((j + 1 : ℕ) : ℝ) ^ (1 - β)
        - (1 - β) * (((j + 1 : ℕ) : ℝ) ^ (1 - β) / ((j + 1 : ℕ) : ℝ)) := by
    field_simp
    ring
  rw [hexpand] at hmul
  linarith

/-- **Below the critical exponent the clock grows like `n^{1-β}`.** -/
theorem clockSum_le_of_lt_one {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β < 1) {n : ℕ} (hn : 1 ≤ n) :
    clockSum β n ≤ (1 + 1 / (1 - β)) * (n : ℝ) ^ (1 - β) := by
  have hβ1 : (0 : ℝ) < 1 - β := by linarith
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have htel : ∑ j ∈ Finset.range m, ((((j + 1 : ℕ) : ℝ) ^ (1 - β)) - (((j : ℕ) : ℝ) ^ (1 - β)))
      = ((m : ℕ) : ℝ) ^ (1 - β) - ((0 : ℕ) : ℝ) ^ (1 - β) :=
    Finset.sum_range_sub (fun j => ((j : ℕ) : ℝ) ^ (1 - β)) m
  have hzero : ((0 : ℕ) : ℝ) ^ (1 - β) = 0 := by
    rw [Nat.cast_zero, Real.zero_rpow (ne_of_gt hβ1)]
  have hsum : (1 - β) * ∑ j ∈ Finset.range m, clockTerm β (j + 1) ≤ (m : ℝ) ^ (1 - β) := by
    rw [Finset.mul_sum]
    refine le_trans (Finset.sum_le_sum fun j _ => clockTerm_le_diff hβ0 hβ j) ?_
    rw [htel, hzero, sub_zero]
  have hsplit : clockSum β (m + 1) = 1 + ∑ j ∈ Finset.range m, clockTerm β (j + 1) := by
    rw [clockSum, Finset.sum_range_succ']
    have h0 : clockTerm β 0 = 1 := by simp [clockTerm]
    rw [h0]
    ring
  have hmono : (m : ℝ) ^ (1 - β) ≤ ((m + 1 : ℕ) : ℝ) ^ (1 - β) := by
    refine Real.rpow_le_rpow (Nat.cast_nonneg m) ?_ hβ1.le
    push_cast
    linarith
  have hone : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) ^ (1 - β) := by
    refine Real.one_le_rpow ?_ hβ1.le
    push_cast
    linarith
  rw [hsplit]
  have hkey : ∑ j ∈ Finset.range m, clockTerm β (j + 1)
      ≤ (1 / (1 - β)) * ((m + 1 : ℕ) : ℝ) ^ (1 - β) := by
    rw [one_div, inv_mul_eq_div, le_div_iff₀ hβ1]
    nlinarith [hsum, hmono]
  nlinarith [hkey, hone]

/-! ### At the critical exponent -/

theorem one_div_le_log_diff {n : ℕ} (hn : 1 ≤ n) :
    1 / ((n : ℝ) + 1) ≤ Real.log ((n : ℝ) + 1) - Real.log (n : ℝ) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  have hlog := Real.log_le_sub_one_of_pos (show (0:ℝ) < (n : ℝ) / ((n : ℝ) + 1) by positivity)
  rw [Real.log_div (ne_of_gt hnpos) (ne_of_gt hn1)] at hlog
  have hval : (n : ℝ) / ((n : ℝ) + 1) - 1 = -(1 / ((n : ℝ) + 1)) := by
    field_simp
    ring
  rw [hval] at hlog
  linarith

/-- **At the critical exponent the clock grows like `log n`.** -/
theorem clockSum_le_of_eq_one {n : ℕ} (hn : 1 ≤ n) :
    clockSum 1 n ≤ 2 + Real.log n := by
  have hstep : ∀ m : ℕ, 1 ≤ m → clockSum 1 (m + 1) ≤ 2 + Real.log m := by
    intro m
    induction m with
    | zero => intro h; omega
    | succ m ih =>
        intro _
        rcases Nat.eq_zero_or_pos m with hm | hm
        · subst hm
          rw [clockSum, Finset.sum_range_succ, Finset.sum_range_one]
          have h0 : clockTerm 1 0 = 1 := by simp [clockTerm]
          have h1 : clockTerm 1 1 = 1 := by simp [clockTerm]
          rw [h0, h1]
          norm_num
        · have hprev := ih hm
          have hterm : clockTerm 1 (m + 1) = 1 / ((m : ℝ) + 1) := by
            rw [clockTerm, max_eq_left (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (by omega) :
              (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ))]
            push_cast
            rw [Real.rpow_neg_one]
            simp
          have hlog := one_div_le_log_diff (n := m) hm
          rw [clockSum, Finset.sum_range_succ, ← clockSum, hterm]
          push_cast
          linarith
  rcases Nat.lt_or_ge n 2 with h2 | h2
  · have hn1 : n = 1 := by omega
    subst hn1
    rw [clockSum, Finset.sum_range_one]
    have h0 : clockTerm 1 0 = 1 := by simp [clockTerm]
    rw [h0]
    norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hm : 1 ≤ m := by omega
    refine le_trans (hstep m hm) ?_
    have : Real.log (m : ℝ) ≤ Real.log ((m + 1 : ℕ) : ℝ) := by
      refine Real.log_le_log (by exact_mod_cast hm) ?_
      push_cast
      linarith
    linarith

/-! ### Above the critical exponent -/

/-- **Above the critical exponent the clock is bounded.** -/
theorem clockSum_le_of_one_lt {β : ℝ} (hβ : 1 < β) (n : ℕ) :
    clockSum β n ≤ 1 + ∑' k : ℕ, 1 / (k : ℝ) ^ β := by
  have hsummable : Summable (fun k : ℕ => 1 / (k : ℝ) ^ β) :=
    Real.summable_one_div_nat_rpow.2 hβ
  have hnn : ∀ k : ℕ, 0 ≤ 1 / (k : ℝ) ^ β := fun k => by positivity
  have hpart : ∑ k ∈ Finset.range n, 1 / (k : ℝ) ^ β ≤ ∑' k : ℕ, 1 / (k : ℝ) ^ β :=
    hsummable.sum_le_tsum _ (fun k _ => hnn k)
  have hcmp : clockSum β n ≤ 1 + ∑ k ∈ Finset.range n, 1 / (k : ℝ) ^ β := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [clockSum]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [clockSum, Finset.sum_range_succ', Finset.sum_range_succ']
    have hterm : ∀ j ∈ Finset.range m,
        clockTerm β (j + 1) = 1 / (((j + 1 : ℕ) : ℝ)) ^ β := by
      intro j _
      have hj : (1 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.2 (by omega)
      rw [clockTerm, max_eq_left hj, Real.rpow_neg (by linarith), one_div]
    rw [Finset.sum_congr rfl hterm]
    have h0 : clockTerm β 0 = 1 := by rw [clockTerm]; simp
    have h1 : (1 : ℝ) / ((0 : ℕ) : ℝ) ^ β = 0 := by
      rw [Nat.cast_zero, Real.zero_rpow (by linarith), div_zero]
    rw [h0, h1]
    linarith
  linarith

end RWRS.Support
