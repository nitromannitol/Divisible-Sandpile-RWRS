/-
The clock `H_α(n) = ∑_{k<n} (k ∨ 1)^{-α}` of `eq:local-time-ub` is `o(n)`.

This is what Step 2 of `lem:moment-sharpness` uses when it says
`H_α(N_t) = o(t)`.  Below the critical exponent the clock grows like `n^{1-α}`,
at it like `log n`, and above it it converges; in all three regimes it is
bounded by a constant times a power of `n` with exponent strictly below one,
and such a power is eventually below any positive multiple of `n`.
-/
import RWRS.Support.LocalTimeClock

namespace RWRS.Support

open Finset

/-- `2 + log n ≤ 4 √n` for `n ≥ 1`, from `log x ≤ x - 1` applied to `√n`. -/
theorem two_add_log_le_sqrt {n : ℕ} (hn : 1 ≤ n) :
    2 + Real.log n ≤ 4 * (n : ℝ) ^ ((1 : ℝ) / 2) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hs : (0 : ℝ) < (n : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos (by linarith) _
  have hone : (1 : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 2) := Real.one_le_rpow hn1 (by norm_num)
  have hlog : Real.log (n : ℝ) = 2 * Real.log ((n : ℝ) ^ ((1 : ℝ) / 2)) := by
    rw [Real.log_rpow (by linarith : (0 : ℝ) < (n : ℝ))]; ring
  have hle : Real.log ((n : ℝ) ^ ((1 : ℝ) / 2)) ≤ (n : ℝ) ^ ((1 : ℝ) / 2) - 1 :=
    Real.log_le_sub_one_of_pos hs
  rw [hlog]
  nlinarith [hone, hle]

/-- A sublinear power is eventually below any positive multiple of the identity. -/
theorem rpow_le_eps_mul {C β : ℝ} (hC : 0 ≤ C) (hβ1 : β < 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n → C * (n : ℝ) ^ β ≤ ε * (n : ℝ) := by
  have h1β : (0 : ℝ) < 1 - β := by linarith
  have hbase : (0 : ℝ) < C / ε + 1 := by positivity
  set M : ℝ := (C / ε + 1) ^ (1 / (1 - β)) with hM
  obtain ⟨N₀, hN₀⟩ := exists_nat_ge (max M 1)
  refine ⟨N₀ + 1, by omega, fun n hn => ?_⟩
  have hnR : (max M 1) ≤ (n : ℝ) := le_trans hN₀ (by exact_mod_cast Nat.le_of_succ_le hn)
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := le_trans (le_max_right M 1) hnR
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hMn : M ≤ (n : ℝ) := le_trans (le_max_left M 1) hnR
  have hM0 : (0 : ℝ) ≤ M := by rw [hM]; positivity
  have hpow : M ^ (1 - β) ≤ (n : ℝ) ^ (1 - β) := Real.rpow_le_rpow hM0 hMn h1β.le
  have hMeq : M ^ (1 - β) = C / ε + 1 := by
    rw [hM, ← Real.rpow_mul hbase.le, one_div, inv_mul_cancel₀ h1β.ne', Real.rpow_one]
  have hkey : C / ε ≤ (n : ℝ) ^ (1 - β) := by rw [hMeq] at hpow; linarith
  have hC' : C ≤ ε * (n : ℝ) ^ (1 - β) := by rw [div_le_iff₀ hε] at hkey; linarith
  have hsplit : (n : ℝ) ^ β * (n : ℝ) ^ (1 - β) = (n : ℝ) := by
    rw [← Real.rpow_add hnpos]; norm_num
  have hβpos : (0 : ℝ) < (n : ℝ) ^ β := Real.rpow_pos_of_pos hnpos β
  calc C * (n : ℝ) ^ β ≤ (ε * (n : ℝ) ^ (1 - β)) * (n : ℝ) ^ β := by nlinarith
    _ = ε * (n : ℝ) := by rw [mul_assoc, mul_comm ((n : ℝ) ^ (1 - β)), hsplit]

/-- **The clock is bounded by a sublinear power**, in each of the three regimes. -/
theorem exists_clockSum_le_rpow {α : ℝ} (hα : 0 < α) :
    ∃ C β : ℝ, 0 ≤ C ∧ β < 1 ∧ ∀ n : ℕ, 1 ≤ n → clockSum α n ≤ C * (n : ℝ) ^ β := by
  rcases lt_trichotomy α 1 with h | h | h
  · refine ⟨1 + 1 / (1 - α), 1 - α, by positivity, by linarith, fun n hn => ?_⟩
    exact clockSum_le_of_lt_one hα.le h hn
  · subst h
    refine ⟨4, 1 / 2, by norm_num, by norm_num, fun n hn => ?_⟩
    exact le_trans (clockSum_le_of_eq_one hn) (two_add_log_le_sqrt hn)
  · refine ⟨1 + ∑' k : ℕ, 1 / (k : ℝ) ^ α, 0, ?_, by norm_num, fun n hn => ?_⟩
    · have : (0 : ℝ) ≤ ∑' k : ℕ, 1 / (k : ℝ) ^ α :=
        tsum_nonneg fun k => by positivity
      linarith
    · have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      rw [Real.rpow_zero, mul_one]
      exact clockSum_le_of_one_lt h n

/-- **The clock is `o(n)`.** -/
theorem clockSum_le_eps_mul {α : ℝ} (hα : 0 < α) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n → clockSum α n ≤ ε * (n : ℝ) := by
  obtain ⟨C, β, hC, hβ, hbd⟩ := exists_clockSum_le_rpow hα
  obtain ⟨N, hN1, hN⟩ := rpow_le_eps_mul hC hβ hε
  exact ⟨N, hN1, fun n hn => le_trans (hbd n (le_trans hN1 hn)) (hN n hn)⟩

end RWRS.Support
