/-
The moments of the local time in the three regimes of the spectral dimension,
for a vertex set in any universe.

`lem:local-time` is frozen for a vertex set in `Type`; the good-walk event of
`lem:good-walk` needs the same bound at the universe its own statement lives in,
so the three regimes are assembled here once and the frozen statement is the
specialization.
-/
import RWRS.Support.LocalTimeSum
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open scoped ENNReal

/-- **The moments of the local time, summed over the vertices, in the three
regimes.** -/
theorem RWRS.Support.localTimeMomentsAux (p d_s A : ℝ) (hp : 1 ≤ p) (hds : 0 < d_s) :
    ∃ Cp : ℝ, 0 < Cp ∧
      ∀ {V : Type*} (G : SimpleGraph V) [G.LocallyFinite] [Infinite V], G.Connected →
        RWRS.SpectralDimensionBound G d_s A → ∀ (x : V) (n : ℕ), 1 ≤ n →
          (d_s < 2 →
            (∑' v : V, ENNReal.ofReal (RWRS.walkExp G n x
                (fun X => (RWRS.localTime n v X : ℝ) ^ p)))
              ≤ ENNReal.ofReal (Cp * (n : ℝ) ^ (1 + (p - 1) * (1 - d_s / 2)))) ∧
          (d_s = 2 →
            (∑' v : V, ENNReal.ofReal (RWRS.walkExp G n x
                (fun X => (RWRS.localTime n v X : ℝ) ^ p)))
              ≤ ENNReal.ofReal (Cp * (n : ℝ) * (1 + Real.log n) ^ (p - 1))) ∧
          (2 < d_s →
            (∑' v : V, ENNReal.ofReal (RWRS.walkExp G n x
                (fun X => (RWRS.localTime n v X : ℝ) ^ p)))
              ≤ ENNReal.ofReal (Cp * (n : ℝ)))

:= by
  classical
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp
  have hmom : (0 : ℝ) < RWRS.Support.momConst ⌈p⌉₊ := RWRS.Support.momConst_pos _
  have hAone : (1 : ℝ) ≤ max A 1 := le_max_right _ _
  set β : ℝ := d_s / 2 with hβ
  have hβ0 : (0 : ℝ) ≤ β := by rw [hβ]; linarith
  rcases lt_trichotomy d_s 2 with hlt | heq | hgt
  · -- below the critical exponent
    have hβ1 : β < 1 := by rw [hβ]; linarith
    set K : ℝ := max A 1 * (1 + 1 / (1 - β)) with hK
    have hKpos : 0 < K := by
      rw [hK]
      have : (0 : ℝ) < 1 - β := by linarith
      have : (0 : ℝ) < 1 + 1 / (1 - β) := by positivity
      positivity
    refine ⟨p * RWRS.Support.momConst ⌈p⌉₊ * K ^ (p - 1), by positivity, ?_⟩
    intro V G _ _ hG hsp x n hn
    refine ⟨fun _ => ?_, fun h => absurd h (ne_of_lt hlt),
      fun h => absurd h (not_lt.2 hlt.le)⟩
    refine RWRS.Support.tsum_ofReal_le_of_sum_le
      (fun v => RWRS.Support.walkExp_nonneg fun X => Real.rpow_nonneg (by positivity) p)
      fun S => ?_
    refine le_trans (RWRS.Support.sum_walkExp_localTime_rpow_le hG hds hsp hp x hn S) ?_
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hcl : RWRS.Support.clockH A d_s n ≤ K * (n : ℝ) ^ (1 - β) := by
      rw [RWRS.Support.clockH, hK, mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (RWRS.Support.clockSum_le_of_lt_one hβ0 hβ1 hn) (by linarith)
    have hpow : RWRS.Support.clockH A d_s n ^ (p - 1)
        ≤ K ^ (p - 1) * (n : ℝ) ^ ((1 - β) * (p - 1)) := by
      refine le_trans (Real.rpow_le_rpow (RWRS.Support.clockH_pos A d_s hn).le hcl
        (by linarith)) (le_of_eq ?_)
      rw [Real.mul_rpow hKpos.le (Real.rpow_nonneg hnpos.le _), ← Real.rpow_mul hnpos.le]
    have hsplit : (n : ℝ) ^ (1 + (p - 1) * (1 - d_s / 2))
        = (n : ℝ) ^ ((1 - β) * (p - 1)) * (n : ℝ) := by
      have hexp : (1 : ℝ) + (p - 1) * (1 - d_s / 2) = (1 - β) * (p - 1) + 1 := by
        rw [hβ]; ring
      rw [hexp, Real.rpow_add hnpos, Real.rpow_one]
    rw [hsplit]
    calc p * RWRS.Support.momConst ⌈p⌉₊ * RWRS.Support.clockH A d_s n ^ (p - 1) * (n : ℝ)
        ≤ p * RWRS.Support.momConst ⌈p⌉₊
            * (K ^ (p - 1) * (n : ℝ) ^ ((1 - β) * (p - 1))) * (n : ℝ) := by
          refine mul_le_mul_of_nonneg_right ?_ hnpos.le
          exact mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = p * RWRS.Support.momConst ⌈p⌉₊ * K ^ (p - 1)
            * ((n : ℝ) ^ ((1 - β) * (p - 1)) * (n : ℝ)) := by ring
  · -- at the critical exponent
    have hβ1 : β = 1 := by rw [hβ, heq]; norm_num
    set K : ℝ := 2 * max A 1 with hK
    have hKpos : 0 < K := by rw [hK]; linarith
    refine ⟨p * RWRS.Support.momConst ⌈p⌉₊ * K ^ (p - 1), by positivity, ?_⟩
    intro V G _ _ hG hsp x n hn
    refine ⟨fun h => absurd h (by rw [heq]; exact lt_irrefl 2), fun _ => ?_,
      fun h => absurd h (by rw [heq]; exact lt_irrefl 2)⟩
    refine RWRS.Support.tsum_ofReal_le_of_sum_le
      (fun v => RWRS.Support.walkExp_nonneg fun X => Real.rpow_nonneg (by positivity) p)
      fun S => ?_
    refine le_trans (RWRS.Support.sum_walkExp_localTime_rpow_le hG hds hsp hp x hn S) ?_
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hlog : (0 : ℝ) ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
    have hcl : RWRS.Support.clockH A d_s n ≤ K * (1 + Real.log n) := by
      have h1 : RWRS.Support.clockSum β n ≤ 2 + Real.log n := by
        rw [hβ1]; exact RWRS.Support.clockSum_le_of_eq_one hn
      have h2 : RWRS.Support.clockH A d_s n = max A 1 * RWRS.Support.clockSum β n := rfl
      rw [h2, hK]
      nlinarith [h1, hAone, hlog]
    have hpow : RWRS.Support.clockH A d_s n ^ (p - 1)
        ≤ K ^ (p - 1) * (1 + Real.log n) ^ (p - 1) := by
      refine le_trans (Real.rpow_le_rpow (RWRS.Support.clockH_pos A d_s hn).le hcl
        (by linarith)) (le_of_eq ?_)
      rw [Real.mul_rpow hKpos.le (by linarith)]
    calc p * RWRS.Support.momConst ⌈p⌉₊ * RWRS.Support.clockH A d_s n ^ (p - 1) * (n : ℝ)
        ≤ p * RWRS.Support.momConst ⌈p⌉₊
            * (K ^ (p - 1) * (1 + Real.log n) ^ (p - 1)) * (n : ℝ) := by
          refine mul_le_mul_of_nonneg_right ?_ hnpos.le
          exact mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = p * RWRS.Support.momConst ⌈p⌉₊ * K ^ (p - 1) * (n : ℝ)
            * (1 + Real.log n) ^ (p - 1) := by ring
  · -- above the critical exponent
    have hβ1 : 1 < β := by rw [hβ]; linarith
    set T : ℝ := ∑' k : ℕ, 1 / (k : ℝ) ^ β with hT
    have hTnn : 0 ≤ T := by
      rw [hT]
      exact tsum_nonneg fun k => by positivity
    set K : ℝ := max A 1 * (1 + T) with hK
    have hKpos : 0 < K := by
      rw [hK]
      have : (0 : ℝ) < 1 + T := by linarith
      positivity
    refine ⟨p * RWRS.Support.momConst ⌈p⌉₊ * K ^ (p - 1), by positivity, ?_⟩
    intro V G _ _ hG hsp x n hn
    refine ⟨fun h => absurd hgt (not_lt.2 h.le),
      fun h => absurd hgt (by rw [h]; exact lt_irrefl 2), fun _ => ?_⟩
    refine RWRS.Support.tsum_ofReal_le_of_sum_le
      (fun v => RWRS.Support.walkExp_nonneg fun X => Real.rpow_nonneg (by positivity) p)
      fun S => ?_
    refine le_trans (RWRS.Support.sum_walkExp_localTime_rpow_le hG hds hsp hp x hn S) ?_
    have hcl : RWRS.Support.clockH A d_s n ≤ K := by
      have h1 : RWRS.Support.clockSum β n ≤ 1 + T := RWRS.Support.clockSum_le_of_one_lt hβ1 n
      have h2 : RWRS.Support.clockH A d_s n = max A 1 * RWRS.Support.clockSum β n := rfl
      rw [h2, hK]
      exact mul_le_mul_of_nonneg_left h1 (by linarith)
    have hpow : RWRS.Support.clockH A d_s n ^ (p - 1) ≤ K ^ (p - 1) :=
      Real.rpow_le_rpow (RWRS.Support.clockH_pos A d_s hn).le hcl (by linarith)
    have hnnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    refine mul_le_mul_of_nonneg_right ?_ hnnn
    exact mul_le_mul_of_nonneg_left hpow (by positivity)
