/-
Step 1 of `lem:moment-sharpness`: the local-time bounds.

The upper bound is the diagonal one.  Reversibility reads the Green function
from the reversed walk, `g_n(o,v) = E_v[L_n(o)]/deg(o)`, and the first-passage
decomposition makes the expected local time at a site largest when the walk
starts there, `E_v[L_n(o)] ≤ E_o[L_n(o)]`; together they give
`g_n(o,v) ≤ g_n(o,o)`.  The diagonal is the sum of the on-diagonal heat kernel,
which hypothesis (A1) bounds term by term by the clock.  The paper reaches the
same bound by Cauchy--Schwarz in `ℓ²(deg)`.

The clock itself is at most the horizon, the inverse degree being at most one.
-/
import RWRS.Support.SharpClock
import RWRS.Support.ClockRatio
import RWRS.Support.Recurrence

namespace RWRS.Support

open Finset

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

/-- Each iterate of the averaging operator on the inverse degree is at most one. -/
theorem iter_walkOp_invDeg_le_one [Infinite V] (hG : G.Connected) (k : ℕ) (x : V) :
    (walkOp G)^[k] (RWRS.invDeg G) x ≤ 1 := by
  induction k generalizing x with
  | zero =>
      have hd : (1 : ℝ) ≤ (G.degree x : ℝ) := by exact_mod_cast degree_pos hG x
      simpa [RWRS.invDeg] using (div_le_one (by linarith)).2 hd
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      refine le_trans (walkOp_mono (g := fun _ => (1 : ℝ)) (fun v => ih v) x) ?_
      exact le_of_eq (walkOp_const hG 1 x)

/-- **The clock is at most the horizon.** -/
theorem clock_le_horizon [Infinite V] (hG : G.Connected) (n : ℕ) (x : V) :
    clock G n x ≤ (n : ℝ) := by
  rw [RWRS.clock]
  calc ∑ k ∈ Finset.range n, (walkOp G)^[k] (RWRS.invDeg G) x
      ≤ ∑ _k ∈ Finset.range n, (1 : ℝ) :=
        Finset.sum_le_sum fun k _ => iter_walkOp_invDeg_le_one hG k x
    _ = (n : ℝ) := by simp

/-- **The uniform upper bound on the finite-time Green function**, `eq:local-time-ub`.
Hypothesis (A1) bounds the diagonal heat kernel term by term. -/
theorem greenTime_le_clockSum [Infinite V] (hG : G.Connected) {α A : ℝ}
    (hA1 : ∀ (x : V) (n : ℕ), 1 ≤ n → RWRS.heat G n x x / G.degree x ≤ A * (n : ℝ) ^ (-α))
    (n : ℕ) (o v : V) :
    RWRS.greenTime G n o v ≤ max A 1 * clockSum α n := by
  have hdiag : RWRS.greenTime G n o v ≤ RWRS.greenTime G n o o :=
    greenTime_le_diag hG n o v
  refine le_trans hdiag ?_
  have hexp : RWRS.greenTime G n o o
      = ∑ k ∈ Finset.range n, RWRS.heat G k o o / (G.degree o : ℝ) := by
    rw [RWRS.greenTime, RWRS.meanLocalTime, Finset.sum_div]
  rw [hexp, clockSum, Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have hd : (1 : ℝ) ≤ (G.degree o : ℝ) := by exact_mod_cast degree_pos hG o
    have h0 : RWRS.heat G 0 o o / (G.degree o : ℝ) ≤ 1 := by
      have : RWRS.heat G 0 o o = 1 := by simp [RWRS.heat]
      rw [this]
      exact (div_le_one (by linarith)).2 hd
    have hct : clockTerm α 0 = 1 := by
      simp [clockTerm, Real.rpow_neg, Real.one_rpow]
    rw [hct, mul_one]
    exact le_trans h0 (le_max_right A 1)
  · have hmax : max (k : ℝ) 1 = (k : ℝ) := max_eq_left (by exact_mod_cast hk)
    have hbd := hA1 o k hk
    have hct : clockTerm α k = (k : ℝ) ^ (-α) := by rw [clockTerm, hmax]
    rw [hct]
    have hpos : (0 : ℝ) < (k : ℝ) ^ (-α) := Real.rpow_pos_of_pos (by exact_mod_cast hk) _
    exact le_trans hbd (mul_le_mul_of_nonneg_right (le_max_left A 1) hpos.le)

end RWRS.Support
