/-
Symmetry of the Green function.

The Green function of the simple random walk on a locally finite graph is
symmetric: `g(x,y) = g(y,x)`.  This follows from reversibility of the kernel
(`LatticeProb.Network.heat_reversible`) after clearing the degree factors, with
the zero-degree corners handled through the fact that an isolated vertex is
never reached from a different one.
-/
import RWRS.Support.LibraryBridge

open scoped ENNReal

variable {V : Type*}

/-- The heat kernel vanishes from an isolated vertex to a different vertex. -/
theorem heat_eq_zero_of_degree_zero (G : SimpleGraph V) [G.LocallyFinite] {x y : V}
    (hx : G.degree x = 0) (hxy : x ≠ y) (k : ℕ) : RWRS.heat G k x y = 0 := by
  induction k with
  | zero => simp [RWRS.heat, hxy]
  | succ k ih =>
      rw [show RWRS.heat G (k + 1) x y = RWRS.walkOp G (fun z => RWRS.heat G k z y) x from rfl,
        show RWRS.walkOp G (fun z => RWRS.heat G k z y) x
          = (∑ z ∈ G.neighborFinset x, RWRS.heat G k z y) / G.degree x from rfl, hx]
      simp

/-- The Green function of the simple random walk is symmetric. -/
theorem green_symm (G : SimpleGraph V) [G.LocallyFinite] (x y : V) :
    RWRS.green G x y = RWRS.green G y x := by
  rw [RWRS.green, RWRS.green]
  have hsum : ∀ k : ℕ, (G.degree x : ℝ≥0∞) * ENNReal.ofReal (RWRS.heat G k x y)
      = (G.degree y : ℝ≥0∞) * ENNReal.ofReal (RWRS.heat G k y x) := by
    intro k
    have hr : (G.degree x : ℝ) * RWRS.heat G k x y
        = (G.degree y : ℝ) * RWRS.heat G k y x := by
      have h := LatticeProb.Network.heat_reversible (G := G) k x y
      rw [← RWRS.Support.heat_eq_lib k x y, ← RWRS.Support.heat_eq_lib k y x] at h
      exact h
    have hr' : ENNReal.ofReal ((G.degree x : ℝ) * RWRS.heat G k x y)
        = ENNReal.ofReal ((G.degree y : ℝ) * RWRS.heat G k y x) := congrArg _ hr
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_natCast, ENNReal.ofReal_natCast] at hr'
    exact hr'
  have hmul : (G.degree x : ℝ≥0∞) * (∑' k : ℕ, ENNReal.ofReal (RWRS.heat G k x y))
      = (G.degree y : ℝ≥0∞) * (∑' k : ℕ, ENNReal.ofReal (RWRS.heat G k y x)) := by
    rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
    exact tsum_congr hsum
  by_cases hxy : x = y
  · subst hxy; rfl
  rcases Nat.eq_zero_or_pos (G.degree x) with hx | hx
  · -- x isolated: both tsums vanish
    have h1 : ∀ k, ENNReal.ofReal (RWRS.heat G k x y) = 0 := fun k => by
      rw [heat_eq_zero_of_degree_zero G hx hxy k, ENNReal.ofReal_zero]
    have h2 : ∀ k, ENNReal.ofReal (RWRS.heat G k y x) = 0 := fun k => by
      rcases Nat.eq_zero_or_pos (G.degree y) with hy' | hy'
      · rw [heat_eq_zero_of_degree_zero G hy' (Ne.symm hxy) k, ENNReal.ofReal_zero]
      · have hr : (G.degree y : ℝ) * RWRS.heat G k y x
          = (G.degree x : ℝ) * RWRS.heat G k x y := by
          have h := LatticeProb.Network.heat_reversible (G := G) k y x
          rw [← RWRS.Support.heat_eq_lib k y x, ← RWRS.Support.heat_eq_lib k x y] at h
          exact h
        rw [hx, Nat.cast_zero, zero_mul] at hr
        have h0 : RWRS.heat G k y x = 0 := by
          rcases mul_eq_zero.1 hr with h | h
          · exact absurd h (Nat.cast_ne_zero.2 hy'.ne')
          · exact h
        rw [h0, ENNReal.ofReal_zero]
    rw [tsum_congr h1, tsum_zero, tsum_congr h2, tsum_zero, ENNReal.zero_div, ENNReal.zero_div]
  rcases Nat.eq_zero_or_pos (G.degree y) with hy | hy
  · -- y isolated: both tsums vanish
    have h2 : ∀ k, ENNReal.ofReal (RWRS.heat G k y x) = 0 := fun k => by
      rw [heat_eq_zero_of_degree_zero G hy (Ne.symm hxy) k, ENNReal.ofReal_zero]
    have h1 : ∀ k, ENNReal.ofReal (RWRS.heat G k x y) = 0 := fun k => by
      have hr : (G.degree x : ℝ) * RWRS.heat G k x y
          = (G.degree y : ℝ) * RWRS.heat G k y x := by
        have h := LatticeProb.Network.heat_reversible (G := G) k x y
        rw [← RWRS.Support.heat_eq_lib k x y, ← RWRS.Support.heat_eq_lib k y x] at h
        exact h
      rw [hy, Nat.cast_zero, zero_mul] at hr
      have h0 : RWRS.heat G k x y = 0 := by
        rcases mul_eq_zero.1 hr with h | h
        · exact absurd h (Nat.cast_ne_zero.2 hx.ne')
        · exact h
      rw [h0, ENNReal.ofReal_zero]
    rw [tsum_congr h1, tsum_zero, tsum_congr h2, tsum_zero, ENNReal.zero_div, ENNReal.zero_div]
  · -- both degrees positive and finite: cancel
    have hdx : (G.degree x : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 hx.ne'
    have hdy : (G.degree y : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 hy.ne'
    have hxt : (G.degree x : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
    have hyt : (G.degree y : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
    rw [ENNReal.div_eq_div_iff hdx hxt hdy hyt]
    exact hmul
