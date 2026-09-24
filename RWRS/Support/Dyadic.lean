/-
The dyadic decomposition of the payoff (`lem:dyadic`).

Along one trajectory the payoff splits into a deterministic drift and a
fluctuation: writing the payoff as a sum over the vertices weighted by the
local time, and subtracting the mean of the scenery, gives
`S_n = E[ξ] A_n + W_n` pathwise, where `A_n` is the inverse-degree clock of the
trajectory.  On a graph of degree at most `d` the clock is at least `n/d`, so
at a negative mean the drift beats any block of times by its left endpoint, and
the supremum of the payoff over a dyadic block is at most the block's `Y_k`.
-/
import RWRS.Support.Critical

namespace RWRS.Support

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

open scoped Classical in
/-- The local time vanishes off the sites visited before time `n`. -/
theorem localTime_eq_zero_of_notMem (n : ℕ) (v : V) (X : ℕ → V)
    (hv : v ∉ (Finset.range n).image X) : localTime n v X = 0 := by
  classical
  rw [localTime, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro k hk hxk
  exact hv (Finset.mem_image.2 ⟨k, hk, hxk⟩)

/-- The local-time sum over the vertices is the sum along the trajectory. -/
theorem tsum_localTime_mul (c : V → ℝ) (n : ℕ) (X : ℕ → V) :
    ∑' v : V, ((localTime n v X : ℝ) / (G.degree v : ℝ)) * c v
      = ∑ k ∈ Finset.range n, c (X k) / (G.degree (X k) : ℝ) := by
  classical
  set S : Finset V := (Finset.range n).image X with hS
  rw [tsum_eq_sum (s := S) fun v hv => by
    rw [localTime_eq_zero_of_notMem n v X hv]
    simp]
  have hmaps : ∀ k ∈ Finset.range n, X k ∈ S := fun k hk =>
    Finset.mem_image.2 ⟨k, hk, rfl⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
    (fun k => c (X k) / (G.degree (X k) : ℝ))]
  refine Finset.sum_congr rfl fun v _ => ?_
  have hfib : ∀ k ∈ (Finset.range n).filter (fun k => X k = v),
      c (X k) / (G.degree (X k) : ℝ) = c v / (G.degree v : ℝ) := by
    intro k hk
    rw [(Finset.mem_filter.1 hk).2]
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, nsmul_eq_mul, localTime]
  ring

/-- The pathwise drift and fluctuation of `eq:dn-wn-stuff`. -/
theorem payoff_eq_drift_add (ξ : V → ℝ) (m : ℝ) (n : ℕ) (X : ℕ → V) :
    payoff G ξ n X
      = m * (∑ k ∈ Finset.range n, invDeg G (X k)) + fluctuation G ξ m n X := by
  have h1 := tsum_localTime_mul (G := G) ξ n X
  have h2 := tsum_localTime_mul (G := G) (fun v => ξ v - m) n X
  have h3 := tsum_localTime_mul (G := G) (fun _ => m) n X
  have hsplit : ∑' v : V, ((localTime n v X : ℝ) / (G.degree v : ℝ)) * ξ v
      = (∑' v : V, ((localTime n v X : ℝ) / (G.degree v : ℝ)) * (fun _ : V => m) v)
        + ∑' v : V, ((localTime n v X : ℝ) / (G.degree v : ℝ)) * (ξ v - m) := by
    rw [h1, h2, h3, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [payoff, ← h1, hsplit, h3]
  have hdrift : ∑ k ∈ Finset.range n, (fun _ : V => m) (X k) / (G.degree (X k) : ℝ)
      = m * ∑ k ∈ Finset.range n, invDeg G (X k) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [invDeg]; ring
  rw [hdrift, fluctuation]

/-- On a graph of degree at most `d` the inverse-degree clock of a trajectory is
at least `n/d`. -/
theorem sum_invDeg_ge [Infinite V] (hG : G.Connected) {d : ℕ} (hd : BoundedDegree G d)
    (n : ℕ) (X : ℕ → V) :
    (n : ℝ) / d ≤ ∑ k ∈ Finset.range n, invDeg G (X k) := by
  have hterm : ∀ k ∈ Finset.range n, (1 : ℝ) / d ≤ invDeg G (X k) := by
    intro k _
    have hpos : (0 : ℝ) < (G.degree (X k) : ℝ) := by
      exact_mod_cast degree_pos hG (X k)
    have hle : (G.degree (X k) : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd (X k)
    rw [invDeg]
    exact one_div_le_one_div_of_le hpos hle
  calc (n : ℝ) / d = ∑ _k ∈ Finset.range n, (1 : ℝ) / d := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
    _ ≤ ∑ k ∈ Finset.range n, invDeg G (X k) := Finset.sum_le_sum hterm

end RWRS.Support
