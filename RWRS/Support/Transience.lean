import RWRS.Support.BallWalk
import LatticeProb.Network.Killed
import RWRS.Support.Recurrence
import RWRS.Support.Odometer
import RWRS.Support.KilledGreen

namespace RWRS.Support

open scoped Classical

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

omit [G.LocallyFinite] in
theorem closedBall_mono_of_adj {x z : V} (h : G.Adj x z) (k : ℕ) :
    RWRS.closedBall G z k ⊆ RWRS.closedBall G x (k + 1) := by
  intro v hv
  have h1 : G.edist v z ≤ (k : ℕ∞) := hv
  have h2 : G.edist z x ≤ 1 := le_of_eq (SimpleGraph.edist_eq_one_iff_adj.2 h.symm)
  have h3 : G.edist v x ≤ G.edist v z + G.edist z x := SimpleGraph.edist_triangle
  have : G.edist v x ≤ (k : ℕ∞) + 1 := le_trans h3 (add_le_add h1 h2)
  simpa [RWRS.closedBall, Nat.cast_add] using this

/-- **The killed walk and the free walk agree up to the horizon** as long as the
whole ball of that radius lies in the set. -/
theorem killedHeat_eq_heat_of_ball (C : Set V) :
    ∀ (k : ℕ) (x : V), RWRS.closedBall G x k ⊆ C → ∀ y : V,
      RWRS.killedHeat G C k x y = RWRS.heat G k x y := by
  intro k
  induction k with
  | zero =>
      intro x hx y
      have hxC : x ∈ C := hx (by simp [RWRS.closedBall])
      simp only [RWRS.killedHeat, RWRS.heat, if_pos hxC]
  | succ k ih =>
      intro x hx y
      have hxC : x ∈ C := hx (by simp [RWRS.closedBall])
      simp only [RWRS.killedHeat, RWRS.heat, if_pos hxC]
      rw [RWRS.walkOp, RWRS.walkOp]
      congr 1
      refine Finset.sum_congr rfl fun z hz => ?_
      have hadj : G.Adj x z := (SimpleGraph.mem_neighborFinset _ _ _).1 hz
      exact ih z (fun v hv => hx (closedBall_mono_of_adj hadj k hv)) y

/-! ### A uniform bound on the killed Green function at the source gives
transience -/

/-- **Transience from a uniform bound on the effective resistance.**  If the
killed Green function at the source stays bounded over all finite escapable
sets, the walk is transient at that source. -/
theorem not_recurrent_of_killedGreen_bound [Infinite V] (hG : G.Connected) (o : V) (M : ℝ)
    (hM : ∀ C : Finset V, o ∈ C →
        (∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ (C : Set V)) →
        RWRS.killedGreenReal G (C : Set V) o o ≤ M) :
    ¬ RWRS.Recurrent G o := by
  classical
  intro hrec
  set M' : ℝ := (G.degree o : ℝ) * M with hM'
  obtain ⟨n, hn⟩ := meanLocalTime_unbounded_of_recurrent hG o hrec M'
  set C : Finset V := (finite_closedBall (G := G) o n).toFinset with hC
  have hball : RWRS.closedBall G o n ⊆ (C : Set V) := by
    intro v hv
    simpa [hC] using hv
  have hoC : o ∈ C := by
    have : o ∈ RWRS.closedBall G o n := by simp [RWRS.closedBall]
    exact_mod_cast hball this
  have hprop : ((C : Set V))ᶜ.Nonempty := by
    rcases Set.eq_empty_or_nonempty ((C : Set V))ᶜ with h | h
    · exfalso
      rw [Set.compl_empty_iff] at h
      have hfin : (Set.univ : Set V).Finite := h ▸ C.finite_toSet
      exact Set.infinite_univ hfin
    · exact h
  obtain ⟨q, hq⟩ := hprop
  have hesc : ∀ x : V, ∃ (p : V) (_ : G.Walk x p), p ∉ (C : Set V) := by
    intro x
    obtain ⟨w⟩ := hG.preconnected x q
    exact ⟨q, w, hq⟩
  -- the free walk and the killed walk agree up to time `n`
  have heq : ∀ k ∈ Finset.range n, RWRS.heat G k o o
      = LatticeProb.Graph.killedHeat G (C : Set V) k o o := by
    intro k hk
    have hk' : k ≤ n := le_of_lt (Finset.mem_range.1 hk)
    have hsub : RWRS.closedBall G o k ⊆ (C : Set V) := by
      intro v hv
      have hvk : G.edist v o ≤ (k : ℕ∞) := hv
      exact hball (le_trans hvk (by exact_mod_cast hk'))
    rw [← killedHeat_eq_heat_of_ball (C : Set V) k o hsub o, killedHeat_eq_lib]
  have hsum := summable_killedHeat_of_escape C hesc o o
  have hle : RWRS.meanLocalTime G n o o
      ≤ ∑' k : ℕ, LatticeProb.Graph.killedHeat G (C : Set V) k o o := by
    rw [RWRS.meanLocalTime, Finset.sum_congr rfl heq]
    exact hsum.sum_le_tsum _ (fun k _ => LatticeProb.Network.killedHeat_nonneg _ k o o)
  have hgreen := killedGreenReal_eq_tsum_of_escape C hesc o o
  have hdeg : (0 : ℝ) < (G.degree o : ℝ) := by
    exact_mod_cast degree_pos hG o
  have hbd := hM C hoC hesc
  rw [hgreen, div_le_iff₀ hdeg] at hbd
  linarith [hle, hn]

end RWRS.Support
