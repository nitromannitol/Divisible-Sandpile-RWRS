import RWRS.Support.ErgBall

/-!
# Measurability of connected network codes

Connectedness is detected by the countable family of rooted balls. This is the
connectedness component of the construction in Lattice-Probability,
`LatticeProb/Prob/RerootGraphMeasurable.lean`.
-/

namespace RWRS.Support

open MeasureTheory

/-- Connectedness is equivalent to exhaustion of the vertex set by rooted balls. -/
theorem netGood_iff_forall_exists_mem_netBallSet {m : ℕ} (N : Net m) :
    NetGood N ↔ ∀ i : ℕ, ∃ r : ℕ, i ∈ netBallSet N r := by
  constructor
  · intro h i
    exact exists_mem_netBallSet h i
  · intro h
    refine ⟨?_⟩
    have hreach (i : ℕ) : (netGraph N).Reachable i (netRoot N) := by
      obtain ⟨r, hr⟩ := h i
      have hd := netBallSet_subset_closedBall N r hr
      have hne : (netGraph N).edist i (netRoot N) ≠ ⊤ := by
        intro heq
        change (netGraph N).edist i (netRoot N) ≤ (r : ℕ∞) at hd
        rw [heq] at hd
        exact (WithTop.not_top_le_coe r) hd
      exact SimpleGraph.reachable_of_edist_ne_top hne
    intro u v
    exact (hreach u).trans (hreach v).symm

/-- The set of connected network codes is measurable. -/
theorem measurableSet_netGood {m : ℕ} : MeasurableSet {N : Net m | NetGood N} := by
  have heq : {N : Net m | NetGood N} =
      ⋂ i : ℕ, ⋃ r : ℕ, {N : Net m | i ∈ netBallSet N r} := by
    ext N
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_iUnion,
      netGood_iff_forall_exists_mem_netBallSet]
  rw [heq]
  exact MeasurableSet.iInter fun i => MeasurableSet.iUnion fun r =>
    measurableSet_mem_netBallSet i r

/-- A rerooting-invariant event is unchanged by moving the root to any vertex
in its connected component. -/
theorem mem_iff_netReroot_of_mem_ball {m : ℕ} {A : Set (Net m)}
    (hA : RerootInvariant A) :
    ∀ (r : ℕ) (N : Net m) (v : ℕ), v ∈ netBallSet N r →
      (N ∈ A ↔ netReroot N v ∈ A) := by
  intro r
  induction r with
  | zero =>
      intro N v hv
      have hvroot : v = netRoot N := hv
      subst hvroot
      rfl
  | succ r ih =>
      intro N v hv
      rcases hv with hv | ⟨w, hw, hadj⟩
      · exact ih N v hv
      · have h₁ := ih N w hw
        have h₂ := hA (netReroot N w) v hadj
        exact h₁.trans h₂

/-- On a connected network, a rerooting-invariant event is unchanged by moving
the root to any vertex. -/
theorem mem_iff_netReroot_of_netGood {m : ℕ} {A : Set (Net m)}
    (hA : RerootInvariant A) {N : Net m} (hN : NetGood N) (v : ℕ) :
    N ∈ A ↔ netReroot N v ∈ A := by
  obtain ⟨r, hr⟩ := exists_mem_netBallSet hN v
  exact mem_iff_netReroot_of_mem_ball hA r N v hr

end RWRS.Support
