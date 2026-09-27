/-
An infinite locally finite connected graph has a countable vertex set.  This is
what lets an event of the sandpile, which is a condition at every vertex, be
measurable for the product sigma algebra of the masses.
-/
import RWRS.Support.Odometer

namespace RWRS.Support

open scoped Classical

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

/-- The vertices reachable from `x` in at most `r` steps. -/
noncomputable def reach (G : SimpleGraph V) [G.LocallyFinite] (x : V) : ℕ → Finset V
  | 0 => {x}
  | r + 1 => (reach G x r).biUnion fun y => insert y (G.neighborFinset y)

/-- The base point `x` lies in `reach G x r` for every radius `r`, by
induction on `r` using that each step's `biUnion` inserts its own center. -/
theorem self_mem_reach (x : V) : ∀ r : ℕ, x ∈ reach G x r := by
  intro r
  induction r with
  | zero => simp [reach]
  | succ r ih => exact Finset.mem_biUnion.mpr ⟨x, ih, Finset.mem_insert_self _ _⟩

/-- `reach G x r` is contained in `reach G x (r + 1)`, since each vertex of
the former is inserted into its own `biUnion` term at the next step. -/
theorem reach_subset_succ (x : V) (r : ℕ) : reach G x r ⊆ reach G x (r + 1) := by
  intro y hy
  exact Finset.mem_biUnion.mpr ⟨y, hy, Finset.mem_insert_self _ _⟩

/-- `reach G x r` is monotone in the radius `r`, by chaining
`reach_subset_succ`. -/
theorem reach_mono (x : V) {r s : ℕ} (h : r ≤ s) : reach G x r ⊆ reach G x s := by
  induction s with
  | zero => rw [Nat.le_zero.mp h]
  | succ s ih =>
      rcases Nat.lt_or_ge r (s + 1) with hr | hr
      · exact (ih (Nat.lt_succ_iff.mp hr)).trans (reach_subset_succ x s)
      · rw [le_antisymm h hr]

/-- If `y ∈ reach G x s` then `reach G y r ⊆ reach G x (s + r)`: reaching `r`
steps from `y` reaches at most `s + r` steps from `x`. -/
theorem reach_trans {x y : V} {s : ℕ} (h : y ∈ reach G x s) :
    ∀ r : ℕ, reach G y r ⊆ reach G x (s + r) := by
  intro r
  induction r with
  | zero =>
      intro z hz
      rw [reach, Finset.mem_singleton] at hz
      subst hz
      simpa using h
  | succ r ih =>
      intro z hz
      rw [reach, Finset.mem_biUnion] at hz
      obtain ⟨w, hw, hz⟩ := hz
      exact Finset.mem_biUnion.mpr ⟨w, ih hw, hz⟩

/-- Every vertex `G`-reachable from `x` lies in `reach G x r` for some `r`,
by induction along the connecting walk. -/
theorem exists_mem_reach (x : V) : ∀ {y : V}, G.Reachable x y → ∃ r : ℕ, y ∈ reach G x r := by
  intro y hxy
  obtain ⟨p⟩ := hxy
  induction p with
  | nil => exact ⟨0, self_mem_reach _ 0⟩
  | @cons u w z h q ih =>
      obtain ⟨r, hr⟩ := ih
      refine ⟨1 + r, ?_⟩
      refine reach_trans (x := u) (y := w) (s := 1) ?_ r hr
      exact Finset.mem_biUnion.mpr ⟨u, self_mem_reach _ 0,
        Finset.mem_insert_of_mem ((SimpleGraph.mem_neighborFinset _ _ _).mpr h)⟩

/-- A connected, locally finite graph has a countable vertex set: fixing a
base point `o`, `V` is the countable union over `r` of the finite sets
`reach G o r`. -/
theorem countable_of_connected (hG : G.Connected) : Countable V := by
  have hne : Nonempty V := hG.nonempty
  obtain ⟨o⟩ := hne
  have huniv : (Set.univ : Set V) = ⋃ r : ℕ, ↑(reach G o r) := by
    ext y
    simp only [Set.mem_univ, true_iff, Set.mem_iUnion, Finset.mem_coe]
    exact exists_mem_reach o (hG.preconnected o y)
  have : (Set.univ : Set V).Countable := by
    rw [huniv]
    exact Set.countable_iUnion fun r => (reach G o r).countable_toSet
  exact Set.countable_univ_iff.mp this

end RWRS.Support
