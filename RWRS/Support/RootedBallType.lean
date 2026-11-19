import RWRS.Support.RootedBallCode

/-!
# Measurable rooted ball types

A rooted ball is assigned the least code in a fixed enumeration of finite
rooted graphs. Equal families of matching codes give equal assigned types.
-/

namespace RWRS.Support

open MeasureTheory

/-- An injective enumeration of finite rooted adjacency matrices. -/
noncomputable def rootedFiniteGraphCode : RootedFiniteGraph → ℕ :=
  @Encodable.encode RootedFiniteGraph (Encodable.ofCountable RootedFiniteGraph)

/-- Some finite rooted graph matching the ball has the given code. -/
def HasNetBallCode {m : ℕ} (N : Net m) (r k : ℕ) : Prop :=
  ∃ c : RootedFiniteGraph, rootedFiniteGraphCode c = k ∧ NetBallMatches N r c

/-- Every rooted ball has a finite graph code. -/
theorem exists_netBallCode {m : ℕ} (N : Net m) (r : ℕ) :
    ∃ k, HasNetBallCode N r k := by
  obtain ⟨c, hc⟩ := exists_netBallMatches N r
  exact ⟨rootedFiniteGraphCode c, c, rfl, hc⟩

/-- The least finite graph code matching a rooted network ball. -/
noncomputable def netBallType {m : ℕ} (N : Net m) (r : ℕ) : ℕ := by
  classical
  exact Nat.find (exists_netBallCode N r)

/-- The least matching code is a measurable function of the network. -/
theorem measurable_netBallType {m : ℕ} (r : ℕ) :
    Measurable fun N : Net m => netBallType N r := by
  classical
  apply measurable_find (fun N : Net m => exists_netBallCode N r)
  intro k
  have heq : {N : Net m | HasNetBallCode N r k} =
      ⋃ c : RootedFiniteGraph,
        {N : Net m | rootedFiniteGraphCode c = k ∧ NetBallMatches N r c} := by
    ext N
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, HasNetBallCode]
  rw [heq]
  refine MeasurableSet.iUnion fun c => ?_
  by_cases h : rootedFiniteGraphCode c = k
  · simpa [h] using measurableSet_netBallMatches (m := m) r c
  · simp [h]

/-- Two balls that match the same finite rooted graphs have the same type. -/
theorem netBallType_eq_of_matches_iff {m : ℕ} {N N' : Net m} (r : ℕ)
    (h : ∀ c, NetBallMatches N r c ↔ NetBallMatches N' r c) :
    netBallType N r = netBallType N' r := by
  classical
  have hc (k : ℕ) : HasNetBallCode N r k ↔ HasNetBallCode N' r k := by
    simp only [HasNetBallCode]
    exact exists_congr fun c => and_congr_right fun _ => h c
  apply le_antisymm
  · apply Nat.find_min'
    exact (hc _).2 (Nat.find_spec (exists_netBallCode N' r))
  · apply Nat.find_min'
    exact (hc _).1 (Nat.find_spec (exists_netBallCode N r))

end RWRS.Support
