/-
The walk-fixed stage blocks of Step 1: for a fixed trajectory, the blocks of
distinct usable stages are disjoint, and an earlier block lies in the sites of
the stages before a later one.
-/
import RWRS.Support.DTStageCount
import RWRS.Support.DTStageEvents
import RWRS.Support.DTNatConv

open scoped Classical

namespace RWRS.Support

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [G.LocallyFinite]

omit [DecidableEq V] in
/-- **The walk-fixed stage blocks are pairwise disjoint.**
The blocks `C (X T_j)` of distinct usable stages are disjoint. -/
theorem disjoint_walkBlocks (r : ℕ) (C : V → Finset V) (K : Finset V) {N : ℕ}
    (hCball : ∀ y : V, ((C y : Finset V) : Set V) ⊆ RWRS.closedBall G y r)
    (hCself : ∀ y : V, y ∈ C y) (X : ℕ → V) (ℓ : ℕ) {i : ℕ}
    (hi : i < stageCnt G r C ℓ K N X) :
    ∀ a ≤ i, ∀ b ≤ i, a ≠ b →
      Disjoint ((C (X ((uncTime G r C X a).toNat)) : Finset V) : Set V)
        ((C (X ((uncTime G r C X b).toNat)) : Finset V) : Set V) := by
  have hagree : ∀ j ≤ i, stageState G r C K N X j
      = ((uncTime G r C X j).toNat, uncUsed G r C X j) := fun j hj =>
    stageState_eq_of_lt_stageCnt r C ℓ K N X (lt_of_le_of_lt hj hi)
  have hgen : ∀ j ≤ i, (stageState G r C K N X j).1 < N := by
    intro j hj
    rw [hagree j hj]
    exact toNat_lt_of_lt_coe _ _ (stageOK_of_lt_stageCnt r C ℓ K N X (lt_of_le_of_lt hj hi)).2.1
  intro a ha b hb hab
  rcases lt_or_gt_of_ne hab with hlt | hgt
  · have := disjoint_stage_traps r C K hCball hCself X hlt (hgen b hb)
    rw [hagree a ha, hagree b hb] at this
    exact this
  · have := disjoint_stage_traps r C K hCball hCself X hgt (hgen a ha)
    rw [hagree b hb, hagree a ha] at this
    exact this.symm

omit [DecidableEq V] in
/-- **Earlier walk-fixed blocks lie in the stage sites below `i`.** -/
theorem walkBlock_subset_stageSitesBelow (r : ℕ) (C : V → Finset V) (X : ℕ → V)
    (i j : ℕ) (hj : j < i) :
    C (X ((uncTime G r C X j).toNat) : V) ⊆
      stageSitesBelow (fun j' => C (X ((uncTime G r C X j').toNat))) i := by
  intro v hv
  simp only [stageSitesBelow, Finset.mem_biUnion]
  exact ⟨j, Finset.mem_range.2 hj, hv⟩

end RWRS.Support
