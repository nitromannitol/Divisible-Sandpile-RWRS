/-
The sites used by the unconstrained stages are the union of the stage blocks,
and the centre of a usable stage is admissible for the sites of the stages
before it.
-/
import RWRS.Support.DTStageAdm
import RWRS.Support.DTStageEvents

open scoped Classical ENNReal

namespace RWRS.Support

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

/-- **The used set gains exactly the block of the new stage centre.** -/
theorem uncUsed_succ (G : SimpleGraph V) [G.LocallyFinite] (r : ℕ)
    (C : V → Finset V) (X : ℕ → V) (i : ℕ) :
    uncUsed G r C X (i + 1)
      = uncUsed G r C X i ∪ C (X ((uncTime G r C X (i + 1)).toNat)) := by
  by_cases htop : uncTime G r C X i = ⊤
  · have hfrozen : uncStageState G r C X (i + 1) = uncStageState G r C X i :=
      uncTime_top_frozen G r C X i htop (i + 1) (Nat.le_succ i)
    have h1 : (uncTime G r C X (i + 1)).toNat = 0 := by
      show (uncStageState G r C X (i + 1)).1.toNat = 0
      rw [hfrozen]
      have htop' : (uncStageState G r C X i).1 = ⊤ := htop
      rw [htop']
      simp
    have h2 : uncUsed G r C X (i + 1) = uncUsed G r C X i := by
      show (uncStageState G r C X (i + 1)).2 = (uncStageState G r C X i).2
      rw [hfrozen]
    rw [h1, h2]
    exact (Finset.union_eq_left.2 (uncStart_block_subset_used G r C X i)).symm
  · by_cases hex : ∃ m : ℕ, (uncStageState G r C X i).1.toNat < m ∧
      Admissible G r (uncStageState G r C X i).2 (X m)
    · obtain ⟨h1, h2⟩ := uncTime_succ_of_ex G r C X i htop hex
      rw [h2, h1, ENat.toNat_coe]
      rfl
    · obtain ⟨h1, h2⟩ := uncTime_succ_of_nex G r C X i hex
      have h3 : (uncTime G r C X (i + 1)).toNat = 0 := by rw [h1]; simp
      rw [h3, h2]
      exact (Finset.union_eq_left.2 (uncStart_block_subset_used G r C X i)).symm

/-- **The used sites are the union of the blocks of the stages so far.** -/
theorem uncUsed_eq_stageSitesBelow (G : SimpleGraph V) [G.LocallyFinite] (r : ℕ)
    (C : V → Finset V) (X : ℕ → V) (i : ℕ) :
    uncUsed G r C X i
      = stageSitesBelow (fun j => C (X ((uncTime G r C X j).toNat))) (i + 1) := by
  induction i with
  | zero =>
      show uncUsed G r C X 0 = (Finset.range 1).biUnion _
      rw [Finset.range_one, Finset.singleton_biUnion]
      rfl
  | succ i ih =>
      rw [uncUsed_succ G r C X i, ih]
      simp only [stageSitesBelow, Finset.range_add_one, Finset.biUnion_insert]
      exact Finset.union_comm _ _

/-- **The centre of a stage is admissible for the sites of the earlier
stages.** -/
theorem admissible_stageSitesBelow (G : SimpleGraph V) [G.LocallyFinite] (r : ℕ)
    (C : V → Finset V) (X : ℕ → V) (i : ℕ) (hfin : uncTime G r C X i ≠ ⊤) :
    Admissible G r (stageSitesBelow (fun j => C (X ((uncTime G r C X j).toNat))) i)
      (X ((uncTime G r C X i).toNat)) := by
  cases i with
  | zero =>
      refine ⟨fun w hw => ?_, ?_⟩
      · simp [stageSitesBelow] at hw
      · simp [stageSitesBelow]
  | succ d =>
      have h := uncCentre_admissible G r C X d hfin
      rwa [uncUsed_eq_stageSitesBelow G r C X d] at h

end RWRS.Support
