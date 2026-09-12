/-
The stage-block bookkeeping of Step 1 of `prop:doubly-transient-really-general`.

The unconstrained stage recursion carries its used set with it: the block of a
stage centre is part of the used set, the used set grows, and the centre of a
finite stage is admissible for the sites used before it.  Admissibility caps
the Green weights of the used set at the centre, so none of them is infinite.
-/
import RWRS.Support.DTUnconstrained

open scoped ENNReal

namespace RWRS.Support

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

/-- **Admissibility caps each Green weight**, so no weight at an admissible
site is infinite. -/
theorem green_ne_top_of_admissible (r : ℕ) (F : Finset V) (z : V)
    (hadm : RWRS.Support.Admissible G r F z) :
    ∀ v ∈ F, RWRS.green G v z ≠ ⊤ := by
  intro v hv
  have hle : RWRS.green G v z ≤ ∑ w ∈ F, RWRS.green G w z :=
    Finset.single_le_sum (f := fun w => RWRS.green G w z) (fun _ _ => bot_le) hv
  exact ne_top_of_le_ne_top ENNReal.one_ne_top (le_trans hle hadm.2)

open scoped Classical in
/-- **The starting block is always used.** -/
theorem uncStart_block_subset_used (G : SimpleGraph V) [G.LocallyFinite] (r : ℕ)
    (C : V → Finset V) (X : ℕ → V) :
    ∀ i : ℕ, C (X 0) ⊆ uncUsed G r C X i := by
  intro i
  induction i with
  | zero => exact Finset.Subset.refl _
  | succ i ih => exact Finset.Subset.trans ih (uncUsed_mono G r C X i)

open scoped Classical in
/-- **The block of a stage centre is part of the used set.** -/
theorem uncBlock_subset_used (G : SimpleGraph V) [G.LocallyFinite] (r : ℕ)
    (C : V → Finset V) (X : ℕ → V) :
    ∀ i : ℕ, C (X ((uncTime G r C X i).toNat)) ⊆ uncUsed G r C X i := by
  intro i
  induction i with
  | zero =>
    show C (X ((0 : ℕ∞).toNat)) ⊆ C (X 0)
    simp only [ENat.toNat_zero]
    exact Finset.Subset.refl _
  | succ i ih =>
    by_cases htop : uncTime G r C X i = ⊤
    · have hfrozen : uncStageState G r C X (i + 1) = uncStageState G r C X i :=
        uncTime_top_frozen G r C X i htop (i + 1) (Nat.le_succ i)
      have h1 : (uncTime G r C X (i + 1)).toNat = 0 := by
        show (uncStageState G r C X (i + 1)).1.toNat = 0
        rw [hfrozen]
        have htop' : (uncStageState G r C X i).1 = ⊤ := htop
        rw [htop']
        simp
      rw [h1, uncUsed, hfrozen]
      exact uncStart_block_subset_used G r C X i
    · by_cases hex : ∃ m : ℕ, (uncStageState G r C X i).1.toNat < m ∧
        Admissible G r (uncStageState G r C X i).2 (X m)
      · obtain ⟨h1, h2⟩ := uncTime_succ_of_ex G r C X i htop hex
        rw [h1, h2]
        exact Finset.subset_union_right
      · obtain ⟨h1, h2⟩ := uncTime_succ_of_nex G r C X i hex
        rw [h1]
        show C (X 0) ⊆ uncUsed G r C X (i + 1)
        rw [h2]
        exact uncStart_block_subset_used G r C X i

open scoped Classical in
/-- **The used sets grow along the stages.** -/
theorem uncUsed_mono' (G : SimpleGraph V) [G.LocallyFinite] (r : ℕ)
    (C : V → Finset V) (X : ℕ → V) {i j : ℕ} (hij : i ≤ j) :
    uncUsed G r C X i ⊆ uncUsed G r C X j := by
  induction hij with
  | refl => exact Finset.Subset.refl _
  | @step k _ ih => exact Finset.Subset.trans ih (uncUsed_mono G r C X k)

open scoped Classical in
/-- **The block of an earlier stage lies in the used set of a later one.** -/
theorem uncBlock_subset_used_of_le (G : SimpleGraph V) [G.LocallyFinite] (r : ℕ)
    (C : V → Finset V) (X : ℕ → V) {i j : ℕ} (hij : j ≤ i) :
    C (X ((uncTime G r C X j).toNat)) ⊆ uncUsed G r C X i :=
  Finset.Subset.trans (uncBlock_subset_used G r C X j) (uncUsed_mono' G r C X hij)

open scoped Classical in
/-- **The centre of a finite stage is admissible for the sites used before
it.** -/
theorem uncCentre_admissible (G : SimpleGraph V) [G.LocallyFinite] (r : ℕ)
    (C : V → Finset V) (X : ℕ → V) (i : ℕ)
    (hfin : uncTime G r C X (i + 1) ≠ ⊤) :
    Admissible G r (uncUsed G r C X i) (X ((uncTime G r C X (i + 1)).toNat)) := by
  by_cases htop : uncTime G r C X i = ⊤
  · exfalso
    have hfrozen : uncStageState G r C X (i + 1) = uncStageState G r C X i :=
      uncTime_top_frozen G r C X i htop (i + 1) (Nat.le_succ i)
    exact hfin (by show (uncStageState G r C X (i + 1)).1 = ⊤; rw [hfrozen]; exact htop)
  · by_cases hex : ∃ m : ℕ, (uncStageState G r C X i).1.toNat < m ∧
      Admissible G r (uncStageState G r C X i).2 (X m)
    · obtain ⟨h1, _⟩ := uncTime_succ_of_ex G r C X i htop hex
      rw [h1]
      rw [ENat.toNat_coe]
      exact (Nat.find_spec hex).2
    · exact absurd (uncTime_succ_of_nex G r C X i hex).1 hfin

end RWRS.Support
