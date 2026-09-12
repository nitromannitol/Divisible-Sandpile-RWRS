/-
The stage times of the unconstrained trap selection are almost surely finite.

The paper's Step 1 needs `T_ℓ < ∞` almost surely.  The admissible set the walk
must reach depends on the walk itself (through the used set `F_i`), so the
library's exit-time lemma does not apply to it directly.  The obstruction is
removed by conditioning on the value of `F_i`: for each FIXED finite `F` the
non-admissible set is finite and co-infinite, so the walk restarted at the
stage time leaves it almost surely (`ae_exitTime_shift_ne_top` at the stage
time, which is a stopping time with an almost surely finite value by
induction), and the bad set is the union over the countably many `F` of null
sets.
-/
import RWRS.Support.DTStagesE
import RWRS.Support.DTAdmissible
import LatticeProb.Graph.ExitTime
import LatticeProb.Graph.MarkovAE

namespace RWRS.Support

open MeasureTheory
open scoped ENNReal

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [G.LocallyFinite]
variable [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]

omit [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] in
theorem stageUsed_dep (r : ℕ) (C : V → Finset V) (X : ℕ → V) (i k : ℕ)
    (hk : stageTime G r C X i ≤ (k : ℕ∞)) (X' : ℕ → V) (h : ∀ j ≤ k, X j = X' j) :
    stageUsed G r C X i = stageUsed G r C X' i := by
  have hp := stageE_prefix r C h i hk
  exact congrArg Prod.snd hp

/-- **For a fixed used set, the walk restarted at a finite stage time reaches
the admissible set almost surely.** -/
theorem ae_stageTime_succ_of_fixed [Infinite V] (hG : G.Connected)
    (hdeg : ∀ v : V, 0 < G.degree v)
    (hdt : RWRS.DoublyTransient G) (r : ℕ) (C : V → Finset V) (o : V) (i : ℕ)
    (F : Finset V)
    (hfin : ∀ᵐ X ∂(LatticeProb.Graph.walkLaw G o), stageTime G r C X i ≠ ⊤) :
    ∀ᵐ X ∂(LatticeProb.Graph.walkLaw G o),
      stageUsed G r C X i = F →
        stageTime G r C X (i + 1) ≠ ⊤ := by
  classical
  obtain ⟨D, hD⟩ := (finite_not_admissible hdt r F).exists_finset_coe
  have hesc : ∀ z : V, ∃ (q : V) (_ : G.Walk z q), q ∉ (D : Set V) := by
    intro z
    obtain ⟨q, hq⟩ := (finite_not_admissible hdt r F).infinite_compl.nonempty
    exact ⟨q, (hG.preconnected z q).some, by rw [hD]; exact hq⟩
  have hae := LatticeProb.Graph.ae_exitTime_shift_ne_top hdeg o
    (fun X => stageTime G r C X i) (isWalkStoppingE_stageTime r C i) hfin D hesc
  filter_upwards [hae, hfin] with X hX hTne hF
  by_contra htop
  rw [stageTime_succ] at htop
  have hno : ∀ n : ℕ, ¬ (stageTime G r C X i ≤ (n : ℕ∞)
      ∧ Admissible G r (stageUsed G r C X i) (X n)) :=
    (sInf_cast_eq_top (fun n => stageTime G r C X i ≤ (n : ℕ∞)
      ∧ Admissible G r (stageUsed G r C X i) (X n))).1 htop
  have hTcoe : (((stageTime G r C X i).toNat : ℕ) : ℕ∞) = stageTime G r C X i :=
    ENat.coe_toNat hTne
  have hmem : ∀ k : ℕ, LatticeProb.Graph.shiftPath (stageTime G r C X i).toNat X k ∈ (D : Set V) := by
    intro k
    have h1 : stageTime G r C X i ≤ (((stageTime G r C X i).toNat + k : ℕ) : ℕ∞) := by
      rw [← hTcoe]
      exact Nat.cast_le.2 (Nat.le_add_right _ k)
    have h2 : ¬ Admissible G r (stageUsed G r C X i) (X ((stageTime G r C X i).toNat + k)) :=
      fun hc => hno _ ⟨h1, hc⟩
    rw [hF] at h2
    rw [hD]
    exact h2
  have hstay : ∀ k : ℕ, LatticeProb.Graph.shiftPath (stageTime G r C X i).toNat X
      ∈ LatticeProb.Graph.stayIn (D : Set V) k := by
    intro k j _
    exact hmem j
  exact hX ((LatticeProb.Graph.exitTime_eq_top_iff (D : Set V)
    (LatticeProb.Graph.shiftPath (stageTime G r C X i).toNat X)).2 (hstay))

/-- **Every stage time is almost surely finite.**  Condition on the value of
the used set: for each fixed `F` the previous lemma applies, and the countable
intersection over `F : Finset V` of a.e. events is a.e. -/
theorem ae_stageTime_ne_top [Infinite V] (hG : G.Connected)
    (hdeg : ∀ v : V, 0 < G.degree v)
    (hdt : RWRS.DoublyTransient G) (r : ℕ) (C : V → Finset V) (o : V) :
    ∀ i, ∀ᵐ X ∂(LatticeProb.Graph.walkLaw G o), stageTime G r C X i ≠ ⊤ := by
  intro i
  induction i with
  | zero => filter_upwards with X; exact ENat.zero_ne_top
  | succ i ih =>
      -- decompose by the value of the used set, a countable union of a.e. events
      have hcover : {X : ℕ → V | ¬ stageTime G r C X (i + 1) ≠ ⊤}
          ⊆ ⋃ F : Finset V,
            {X : ℕ → V | stageTime G r C X i = ⊤} ∪
              {X : ℕ → V | stageUsed G r C X i = F ∧ stageTime G r C X (i + 1) = ⊤} := by
        intro X hX
        by_cases hT : stageTime G r C X i = ⊤
        · exact Set.mem_iUnion.2 ⟨stageUsed G r C X i, Or.inl hT⟩
        · exact Set.mem_iUnion.2 ⟨stageUsed G r C X i, Or.inr ⟨rfl, not_not.1 hX⟩⟩
      refine measure_mono_null hcover ?_
      rw [measure_iUnion_null_iff]
      intro F
      have hF := ae_stageTime_succ_of_fixed hG hdeg hdt r C o i F ih
      refine le_antisymm ((measure_union_le _ _).trans ?_) (by positivity)
      have h1 : (LatticeProb.Graph.walkLaw G o) {X : ℕ → V | stageTime G r C X i = ⊤} = 0 := by
        refine le_antisymm ((measure_mono ?_).trans (le_of_eq (ae_iff.1 ih))) (by positivity)
        intro X hX
        simp only [Set.mem_setOf_eq, not_not]
        exact hX
      have h2 : (LatticeProb.Graph.walkLaw G o)
          {X : ℕ → V | stageUsed G r C X i = F ∧ stageTime G r C X (i + 1) = ⊤} = 0 := by
        refine le_antisymm ((measure_mono ?_).trans (le_of_eq (ae_iff.1 hF))) (by positivity)
        rintro X ⟨h1, h2⟩
        simp only [Set.mem_setOf_eq, Classical.not_imp]
        exact ⟨h1, not_not.2 h2⟩
      rw [h1, h2]
      norm_num

end RWRS.Support
