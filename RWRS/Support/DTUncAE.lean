import RWRS.Support.DTUnconstrained
import RWRS.Support.DTStagesAE
import RWRS.Support.DTAdmissibleCap

/-!
# Almost-sure finiteness of the unconstrained stage times

The unconstrained stage recursion (no horizon, no confinement) has all its
stage times finite almost surely, by the same exit-time argument as the
constrained recursion: condition on the value of the used set, apply the
library's a.s. exit from the finite set of non-admissible sites, and take the
countable intersection over the possible used sets.
-/

namespace RWRS.Support

open MeasureTheory LatticeProb Filter
open scoped Classical ENNReal

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [G.LocallyFinite] [MeasurableSpace V]
  [MeasurableSingletonClass V] [Countable V] [Infinite V]

/-- **The unconstrained successor stage time is a.s. finite, given the value of
the used set.** -/
theorem ae_uncTime_succ_of_fixed (hG : G.Connected)
    (hdeg : ∀ v : V, 0 < G.degree v) (hdt : RWRS.DoublyTransient G) (r : ℕ)
    (C : V → Finset V) (hC : ∀ y : V, y ∈ C y) (o : V) (i : ℕ) (F : Finset V)
    (hfin : ∀ᵐ X ∂(LatticeProb.Graph.walkLaw G o), uncTime G r C X i ≠ ⊤) :
    ∀ᵐ X ∂(LatticeProb.Graph.walkLaw G o),
      uncUsed G r C X i = F →
        uncTime G r C X (i + 1) ≠ ⊤ := by
  classical
  obtain ⟨D, hD⟩ := (finite_not_admissible hdt r F).exists_finset_coe
  have hesc : ∀ z : V, ∃ (q : V) (_ : G.Walk z q), q ∉ (D : Set V) := by
    intro z
    obtain ⟨q, hq⟩ := (finite_not_admissible hdt r F).infinite_compl.nonempty
    exact ⟨q, (hG.preconnected z q).some, by rw [hD]; exact hq⟩
  have hae := LatticeProb.Graph.ae_exitTime_shift_ne_top hdeg o
    (fun X => uncTime G r C X i) (uncTime_isStopping G r C i) hfin D hesc
  filter_upwards [hae, hfin] with X hX hTne hF
  by_contra htop
  have hno : ¬ ∃ m : ℕ, (uncTime G r C X i).toNat < m ∧
      Admissible G r (uncUsed G r C X i) (X m) := by
    intro hex
    obtain ⟨h1, h2⟩ := uncTime_succ_of_ex G r C X i hTne hex
    rw [h1] at htop
    exact absurd htop (ENat.coe_ne_top _)
  have htop' : uncTime G r C X (i + 1) = ⊤ := (uncTime_succ_of_nex G r C X i hno).1
  have hTcoe : (((uncTime G r C X i).toNat : ℕ) : ℕ∞) = uncTime G r C X i :=
    ENat.coe_toNat hTne
  have hmem : ∀ k : ℕ, LatticeProb.Graph.shiftPath (uncTime G r C X i).toNat X k ∈ (D : Set V) := by
    intro k
    have h2 : ¬ Admissible G r (uncUsed G r C X i) (X ((uncTime G r C X i).toNat + k)) := by
      rcases Nat.eq_zero_or_pos k with hk | hk
      · rw [hk]
        have hcen : X ((uncTime G r C X i).toNat) ∈ uncUsed G r C X i :=
          uncCentre_mem_used G r C hC X i
        intro hc
        rw [Nat.add_zero] at hc
        exact hc.1 _ hcen (by rw [G.edist_self]; simp)
      · intro hc
        exact hno ⟨(uncTime G r C X i).toNat + k, by omega, hc⟩
    rw [hF] at h2
    rw [hD]
    exact h2
  have hstay : ∀ k : ℕ, LatticeProb.Graph.shiftPath (uncTime G r C X i).toNat X
      ∈ LatticeProb.Graph.stayIn (D : Set V) k := by
    intro k j _
    exact hmem j
  exact hX ((LatticeProb.Graph.exitTime_eq_top_iff (D : Set V)
    (LatticeProb.Graph.shiftPath (uncTime G r C X i).toNat X)).2 (hstay))

/-- **Every unconstrained stage time is almost surely finite.** -/
theorem ae_uncTime_ne_top (hG : G.Connected)
    (hdeg : ∀ v : V, 0 < G.degree v) (hdt : RWRS.DoublyTransient G) (r : ℕ)
    (C : V → Finset V) (hC : ∀ y : V, y ∈ C y) (o : V) :
    ∀ i, ∀ᵐ X ∂(LatticeProb.Graph.walkLaw G o), uncTime G r C X i ≠ ⊤ := by
  intro i
  induction i with
  | zero => filter_upwards with X; exact ENat.zero_ne_top
  | succ i ih =>
      have hcover : {X : ℕ → V | ¬ uncTime G r C X (i + 1) ≠ ⊤}
          ⊆ ⋃ F : Finset V,
            {X : ℕ → V | uncTime G r C X i = ⊤} ∪
              {X : ℕ → V | uncUsed G r C X i = F ∧ uncTime G r C X (i + 1) = ⊤} := by
        intro X hX
        by_cases hT : uncTime G r C X i = ⊤
        · exact Set.mem_iUnion.2 ⟨uncUsed G r C X i, Or.inl hT⟩
        · exact Set.mem_iUnion.2 ⟨uncUsed G r C X i, Or.inr ⟨rfl, not_not.1 hX⟩⟩
      refine measure_mono_null hcover ?_
      rw [measure_iUnion_null_iff]
      intro F
      have hF := ae_uncTime_succ_of_fixed hG hdeg hdt r C hC o i F ih
      refine le_antisymm ((measure_union_le _ _).trans ?_) (by positivity)
      have h1 : (LatticeProb.Graph.walkLaw G o) {X : ℕ → V | uncTime G r C X i = ⊤} = 0 := by
        refine le_antisymm ((measure_mono ?_).trans (le_of_eq (ae_iff.1 ih))) (by positivity)
        intro X hX
        simp only [Set.mem_setOf_eq, not_not]
        exact hX
      have h2 : (LatticeProb.Graph.walkLaw G o)
          {X : ℕ → V | uncUsed G r C X i = F ∧ uncTime G r C X (i + 1) = ⊤} = 0 := by
        refine le_antisymm ((measure_mono ?_).trans (le_of_eq (ae_iff.1 hF))) (by positivity)
        rintro X ⟨h1, h2⟩
        simp only [Set.mem_setOf_eq, Classical.not_imp]
        exact ⟨h1, not_not.2 h2⟩
      rw [h1, h2]
      norm_num

