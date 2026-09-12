/-
# The capped rule fires at the first usable good stage

For a fixed trajectory the stage blocks are fixed, and on the stage-`i` hit
event (the first block whose trap fires) with `i` below the count of usable
stages, the capped rule stops exactly at the stage-`i` time.  This is the
per-trajectory identification of the rule with the stage selection of Step 1.
-/
import RWRS.Support.DTStageCount
import RWRS.Support.DTStageEvents
import RWRS.Support.DTNatConv

namespace RWRS.Support

open MeasureTheory
open scoped Classical ENNReal

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

/-- **The capped rule fires at the first usable good stage.**  On the stage-`i`
hit event, with `i` below the count of usable stages, the capped rule stops
exactly at the stage-`i` time. -/
theorem trapRuleCapped_eq_stageTime_of_hitEvent (r : ℕ) (C : V → Finset V)
    (ℓ : ℕ) (K : Finset V) {N : ℕ} (hN : 0 < N) (ε : ℝ) (X : ℕ → V)
    {i : ℕ} (hi : i < stageCnt G r C ℓ K N X)
    (ξ : V → ℝ)
    (hξ : ξ ∈ hitEvent (fun j => C (X ((uncTime G r C X j).toNat))) ε i) :
    trapRuleCapped G r C ℓ K N ε ξ X = (uncTime G r C X i).toNat := by
  obtain ⟨hiℓ, hok⟩ := stageOK_of_lt_stageCnt r C ℓ K N X hi
  have hagree : stageState G r C K N X i
      = ((uncTime G r C X i).toNat, uncUsed G r C X i) :=
    stageState_eq_of_lt_stageCnt r C ℓ K N X hi
  have hTiN : (uncTime G r C X i).toNat < N := toNat_lt_of_lt_coe _ _ hok.1
  obtain ⟨ha, hb⟩ := hξ
  have ha' : ∀ v ∈ C (X ((uncTime G r C X i).toNat)), ξ v ≤ -ε := Set.mem_setOf.1 ha
  have hb' : ∀ j < i, ξ ∉ trapEvent (C (X ((uncTime G r C X j).toNat))) ε := hb
  have hstageeq : (stageState G r C K N X i).1 = (uncTime G r C X i).toNat := by
    rw [hagree]
  have hused : (stageState G r C K N X i).2 ⊆ K := by
    rw [hagree]; exact hok.2.2
  have hmem : (uncTime G r C X i).toNat ∈ ruleSetCapped G r C ℓ K N ε ξ X :=
    Or.inr ⟨hTiN, Or.inr ⟨i, hiℓ, hstageeq, hok.2.1, hused, ha'⟩⟩
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra hnot
  have hlt : trapRuleCapped G r C ℓ K N ε ξ X < (uncTime G r C X i).toNat :=
    Nat.not_le.1 hnot
  have hin : trapRuleCapped G r C ℓ K N ε ξ X ∈ ruleSetCapped G r C ℓ K N ε ξ X :=
    Nat.sInf_mem ⟨N, ruleSetCapped_nonempty r C ℓ K N ε ξ X⟩
  rcases hin with hN' | ⟨_, hexit⟩
  · omega
  · rcases hexit with hout | ⟨j, hj, hstage, hwalk, husedj, htrap⟩
    · exact absurd (hok.2.1 _ (by omega)) hout
    · have hjlt : j < stageCnt G r C ℓ K N X :=
        lt_stageCnt_of_fire r C ℓ K hN X hj (by rw [hstage]; omega)
          (fun t ht => hwalk t (by rw [← hstage]; exact ht)) husedj
      have hagreej : stageState G r C K N X j
          = ((uncTime G r C X j).toNat, uncUsed G r C X j) :=
        stageState_eq_of_lt_stageCnt r C ℓ K N X hjlt
      have hjT : (uncTime G r C X j).toNat = trapRuleCapped G r C ℓ K N ε ξ X := by
        rw [← hstage, hagreej]
      have hji : j < i := by
        by_contra hge
        have hmono : uncTime G r C X i ≤ uncTime G r C X j :=
          uncTime_mono G r C X (Nat.not_lt.1 hge)
        have hjne : uncTime G r C X j ≠ ⊤ :=
          ne_top_of_lt (stageOK_of_lt_stageCnt r C ℓ K N X hjlt).2.1
        have := ENat.toNat_le_toNat hmono hjne
        omega
      refine hb' j hji (Set.mem_setOf.2 ?_)
      intro v hv
      exact htrap v (by rw [← hjT]; exact hv)

end RWRS.Support
