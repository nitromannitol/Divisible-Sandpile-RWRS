/-
The failure case of Step 1 costs nothing.

If no usable stage carries a good trap and the walk leaves `K` before the
horizon, then the capped rule stops at a site outside `K`, where the killed
potential of `K` vanishes.
-/
import RWRS.Support.DTStageFire
import RWRS.Support.DTPotential

open scoped Classical ENNReal

namespace RWRS.Support

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

/-- **On the no-hit event the potential at the capped rule vanishes.** -/
theorem trapPotential_trapRuleCapped_eq_zero_of_noHit (r : ℕ) (C : V → Finset V)
    (ℓ : ℕ) (K : Finset V) {N : ℕ} (hN : 0 < N) (ε : ℝ) (X : ℕ → V)
    (hescK : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ (K : Set V))
    (hexit : ∃ n, n < N ∧ X n ∉ K) (ξ : V → ℝ)
    (hξ : ∀ j < stageCnt G r C ℓ K N X,
      ξ ∉ trapEvent (C (X ((uncTime G r C X j).toNat))) ε) :
    trapPotential G K ξ (X (trapRuleCapped G r C ℓ K N ε ξ X)) = 0 := by
  obtain ⟨n, hnN, hnK⟩ := hexit
  have hnmem : n ∈ ruleSetCapped G r C ℓ K N ε ξ X := Or.inr ⟨hnN, Or.inl hnK⟩
  have hrN : trapRuleCapped G r C ℓ K N ε ξ X < N :=
    lt_of_le_of_lt (Nat.sInf_le hnmem) hnN
  have hin := trapRuleCapped_mem (G := G) r C ℓ K N ε ξ X
  rcases hin with hEq | ⟨_, hout | ⟨i, hiℓ, hstage, hwalk, husedj, htrap⟩⟩
  · exact absurd hEq (by omega)
  · exact trapPotential_eq_zero_of_notMem K hescK ξ hout
  · exfalso
    have hjlt : i < stageCnt G r C ℓ K N X :=
      lt_stageCnt_of_fire r C ℓ K hN X hiℓ (by rw [hstage]; exact hrN)
        (fun t ht => hwalk t (by rw [← hstage]; exact ht)) husedj
    have hagree : stageState G r C K N X i
        = ((uncTime G r C X i).toNat, uncUsed G r C X i) :=
      stageState_eq_of_lt_stageCnt r C ℓ K N X hjlt
    have hTi : (uncTime G r C X i).toNat = trapRuleCapped G r C ℓ K N ε ξ X := by
      rw [← hstage, hagree]
    refine hξ i hjlt (Set.mem_setOf.2 fun v hv => htrap v ?_)
    rw [← hTi]
    exact hv

end RWRS.Support
