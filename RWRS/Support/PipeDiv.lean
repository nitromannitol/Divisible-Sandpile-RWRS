import RWRS.Support.PipeFlowBase

namespace RWRS.Support

open scoped Classical

variable {B : ℕ} {L : ℕ → ℕ}

theorem pipeUp_fst (v : List (Fin B) × ℕ) : (pipeUp B L v).1 = v.1 := by
  unfold pipeUp; split <;> rfl

/-- The divergence of the unit flow, read in the ambient graph. -/
theorem sum_pipeFlowAmb_interior (hL : ∀ j, 1 ≤ j → 1 ≤ L j)
    {w : List (Fin B)} {i : ℕ} (hw : w ≠ []) (hi : 1 ≤ i) (hiL : i ≤ L w.length - 1) :
    ∑ y ∈ (pipeGraph B L false).neighborFinset ((w : List (Fin B)), i),
        pipeFlowAmb B L (w, i) y = 0 := by
  have hval : PipeValid B L ((w : List (Fin B)), i) := Or.inr ⟨hw, hi, hiL⟩
  have hne : ((w : List (Fin B)), i) ≠ pipeRoot B := by
    intro h
    have := congrArg Prod.snd h
    simp only [pipeRoot] at this
    omega
  rw [neighborFinset_interior hL false hw hi hiL,
    Finset.sum_insert (by simpa using pipePred_ne_pipeUp hw hi), Finset.sum_singleton]
  have h1 : pipeFlowAmb B L (w, i) (pipePred B L (w, i))
      = -(((B : ℝ) ^ ((w : List (Fin B)).length))⁻¹) := by
    refine pipeFlowAmb_of_pred' hL hval (pipePred_valid hval) ?_ rfl
    exact fun hc => pipePred_ne_self hL hval hne hc.symm
  have h2 : pipeFlowAmb B L (w, i) (pipeUp B L (w, i))
      = ((B : ℝ) ^ ((w : List (Fin B)).length))⁻¹ := by
    have hpred : pipePred B L (pipeUp B L (w, i)) = (w, i) :=
      (pred_eq_iff_of_interior false hw hi hiL (pipeValidPlus_pipeUp false hw hi)).2 rfl
    have := pipeFlowAmb_of_pred (B := B) (L := L) (ne_pipeUp hi) hpred.symm
    rw [this, pipeUp_fst]
  rw [h1, h2]
  ring

theorem sum_pipeFlowAmb_branch (hL : ∀ j, 1 ≤ j → 1 ≤ L j) (hL2 : ∀ j, 1 ≤ j → 2 ≤ L j)
    (hB : 1 ≤ B) {u : List (Fin B)} (hu : u ≠ []) :
    ∑ y ∈ (pipeGraph B L false).neighborFinset ((u : List (Fin B)), 0),
        pipeFlowAmb B L (u, 0) y = 0 := by
  have hlen : 1 ≤ u.length := List.length_pos_iff.2 hu
  have h2 : 2 ≤ L u.length := hL2 u.length hlen
  have hBR : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB
  rw [neighborFinset_branch hL2 false hu, Finset.sum_insert branch_not_mem_image,
    Finset.sum_image (fun c _ d _ h => child_injective u h)]
  have h1 : pipeFlowAmb B L (u, 0) (u, L u.length - 1)
      = -(((B : ℝ) ^ u.length)⁻¹) := by
    refine pipeFlowAmb_of_pred' hL (Or.inl rfl) (pipeValid_pred_branch hL2 hu) ?_
      (pipePred_branch hL2 hu).symm
    intro hc
    have := congrArg Prod.snd hc
    simp only at this
    omega
  have h3 : ∀ c : Fin B, pipeFlowAmb B L (u, 0) ((u ++ [c] : List (Fin B)), 1)
      = ((B : ℝ) ^ (u.length + 1))⁻¹ := by
    intro c
    have hne : ((u : List (Fin B)), 0) ≠ ((u ++ [c] : List (Fin B)), 1) := by
      intro hc
      exact absurd (congrArg Prod.snd hc) (by simp)
    have := pipeFlowAmb_of_pred (B := B) (L := L) hne (pipePred_child c u).symm
    rw [this]
    simp
  rw [h1, Finset.sum_congr rfl (fun c _ => h3 c), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  have hpow : ((B : ℝ) ^ (u.length + 1)) = (B : ℝ) ^ u.length * (B : ℝ) := pow_succ _ _
  rw [hpow]
  field_simp
  ring

theorem sum_pipeFlowAmb_root (hL2 : ∀ j, 1 ≤ j → 2 ≤ L j)
    (hB : 1 ≤ B) :
    ∑ y ∈ (pipeGraph B L false).neighborFinset (([] : List (Fin B)), 0),
        pipeFlowAmb B L ([], 0) y = 1 := by
  have hBR : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB
  rw [neighborFinset_root hL2 false]
  rw [show (if (false : Bool) then ({(([] : List (Fin B)), 1)} : Finset (List (Fin B) × ℕ))
      else ∅) = ∅ from rfl, Finset.union_empty]
  rw [Finset.sum_image (fun c _ d _ h => root_child_injective h)]
  have h3 : ∀ c : Fin B, pipeFlowAmb B L (([] : List (Fin B)), 0) (([c] : List (Fin B)), 1)
      = ((B : ℝ))⁻¹ := by
    intro c
    have hne : (([] : List (Fin B)), 0) ≠ (([c] : List (Fin B)), 1) := by
      intro hc
      exact absurd (congrArg Prod.snd hc) (by simp)
    have hpc : (([] : List (Fin B)), 0) = pipePred B L (([c] : List (Fin B)), 1) := by
      have := pipePred_child (B := B) (L := L) c []
      simpa using this.symm
    rw [pipeFlowAmb_of_pred hne hpc]
    norm_num
  rw [Finset.sum_congr rfl (fun c _ => h3 c), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  exact mul_inv_cancel₀ (ne_of_gt hBR)

/-- **The unit flow of the tree of pipes has divergence one at the root and zero
everywhere else.**  A unit current enters at the root and splits equally among
the `B` child pipes at every branching vertex. -/
theorem divergence_pipeFlow (hL : ∀ j, 1 ≤ j → 1 ≤ L j) (hL2 : ∀ j, 1 ≤ j → 2 ≤ L j)
    (hB : 1 ≤ B) (x : pipeSites B L) :
    LatticeProb.Network.divergence (pipeSub B L) (pipeFlow B L) x
      = if x = pipeRootSub B L then 1 else 0 := by
  have hsum : LatticeProb.Network.divergence (pipeSub B L) (pipeFlow B L) x
      = ∑ y ∈ (pipeGraph B L false).neighborFinset (x : List (Fin B) × ℕ),
          pipeFlowAmb B L (x : List (Fin B) × ℕ) y :=
    sum_neighborFinset_pipeSub x (fun y => pipeFlowAmb B L (x : List (Fin B) × ℕ) y)
  rw [hsum]
  have hval := x.2
  rcases hxv : (x : List (Fin B) × ℕ) with ⟨w, i⟩
  rw [hxv] at hval
  by_cases hroot : x = pipeRootSub B L
  · have hw0 : ((w : List (Fin B)), i) = (([] : List (Fin B)), 0) := by
      rw [← hxv, hroot]; rfl
    rw [if_pos hroot, hw0]
    exact sum_pipeFlowAmb_root hL2 hB
  · have hne : ((w : List (Fin B)), i) ≠ (([] : List (Fin B)), 0) := by
      intro hc
      exact hroot (Subtype.ext (by rw [hxv, hc]; rfl))
    rw [if_neg hroot]
    rcases hval with h0 | ⟨hw, hi, hiL⟩
    · simp only at h0
      subst h0
      have hwnil : w ≠ [] := by
        intro hc; exact hne (by rw [hc])
      exact sum_pipeFlowAmb_branch hL hL2 hB hwnil
    · simp only at hw hi hiL
      exact sum_pipeFlowAmb_interior hL hw hi hiL

theorem divergence_pipeFlow_root (hL : ∀ j, 1 ≤ j → 1 ≤ L j) (hL2 : ∀ j, 1 ≤ j → 2 ≤ L j)
    (hB : 1 ≤ B) :
    LatticeProb.Network.divergence (pipeSub B L) (pipeFlow B L) (pipeRootSub B L) = 1 := by
  rw [divergence_pipeFlow hL hL2 hB, if_pos rfl]

theorem divergence_pipeFlow_of_ne (hL : ∀ j, 1 ≤ j → 1 ≤ L j) (hL2 : ∀ j, 1 ≤ j → 2 ≤ L j)
    (hB : 1 ≤ B) {x : pipeSites B L} (hx : x ≠ pipeRootSub B L) :
    LatticeProb.Network.divergence (pipeSub B L) (pipeFlow B L) x = 0 := by
  rw [divergence_pipeFlow hL hL2 hB, if_neg hx]

end RWRS.Support
