import RWRS.Support.PipeDiv

namespace RWRS.Support

open scoped Classical

variable {B : ℕ} {L : ℕ → ℕ}

/-- The energy the unit flow carries at a site, over the ordered pairs. -/
noncomputable def pipeNodeEnergy (B : ℕ) (L : ℕ → ℕ) (v : List (Fin B) × ℕ) : ℝ :=
  ∑ y ∈ (pipeGraph B L false).neighborFinset v, pipeFlowAmb B L v y ^ 2

theorem pipeNodeEnergy_interior (hL : ∀ j, 1 ≤ j → 1 ≤ L j)
    {w : List (Fin B)} {i : ℕ} (hw : w ≠ []) (hi : 1 ≤ i) (hiL : i ≤ L w.length - 1) :
    pipeNodeEnergy B L (w, i) = 2 * (((B : ℝ) ^ w.length) ^ 2)⁻¹ := by
  have hval : PipeValid B L ((w : List (Fin B)), i) := Or.inr ⟨hw, hi, hiL⟩
  have hne : ((w : List (Fin B)), i) ≠ pipeRoot B := by
    intro h
    have := congrArg Prod.snd h
    simp only [pipeRoot] at this
    omega
  rw [pipeNodeEnergy, neighborFinset_interior hL false hw hi hiL,
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
  rw [h1, h2, neg_sq, inv_pow]
  ring

theorem pipeNodeEnergy_branch (hL : ∀ j, 1 ≤ j → 1 ≤ L j) (hL2 : ∀ j, 1 ≤ j → 2 ≤ L j)
    (hB : 1 ≤ B) {u : List (Fin B)} (hu : u ≠ []) :
    pipeNodeEnergy B L (u, 0) ≤ 2 * (((B : ℝ) ^ u.length) ^ 2)⁻¹ := by
  have hlen : 1 ≤ u.length := List.length_pos_iff.2 hu
  have h2 : 2 ≤ L u.length := hL2 u.length hlen
  have hBR : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
  have hBpos : (0 : ℝ) < (B : ℝ) := by linarith
  rw [pipeNodeEnergy, neighborFinset_branch hL2 false hu, Finset.sum_insert branch_not_mem_image,
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
  rw [h1, Finset.sum_congr rfl (fun c _ => by rw [h3 c]), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  have hpos : (0 : ℝ) < (B : ℝ) ^ u.length := pow_pos hBpos _
  have hkey : (B : ℝ) * (((B : ℝ) ^ (u.length + 1))⁻¹) ^ 2
      = (((B : ℝ) ^ u.length) ^ 2)⁻¹ / (B : ℝ) := by
    rw [pow_succ]
    field_simp
    ring
  rw [hkey]
  have hle : (((B : ℝ) ^ u.length) ^ 2)⁻¹ / (B : ℝ) ≤ (((B : ℝ) ^ u.length) ^ 2)⁻¹ := by
    rw [div_le_iff₀ hBpos]
    nlinarith [inv_pos.2 (pow_pos hpos 2)]
  have hsq : (-(((B : ℝ) ^ u.length)⁻¹)) ^ 2 = (((B : ℝ) ^ u.length) ^ 2)⁻¹ := by
    rw [neg_pow, ← inv_pow]
    norm_num
  rw [hsq]
  linarith

theorem pipeNodeEnergy_root (hL2 : ∀ j, 1 ≤ j → 2 ≤ L j) (hB : 1 ≤ B) :
    pipeNodeEnergy B L (([] : List (Fin B)), 0)
      ≤ 2 * (((B : ℝ) ^ ([] : List (Fin B)).length) ^ 2)⁻¹ := by
  have hBR : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
  have hBpos : (0 : ℝ) < (B : ℝ) := by linarith
  rw [pipeNodeEnergy, neighborFinset_root hL2 false]
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
  rw [Finset.sum_congr rfl (fun c _ => by rw [h3 c]), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  simp only [List.length_nil, pow_zero, one_pow, inv_one, mul_one]
  rw [show ((B : ℝ))⁻¹ ^ 2 = ((B : ℝ) ^ 2)⁻¹ by rw [inv_pow]]
  have hkey : (B : ℝ) * ((B : ℝ) ^ 2)⁻¹ = ((B : ℝ))⁻¹ := by
    field_simp
  rw [hkey]
  have hmul : ((B : ℝ))⁻¹ * (B : ℝ) = 1 := inv_mul_cancel₀ (ne_of_gt hBpos)
  have hinvpos : (0 : ℝ) < ((B : ℝ))⁻¹ := inv_pos.2 hBpos
  nlinarith [mul_le_mul_of_nonneg_left hBR hinvpos.le]

theorem pipeNodeEnergy_le (hL : ∀ j, 1 ≤ j → 1 ≤ L j) (hL2 : ∀ j, 1 ≤ j → 2 ≤ L j)
    (hB : 1 ≤ B) {v : List (Fin B) × ℕ} (hv : PipeValid B L v) :
    pipeNodeEnergy B L v ≤ 2 * (((B : ℝ) ^ v.1.length) ^ 2)⁻¹ := by
  rcases hvv : v with ⟨w, i⟩
  rw [hvv] at hv
  rcases hv with h0 | ⟨hw, hi, hiL⟩
  · simp only at h0
    subst h0
    by_cases hwnil : w = []
    · subst hwnil
      exact pipeNodeEnergy_root hL2 hB
    · exact pipeNodeEnergy_branch hL hL2 hB hwnil
  · simp only at hw hi hiL
    exact le_of_eq (pipeNodeEnergy_interior hL hw hi hiL)

end RWRS.Support
