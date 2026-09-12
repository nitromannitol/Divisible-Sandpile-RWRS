/-
The boundary value problem on the comb, and Kirchhoff's node law.

The voltage `g = g_{D_{w,n}}(b_0,·)` vanishes off the comb, is nonnegative, is
harmonic on the comb away from the root, and has Laplacian `-1` at the root.
Combined with the closed form of the voltage along a pipe this gives the three
identities the comb estimates are read from:

* the trunk step `V_{j-1} - V_j = I_j L_j`;
* the side current `V_j / L_{j+1}` on each of the `B-1` sibling pipes at `b_j`;
* the node law `I_j = I_{j+1} + (B-1) V_j / L_{j+1}` at `b_j` for `1 ≤ j < n`,
  and `1 = I_1 + (B-1) V_0 / L_1 + [e] V_0` at the root.
-/
import RWRS.Support.CombStruct

namespace RWRS.Support

variable {B : ℕ} {L : ℕ → ℕ} {n : ℕ} {w : List (Fin B)}

theorem one_le_of_two_le (hL2 : ∀ j, 1 ≤ j → 2 ≤ L j) : ∀ j, 1 ≤ j → 1 ≤ L j :=
  fun j hj => le_trans (by omega) (hL2 j hj)

/-! ### The boundary value problem -/

section BVP

open scoped Classical in
theorem comb_esc (hL2 : ∀ j, 1 ≤ j → 2 ≤ L j) (e : Bool) (hwn : w.length = n) :
    ∀ x : List (Fin B) × ℕ,
      ∃ (q : List (Fin B) × ℕ) (_ : (pipeGraph B L e).Walk x q),
        q ∉ combFinset B L n w := by
  classical
  intro x
  obtain ⟨q, p, hq⟩ := escape_combSet (one_le_of_two_le hL2) e hwn x
  refine ⟨q, p, ?_⟩
  rw [← Finset.mem_coe, coe_combFinset]
  exact hq

open scoped Classical in
theorem comb_deg (hL2 : ∀ j, 1 ≤ j → 2 ≤ L j) (e : Bool) (hB : 2 ≤ B) :
    ∀ v ∈ combFinset B L n w, 0 < (pipeGraph B L e).degree v := by
  classical
  intro v hv
  refine degree_pos_of_mem_combSet (B := B) (L := L) (n := n) (w := w)
    (by omega) (one_le_of_two_le hL2) e ?_
  rw [← coe_combFinset (B := B) (L := L) n w]
  exact_mod_cast hv

open scoped Classical in
theorem comb_root_mem (hn : 1 ≤ n) : pipeRoot B ∈ combFinset B L n w := by
  classical
  rw [← Finset.mem_coe, coe_combFinset]
  exact pipeRoot_mem_combSet w hn

open scoped Classical in
theorem combVoltage_nonneg (hL2 : ∀ j, 1 ≤ j → 2 ≤ L j) (e : Bool) (hwn : w.length = n)
    (v : List (Fin B) × ℕ) :
    0 ≤ combVoltage B L e n w v := by
  classical
  have h := killedGreenReal_nonneg_of_escape (G := pipeGraph B L e)
    (combFinset B L n w) (comb_esc hL2 e hwn) (pipeRoot B) v
  rwa [coe_combFinset] at h

open scoped Classical in
theorem combVoltage_eq_zero (hL2 : ∀ j, 1 ≤ j → 2 ≤ L j) (e : Bool) (hwn : w.length = n)
    {v : List (Fin B) × ℕ}
    (hv : v ∉ combSet B L n w) : combVoltage B L e n w v = 0 := by
  classical
  have hv' : v ∉ combFinset B L n w := by
    rw [← Finset.mem_coe, coe_combFinset]; exact hv
  have h := killedGreenReal_eq_zero_of_not_mem_of_escape (G := pipeGraph B L e)
    (combFinset B L n w) (comb_esc hL2 e hwn) hv' (pipeRoot B)
  rwa [coe_combFinset] at h

open scoped Classical in
theorem combVoltage_harmonic (hL2 : ∀ j, 1 ≤ j → 2 ≤ L j) (e : Bool) (hB : 2 ≤ B)
    (hwn : w.length = n) (hn : 1 ≤ n)
    {v : List (Fin B) × ℕ} (hv : v ∈ combSet B L n w) (hvo : v ≠ pipeRoot B) :
    laplacian (pipeGraph B L e) (combVoltage B L e n w) v = 0 := by
  classical
  have hvC : v ∈ combFinset B L n w := by
    rw [← Finset.mem_coe, coe_combFinset]; exact hv
  have h := harmonic_killedGreenReal_of_escape (G := pipeGraph B L e)
    (combFinset B L n w) (comb_esc hL2 e hwn) (comb_deg hL2 e hB)
    (comb_root_mem (L := L) (w := w) hn) hvC hvo
  rw [coe_combFinset] at h
  exact h

open scoped Classical in
theorem combVoltage_source (hL2 : ∀ j, 1 ≤ j → 2 ≤ L j) (e : Bool) (hB : 2 ≤ B)
    (hwn : w.length = n) (hn : 1 ≤ n) :
    laplacian (pipeGraph B L e) (combVoltage B L e n w) (pipeRoot B) = -1 := by
  classical
  have h := laplacian_killedGreenReal_source_of_escape (G := pipeGraph B L e)
    (combFinset B L n w) (comb_esc hL2 e hwn) (comb_deg hL2 e hB)
    (comb_root_mem (L := L) (w := w) hn)
  rw [coe_combFinset] at h
  exact h

end BVP

/-! ### The pipes of the comb -/

theorem dropLast_take (hwn : w.length = n) {j : ℕ} (hjn : j ≤ n) :
    (w.take j).dropLast = w.take (j - 1) := by
  rw [List.dropLast_eq_take, length_take_eq hwn hjn, List.take_take]
  congr 1
  omega

theorem trunk_mem (hwn : w.length = n) {j : ℕ} (hj : 1 ≤ j) (hjn : j ≤ n) :
    ∀ i, 1 ≤ i → i ≤ L (w.take j).length - 1 →
      ((w.take j : List (Fin B)), i) ∈ combSet B L n w := by
  intro i hi hiL
  rw [length_take_eq hwn hjn] at hiL
  exact mem_combSet_trunk hwn hj hjn hi hiL

theorem child_mem (hwn : w.length = n) {j : ℕ} (hjn : j < n) (c : Fin B) :
    ∀ i, 1 ≤ i → i ≤ L (w.take j ++ [c]).length - 1 →
      (((w.take j ++ [c] : List (Fin B))), i) ∈ combSet B L n w := by
  intro i hi hiL
  rw [show (w.take j ++ [c]).length = j + 1 by
    rw [List.length_append, length_take_eq hwn (by omega)]; simp] at hiL
  exact mem_combSet_child hwn hjn c hi hiL

section Pipes

/-- The drop across the first edge of the `j`-th trunk pipe is the trunk current
`I_j`. -/
theorem trunk_drop (hL2 : ∀ j, 1 ≤ j → 2 ≤ L j) (e : Bool) (hwn : w.length = n) {j : ℕ} (hj : 1 ≤ j) (hjn : j ≤ n) :
    pipeDrop B L e n w (w.take j) = combI B L e n w j := by
  rw [pipeDrop, combI, combBranch, dropLast_take hwn hjn,
    if_pos (hL2 j hj)]

/-- **The trunk step.**  `V_j = V_{j-1} - I_j L_j`. -/
theorem trunk_step (hB : 2 ≤ B) (hL2 : ∀ j, 1 ≤ j → 2 ≤ L j) (e : Bool) (hwn : w.length = n) (hn : 1 ≤ n) {j : ℕ} (hj : 1 ≤ j) (hjn : j ≤ n) :
    combV B L e n w j
      = combV B L e n w (j - 1) - (L j : ℝ) * combI B L e n w j := by
  have hlen : (w.take j).length = j := length_take_eq hwn hjn
  have hfar := pipe_far (B := B) (L := L) (by omega : 1 ≤ B) (one_le_of_two_le hL2) e hwn hn
    (take_ne_nil hwn hj hjn) (by rw [hlen]; exact hL2 j hj) (trunk_mem hwn hj hjn)
  rw [hlen] at hfar
  simp only [combV, combBranch]
  rw [hfar, dropLast_take hwn hjn, trunk_drop hL2 e hwn hj hjn]

/-- The voltage vanishes at the far endpoint of the terminal pipe. -/
theorem trunk_end (hL2 : ∀ j, 1 ≤ j → 2 ≤ L j) (e : Bool) (hwn : w.length = n) : combV B L e n w n = 0 :=
  combVoltage_eq_zero hL2 e hwn (not_mem_combSet_terminal hwn)

/-- The first interior site of the `j`-th trunk pipe. -/
theorem trunk_first (hB : 2 ≤ B) (hL2 : ∀ j, 1 ≤ j → 2 ≤ L j) (e : Bool) (hwn : w.length = n) (hn : 1 ≤ n) {j : ℕ} (hj : 1 ≤ j) (hjn : j ≤ n) :
    combVoltage B L e n w ((w.take j : List (Fin B)), 1)
      = combV B L e n w (j - 1) - combI B L e n w j := by
  have hlen : (w.take j).length = j := length_take_eq hwn hjn
  have h2 : 2 ≤ L (w.take j).length := by rw [hlen]; exact hL2 j hj
  have haff := pipe_affine (B := B) (L := L) (by omega : 1 ≤ B) (one_le_of_two_le hL2) e hwn hn
    (take_ne_nil hwn hj hjn) (trunk_mem hwn hj hjn) 1 (by omega)
  rw [show pipeAt B (w.take j) 1 = ((w.take j : List (Fin B)), 1) by simp [pipeAt],
    dropLast_take hwn hjn, trunk_drop hL2 e hwn hj hjn] at haff
  simp only [combV, combBranch]
  rw [haff]
  push_cast
  ring

/-- The last interior site of the `j`-th trunk pipe carries `V_j + I_j`. -/
theorem trunk_last (hB : 2 ≤ B) (hL2 : ∀ j, 1 ≤ j → 2 ≤ L j) (e : Bool) (hwn : w.length = n) (hn : 1 ≤ n) {j : ℕ} (hj : 1 ≤ j) (hjn : j ≤ n) :
    combVoltage B L e n w ((w.take j : List (Fin B)), L j - 1)
      = combV B L e n w j + combI B L e n w j := by
  have hlen : (w.take j).length = j := length_take_eq hwn hjn
  have h2 : 2 ≤ L j := hL2 j hj
  have haff := pipe_affine (B := B) (L := L) (by omega : 1 ≤ B) (one_le_of_two_le hL2) e hwn hn
    (take_ne_nil hwn hj hjn) (trunk_mem hwn hj hjn) (L j - 1) (by rw [hlen])
  rw [show pipeAt B (w.take j) (L j - 1) = ((w.take j : List (Fin B)), L j - 1) by
      simp [pipeAt]; omega,
    dropLast_take hwn hjn, trunk_drop hL2 e hwn hj hjn] at haff
  have hstep := trunk_step hB hL2 e hwn hn hj hjn
  simp only [combV, combBranch] at hstep ⊢
  have hcast : ((L j - 1 : ℕ) : ℝ) = (L j : ℝ) - 1 := by
    have h1 : (1 : ℕ) ≤ L j := by omega
    have := Nat.cast_sub (R := ℝ) h1
    simpa using this
  rw [haff, hstep, hcast]
  ring

/-- The drop across the first edge of a sibling pipe at `b_j` is `V_j/L_{j+1}`,
because the far endpoint of a sibling pipe is outside the comb. -/
theorem sibling_drop (hB : 2 ≤ B) (hL2 : ∀ j, 1 ≤ j → 2 ≤ L j) (e : Bool) (hwn : w.length = n) (hn : 1 ≤ n) {j : ℕ} (hjn : j < n) {c : Fin B}
    (hc : w.take j ++ [c] ≠ w.take (j + 1)) :
    pipeDrop B L e n w (w.take j ++ [c]) * (L (j + 1) : ℝ) = combV B L e n w j := by
  have hlen : (w.take j ++ [c]).length = j + 1 := by
    rw [List.length_append, length_take_eq hwn (by omega)]; simp
  have hfar := pipe_far (B := B) (L := L) (by omega : 1 ≤ B) (one_le_of_two_le hL2) e hwn hn
    (by simp : (w.take j ++ [c] : List (Fin B)) ≠ [])
    (by rw [hlen]; exact hL2 (j + 1) (by omega)) (child_mem hwn hjn c)
  rw [hlen, List.dropLast_concat] at hfar
  have hzero : combVoltage B L e n w (((w.take j ++ [c] : List (Fin B))), 0) = 0 :=
    combVoltage_eq_zero hL2 e hwn (not_mem_combSet_sibling hwn hjn hc)
  rw [hzero] at hfar
  rw [combV, combBranch]
  linarith [hfar]

/-- The first interior site of a sibling pipe at `b_j`. -/
theorem sibling_first (hB : 2 ≤ B) (hL2 : ∀ j, 1 ≤ j → 2 ≤ L j) (e : Bool) (hwn : w.length = n) (hn : 1 ≤ n) {j : ℕ} (hjn : j < n) {c : Fin B}
    (hc : w.take j ++ [c] ≠ w.take (j + 1)) :
    combVoltage B L e n w (((w.take j ++ [c] : List (Fin B))), 1) * (L (j + 1) : ℝ)
      = combV B L e n w j * (L (j + 1) : ℝ) - combV B L e n w j := by
  have hlen : (w.take j ++ [c]).length = j + 1 := by
    rw [List.length_append, length_take_eq hwn (by omega)]; simp
  have h2 : 2 ≤ L (w.take j ++ [c]).length := by rw [hlen]; exact hL2 (j + 1) (by omega)
  have haff := pipe_affine (B := B) (L := L) (by omega : 1 ≤ B) (one_le_of_two_le hL2) e hwn hn
    (by simp : (w.take j ++ [c] : List (Fin B)) ≠ []) (child_mem hwn hjn c) 1 (by omega)
  rw [show pipeAt B (w.take j ++ [c]) 1 = (((w.take j ++ [c] : List (Fin B))), 1) by
      simp [pipeAt],
    List.dropLast_concat] at haff
  have hdrop := sibling_drop hB hL2 e hwn hn hjn hc
  rw [combV, combBranch] at hdrop ⊢
  push_cast at haff ⊢
  nlinarith [haff, hdrop]

/-- The first interior site of the trunk continuation at `b_j`. -/
theorem trunk_child_first (hB : 2 ≤ B) (hL2 : ∀ j, 1 ≤ j → 2 ≤ L j) (e : Bool) (hwn : w.length = n) (hn : 1 ≤ n) {j : ℕ} (hjn : j < n) {c : Fin B}
    (hc : w.take j ++ [c] = w.take (j + 1)) :
    combVoltage B L e n w (((w.take j ++ [c] : List (Fin B))), 1)
      = combV B L e n w j - combI B L e n w (j + 1) := by
  rw [hc]
  have := trunk_first hB hL2 e hwn hn (j := j + 1) (by omega) (by omega)
  simpa using this

/-! ### Kirchhoff's node law -/

theorem take_ne_root (hwn : w.length = n) {j : ℕ} (hj : 1 ≤ j) (hjn : j ≤ n) :
    ((w.take j : List (Fin B)), 0) ≠ pipeRoot B := by
  intro h
  exact take_ne_nil hwn hj hjn (congrArg Prod.fst h)

/-- **The node law at a trunk branching vertex.**  The trunk current `I_j`
entering `b_j` splits into the continuation `I_{j+1}` and the `B-1` side
currents `V_j/L_{j+1}`. -/
theorem node_law_branch (hB : 2 ≤ B) (hL2 : ∀ j, 1 ≤ j → 2 ≤ L j) (e : Bool)
    (hwn : w.length = n) (hn : 1 ≤ n) {j : ℕ} (hj : 1 ≤ j) (hjn : j < n) :
    combI B L e n w j * (L (j + 1) : ℝ)
      = combI B L e n w (j + 1) * (L (j + 1) : ℝ)
        + ((B : ℝ) - 1) * combV B L e n w j := by
  classical
  obtain ⟨c₀, hc₀⟩ := take_succ_eq hwn hjn
  have hlen : (w.take j).length = j := length_take_eq hwn (by omega)
  have hharm := combVoltage_harmonic hL2 e hB hwn hn
    (mem_combSet_branch (L := L) hwn hjn) (take_ne_root hwn hj (by omega))
  rw [laplacian_branch hL2 e (take_ne_nil hwn hj (by omega)), hlen] at hharm
  -- the parent side
  have hpar := trunk_last hB hL2 e hwn hn hj (by omega)
  -- the trunk continuation
  have hcont := trunk_child_first hB hL2 e hwn hn hjn hc₀.symm
  -- the sibling terms
  have hsib : ∀ c ∈ (Finset.univ : Finset (Fin B)).erase c₀,
      (combVoltage B L e n w (((w.take j ++ [c] : List (Fin B))), 1)
        - combVoltage B L e n w ((w.take j : List (Fin B)), 0)) * (L (j + 1) : ℝ)
        = - combV B L e n w j := by
    intro c hc
    have hcne : c ≠ c₀ := (Finset.mem_erase.1 hc).1
    have hne : w.take j ++ [c] ≠ w.take (j + 1) := by
      rw [hc₀]
      intro h
      exact hcne (by simpa using h)
    have := sibling_first hB hL2 e hwn hn hjn hne
    simp only [combV, combBranch] at this ⊢
    ring_nf
    ring_nf at this
    linarith
  have hcard : ((Finset.univ : Finset (Fin B)).erase c₀).card = B - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  have hsplit := Finset.sum_erase_add (Finset.univ : Finset (Fin B))
    (fun c => combVoltage B L e n w (((w.take j ++ [c] : List (Fin B))), 1)
      - combVoltage B L e n w ((w.take j : List (Fin B)), 0)) (Finset.mem_univ c₀)
  have hsumval : (∑ c ∈ (Finset.univ : Finset (Fin B)).erase c₀,
      (combVoltage B L e n w (((w.take j ++ [c] : List (Fin B))), 1)
        - combVoltage B L e n w ((w.take j : List (Fin B)), 0))) * (L (j + 1) : ℝ)
      = -(((B : ℝ) - 1) * combV B L e n w j) := by
    rw [Finset.sum_mul, Finset.sum_congr rfl hsib, Finset.sum_const, hcard]
    have hBcast : ((B - 1 : ℕ) : ℝ) = (B : ℝ) - 1 := by
      have h1 : (1 : ℕ) ≤ B := by omega
      have := Nat.cast_sub (R := ℝ) h1
      simpa using this
    rw [nsmul_eq_mul, hBcast]
    ring
  -- assemble
  have hzero : (combVoltage B L e n w ((w.take j : List (Fin B)), L j - 1)
      - combVoltage B L e n w ((w.take j : List (Fin B)), 0))
      + (∑ c ∈ (Finset.univ : Finset (Fin B)).erase c₀,
          (combVoltage B L e n w (((w.take j ++ [c] : List (Fin B))), 1)
            - combVoltage B L e n w ((w.take j : List (Fin B)), 0)))
      + (combVoltage B L e n w (((w.take j ++ [c₀] : List (Fin B))), 1)
          - combVoltage B L e n w ((w.take j : List (Fin B)), 0)) = 0 := by
    rw [add_assoc, hsplit]
    linarith [hharm]
  simp only [combV, combBranch] at hpar hcont hsumval ⊢
  linear_combination (L (j + 1) : ℝ) * hzero - hsumval - (L (j + 1) : ℝ) * hpar
    - (L (j + 1) : ℝ) * hcont

/-- **The node law at the root.**  Unit current enters at `b_0`. -/
theorem node_law_root (hB : 2 ≤ B) (hL2 : ∀ j, 1 ≤ j → 2 ≤ L j) (e : Bool)
    (hwn : w.length = n) (hn : 1 ≤ n) :
    (L 1 : ℝ)
      = combI B L e n w 1 * (L 1 : ℝ) + ((B : ℝ) - 1) * combV B L e n w 0
        + (if e then combV B L e n w 0 * (L 1 : ℝ) else 0) := by
  classical
  obtain ⟨c₀, hc₀⟩ := take_succ_eq hwn (show 0 < n by omega)
  have hsrc := combVoltage_source hL2 e hB hwn hn
  rw [pipeRoot, laplacian_root hL2 e] at hsrc
  have hextra : combVoltage B L e n w (([] : List (Fin B)), 1) = 0 := by
    refine combVoltage_eq_zero hL2 e hwn ?_
    rintro ⟨hval, -, -, -⟩
    rcases hval with h0 | ⟨hne, -, -⟩
    · exact absurd h0 (by simp)
    · exact hne rfl
  have hroot : combV B L e n w 0 = combVoltage B L e n w (([] : List (Fin B)), 0) := by
    simp [combV, combBranch]
  have hcont := trunk_child_first hB hL2 e hwn (by omega) (show (0 : ℕ) < n by omega) hc₀.symm
  have hcont' : combVoltage B L e n w (([c₀] : List (Fin B)), 1)
      = combV B L e n w 0 - combI B L e n w 1 := by simpa using hcont
  have hsib : ∀ c ∈ (Finset.univ : Finset (Fin B)).erase c₀,
      (combVoltage B L e n w (([c] : List (Fin B)), 1)
        - combVoltage B L e n w (([] : List (Fin B)), 0)) * (L 1 : ℝ)
        = - combV B L e n w 0 := by
    intro c hc
    have hcne : c ≠ c₀ := (Finset.mem_erase.1 hc).1
    have hne : w.take 0 ++ [c] ≠ w.take (0 + 1) := by
      intro h
      apply hcne
      have h2 : (w.take 0 ++ [c] : List (Fin B)) = w.take 0 ++ [c₀] := by rw [h]; exact hc₀
      simpa using h2
    have := sibling_first hB hL2 e hwn hn (show (0 : ℕ) < n by omega) hne
    simp only [List.take_zero, List.nil_append, Nat.zero_add] at this
    rw [hroot]
    simp only [combV, combBranch, List.take_zero] at this ⊢
    linarith
  have hcard : ((Finset.univ : Finset (Fin B)).erase c₀).card = B - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  have hsplit := Finset.sum_erase_add (Finset.univ : Finset (Fin B))
    (fun c => combVoltage B L e n w (([c] : List (Fin B)), 1)
      - combVoltage B L e n w (([] : List (Fin B)), 0)) (Finset.mem_univ c₀)
  have hsumval : (∑ c ∈ (Finset.univ : Finset (Fin B)).erase c₀,
      (combVoltage B L e n w (([c] : List (Fin B)), 1)
        - combVoltage B L e n w (([] : List (Fin B)), 0))) * (L 1 : ℝ)
      = -(((B : ℝ) - 1) * combV B L e n w 0) := by
    rw [Finset.sum_mul, Finset.sum_congr rfl hsib, Finset.sum_const, hcard]
    have hBcast : ((B - 1 : ℕ) : ℝ) = (B : ℝ) - 1 := by
      have h1 : (1 : ℕ) ≤ B := by omega
      have := Nat.cast_sub (R := ℝ) h1
      simpa using this
    rw [nsmul_eq_mul, hBcast]
    ring
  have hLpos : (0 : ℝ) < (L 1 : ℝ) := by
    have := hL2 1 le_rfl
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_two this
  rw [← hsplit] at hsrc
  rw [hextra] at hsrc
  cases e with
  | false =>
      simp only [Bool.false_eq_true, if_false] at hsrc ⊢
      nlinarith [hsrc, hsumval, hcont', hroot]
  | true =>
      simp only [if_true] at hsrc ⊢
      nlinarith [hsrc, hsumval, hcont', hroot]

end Pipes

end RWRS.Support
