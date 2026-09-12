/-
Part (c) of `prop:comb-estimates`: the total voltage mass on the comb.

The comb is graded by the length of the word of a site.  At level `j` there are
at most `B + 1` words, namely `[]` and the `B` children of the trunk vertex
`b_{j-1}`, and at most `L_j` sites on each, so at most `(B+1)L_j` sites; and
every site at level `j` carries voltage at most `V_{j-1}`, because along each
pipe of the level the voltage decreases from its value at `b_{j-1}`.  With
part (a) that gives `∑_{u} g(u) ≤ ∑_{j=1}^{n} 4(B+1) I_j L_j^2`.
-/
import RWRS.Support.CombEst

namespace RWRS.Support

variable {B : ℕ} {L : ℕ → ℕ} {n : ℕ} {w : List (Fin B)}

/-! ### Sites of the comb -/

theorem combSet_interior_mem {v : List (Fin B)} (hvne : v ≠ [])
    (hvlen : v.length ≤ n) (hpre : v.dropLast <+: w) :
    ∀ i, 1 ≤ i → i ≤ L v.length - 1 → ((v : List (Fin B)), i) ∈ combSet B L n w :=
  fun _ hi hiL => ⟨Or.inr ⟨hvne, hi, hiL⟩, hvlen, hpre, Or.inl hi⟩

theorem dropLast_eq_take_of_mem {u : List (Fin B) × ℕ} (hu : u ∈ combSet B L n w) :
    u.1.dropLast = w.take (u.1.length - 1) := by
  obtain ⟨-, -, hpre, -⟩ := hu
  have := List.prefix_iff_eq_take.1 hpre
  rw [List.length_dropLast] at this
  exact this

theorem branch_of_snd_zero {u : List (Fin B) × ℕ} (hu : u ∈ combSet B L n w)
    (h0 : u.2 = 0) : u.1 = w.take u.1.length ∧ u.1.length < n := by
  obtain ⟨-, -, -, hlast⟩ := hu
  rcases hlast with h1 | ⟨hpre, hlt⟩
  · omega
  · exact ⟨List.prefix_iff_eq_take.1 hpre, hlt⟩

/-! ### The voltage at level `j` is at most `V_{j-1}` -/

theorem combVoltage_le_level (hB : 2 ≤ B) (hL2 : ∀ j, 1 ≤ j → 2 ≤ L j) (e : Bool)
    (hwn : w.length = n) (hn : 1 ≤ n) {j : ℕ} (hjn : j ≤ n)
    {u : List (Fin B) × ℕ} (hu : u ∈ combSet B L n w) (hlen : u.1.length = j) :
    combVoltage B L e n w u ≤ combV B L e n w (j - 1) := by
  obtain ⟨v, i⟩ := u
  simp only at hlen
  rcases Nat.eq_zero_or_pos j with hj0 | hj1
  · subst hj0
    have hvnil : v = [] := List.eq_nil_of_length_eq_zero hlen
    have hi0 : i = 0 := by
      rcases hu.1 with h0 | ⟨hne, -, -⟩
      · exact h0
      · exact absurd hvnil hne
    subst hvnil; subst hi0
    have : combV B L e n w 0 = combVoltage B L e n w (([] : List (Fin B)), 0) := by
      simp [combV, combBranch]
    simp only [Nat.zero_sub, this]
    exact le_rfl
  · rcases Nat.eq_zero_or_pos i with hi0 | hi1
    · subst hi0
      obtain ⟨hvw, hlt⟩ := branch_of_snd_zero hu rfl
      simp only at hvw
      rw [hlen] at hvw
      subst hvw
      have hstep := trunk_step hB hL2 e hwn hn (j := j) hj1 hjn
      have hI := combI_nonneg hB hL2 e hwn hn j hj1 hjn
      have hL := combLen_cast_pos hL2 (j := j) hj1
      have : combVoltage B L e n w ((w.take j : List (Fin B)), 0) = combV B L e n w j := by
        simp [combV, combBranch]
      rw [this]
      nlinarith
    · obtain ⟨hvne, -, hiL⟩ : v ≠ [] ∧ 1 ≤ i ∧ i ≤ L v.length - 1 := by
        rcases hu.1 with h0 | h
        · simp only at h0; omega
        · exact h
      have hpre : v.dropLast <+: w := hu.2.2.1
      have hdl : v.dropLast = w.take (j - 1) := by
        have := dropLast_eq_take_of_mem hu
        simpa [hlen] using this
      have haff := pipe_affine (B := B) (L := L) (by omega : 1 ≤ B)
        (one_le_of_two_le hL2) e hwn hn hvne
        (combSet_interior_mem hvne (by omega) hpre) i hiL
      rw [show pipeAt B v i = ((v : List (Fin B)), i) by simp [pipeAt]; omega] at haff
      have hdnn : 0 ≤ pipeDrop B L e n w v := by
        by_cases hvt : v = w.take j
        · rw [hvt, trunk_drop hL2 e hwn hj1 hjn]
          exact combI_nonneg hB hL2 e hwn hn j hj1 hjn
        · obtain ⟨c, hc⟩ : ∃ c : Fin B, v = w.take (j - 1) ++ [c] := by
            refine ⟨v.getLast hvne, ?_⟩
            rw [← hdl]
            exact (List.dropLast_append_getLast hvne).symm
          have hne : w.take (j - 1) ++ [c] ≠ w.take (j - 1 + 1) := by
            rw [show j - 1 + 1 = j by omega, ← hc]
            exact hvt
          have hsd := sibling_drop hB hL2 e hwn hn (j := j - 1) (by omega) hne
          rw [show j - 1 + 1 = j by omega, ← hc] at hsd
          have hVnn := combV_nonneg hL2 e hwn (j - 1)
          have hL := combLen_cast_pos hL2 (j := j) hj1
          nlinarith
      rw [haff, hdl]
      have : combVoltage B L e n w ((w.take (j - 1) : List (Fin B)), 0)
          = combV B L e n w (j - 1) := by simp [combV, combBranch]
      rw [this]
      have : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg _
      nlinarith

/-! ### There are at most `(B+1) L_j` sites at level `j` -/

open scoped Classical in
theorem card_level_le (hL2 : ∀ j, 1 ≤ j → 2 ≤ L j) (hL0 : 1 ≤ L 0) (j : ℕ) :
    ((combFinset B L n w).filter (fun u => u.1.length = j)).card ≤ (B + 1) * L j := by
  classical
  set T : Finset (List (Fin B)) :=
    ((Finset.univ : Finset (Fin B)).image fun c => w.take (j - 1) ++ [c])
      ∪ {([] : List (Fin B))} with hT
  have hsub : (combFinset B L n w).filter (fun u => u.1.length = j)
      ⊆ T ×ˢ Finset.range (L j) := by
    intro u hu
    rw [Finset.mem_filter] at hu
    obtain ⟨huC, hlen⟩ := hu
    have huS : u ∈ combSet B L n w := by
      rw [← coe_combFinset (B := B) (L := L) n w]; exact_mod_cast huC
    refine Finset.mem_product.2 ⟨?_, ?_⟩
    · rcases Nat.eq_zero_or_pos j with hj0 | hj1
      · have : u.1 = [] := List.eq_nil_of_length_eq_zero (by rw [hlen, hj0])
        rw [hT]
        exact Finset.mem_union_right _ (by simp [this])
      · have hvne : u.1 ≠ [] := by
          intro h
          rw [h] at hlen
          simp at hlen
          omega
        have hdl : u.1.dropLast = w.take (j - 1) := by
          have := dropLast_eq_take_of_mem huS
          simpa [hlen] using this
        refine Finset.mem_union_left _ (Finset.mem_image.2 ⟨u.1.getLast hvne, Finset.mem_univ _, ?_⟩)
        rw [← hdl]
        exact List.dropLast_append_getLast hvne
    · rw [Finset.mem_range]
      rcases Nat.eq_zero_or_pos u.2 with h0 | h1
      · rw [h0]
        rcases Nat.eq_zero_or_pos j with hj0 | hj1
        · rw [hj0]; omega
        · have := hL2 j hj1; omega
      · rcases huS.1 with h0 | ⟨-, -, hiL⟩
        · omega
        · rw [hlen] at hiL
          have hj1 : 1 ≤ j := by
            rcases Nat.eq_zero_or_pos j with hj0 | hj1
            · exfalso
              have : u.1 = [] := List.eq_nil_of_length_eq_zero (by rw [hlen, hj0])
              rcases huS.1 with h0 | ⟨hne, -, -⟩
              · omega
              · exact hne this
            · exact hj1
          have := hL2 j hj1
          omega
  calc ((combFinset B L n w).filter (fun u => u.1.length = j)).card
      ≤ (T ×ˢ Finset.range (L j)).card := Finset.card_le_card hsub
    _ = T.card * L j := by rw [Finset.card_product, Finset.card_range]
    _ ≤ (B + 1) * L j := by
        refine Nat.mul_le_mul_right _ ?_
        calc T.card ≤ ((Finset.univ : Finset (Fin B)).image
              fun c => w.take (j - 1) ++ [c]).card + ({([] : List (Fin B))} : Finset _).card :=
              Finset.card_union_le _ _
          _ ≤ B + 1 := by
              refine Nat.add_le_add ?_ (by simp)
              calc ((Finset.univ : Finset (Fin B)).image
                    fun c => w.take (j - 1) ++ [c]).card
                  ≤ (Finset.univ : Finset (Fin B)).card := Finset.card_image_le
                _ = B := by simp

/-! ### Part (c): the total voltage mass -/

open scoped Classical in
/-- **Part (c).**  The voltage mass of the comb is at most a geometric sum of
the level terms `I_j L_j^2`. -/
theorem comb_mass_le (hB : 2 ≤ B) (hL2 : ∀ j, 1 ≤ j → 2 ≤ L j) (hL0 : L 0 = 1)
    (hLstep : ∀ j, 1 ≤ j → (L (j + 1) : ℝ) ≤ ((B : ℝ) - 1) * (L j : ℝ))
    (e : Bool) (hwn : w.length = n) (hn : 1 ≤ n) :
    ∑ u ∈ combFinset B L n w, combVoltage B L e n w u
      ≤ ∑ j ∈ Finset.Icc 1 n, 4 * ((B : ℝ) + 1) * combI B L e n w j * (L j : ℝ) ^ 2 := by
  classical
  have hBc : (2 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
  -- the level decomposition
  have hmaps : ∀ u ∈ combFinset B L n w, u.1.length ∈ Finset.range (n + 1) := by
    intro u hu
    have huS : u ∈ combSet B L n w := by
      rw [← coe_combFinset (B := B) (L := L) n w]; exact_mod_cast hu
    exact Finset.mem_range.2 (by have := huS.2.1; omega)
  have hfib := Finset.sum_fiberwise_of_maps_to hmaps (fun u => combVoltage B L e n w u)
  rw [← hfib]
  -- each level
  have hlevel : ∀ j ∈ Finset.range (n + 1),
      (∑ u ∈ (combFinset B L n w).filter (fun u => u.1.length = j),
          combVoltage B L e n w u)
        ≤ ((B : ℝ) + 1) * (L j : ℝ) * combV B L e n w (j - 1) := by
    intro j hj
    have hjn : j ≤ n := by have := Finset.mem_range.1 hj; omega
    have hbound : ∀ u ∈ (combFinset B L n w).filter (fun u => u.1.length = j),
        combVoltage B L e n w u ≤ combV B L e n w (j - 1) := by
      intro u hu
      rw [Finset.mem_filter] at hu
      have huS : u ∈ combSet B L n w := by
        rw [← coe_combFinset (B := B) (L := L) n w]; exact_mod_cast hu.1
      exact combVoltage_le_level hB hL2 e hwn hn hjn huS hu.2
    have hcard := card_level_le hL2 (by omega : 1 ≤ L 0) (B := B) (L := L) (n := n) (w := w) j
    have hVnn := combV_nonneg hL2 e hwn (j - 1)
    calc (∑ u ∈ (combFinset B L n w).filter (fun u => u.1.length = j),
            combVoltage B L e n w u)
        ≤ (((combFinset B L n w).filter (fun u => u.1.length = j)).card : ℝ)
            * combV B L e n w (j - 1) := by
          have := Finset.sum_le_card_nsmul
            ((combFinset B L n w).filter (fun u => u.1.length = j))
            (fun u => combVoltage B L e n w u) (combV B L e n w (j - 1)) hbound
          simpa [nsmul_eq_mul] using this
      _ ≤ ((B : ℝ) + 1) * (L j : ℝ) * combV B L e n w (j - 1) := by
          have hc : (((combFinset B L n w).filter (fun u => u.1.length = j)).card : ℝ)
              ≤ ((B : ℝ) + 1) * (L j : ℝ) := by
            have := (Nat.cast_le (α := ℝ)).2 hcard
            push_cast at this
            linarith
          nlinarith
  refine le_trans (Finset.sum_le_sum hlevel) ?_
  -- split off the root level
  have hrange : Finset.range (n + 1) = insert 0 (Finset.Icc 1 n) := by
    ext k
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  have hnot : (0 : ℕ) ∉ Finset.Icc 1 n := by simp
  rw [hrange, Finset.sum_insert hnot]
  -- the root term
  have hroot : ((B : ℝ) + 1) * (L 0 : ℝ) * combV B L e n w (0 - 1)
      ≤ 2 * ((B : ℝ) + 1) * combI B L e n w 1 * (L 1 : ℝ) ^ 2 := by
    have hV0 := combV_le_two_mul hB hL2 hLstep e hwn hn (j := 0) (by omega)
    have hI1 := combI_nonneg hB hL2 e hwn hn 1 le_rfl hn
    have hL1 : (1 : ℝ) ≤ (L 1 : ℝ) := by
      have := hL2 1 le_rfl
      have : (1 : ℕ) ≤ L 1 := by omega
      exact_mod_cast this
    rw [hL0]
    simp only [Nat.zero_sub, Nat.cast_one, mul_one]
    rw [show (0 : ℕ) + 1 = 1 from rfl] at hV0
    have hB1 : (0 : ℝ) ≤ (B : ℝ) + 1 := by linarith
    have hsq : combI B L e n w 1 * (L 1 : ℝ) ≤ combI B L e n w 1 * (L 1 : ℝ) ^ 2 := by
      have hprod : (0 : ℝ) ≤ combI B L e n w 1 * ((L 1 : ℝ) * ((L 1 : ℝ) - 1)) :=
        mul_nonneg hI1 (mul_nonneg (by linarith) (by linarith))
      nlinarith [hprod]
    have step1 : ((B : ℝ) + 1) * combV B L e n w 0
        ≤ ((B : ℝ) + 1) * (2 * combI B L e n w 1 * (L 1 : ℝ)) :=
      mul_le_mul_of_nonneg_left hV0 hB1
    nlinarith [step1, hsq]
  -- the other levels
  have hother : ∀ j ∈ Finset.Icc 1 n,
      ((B : ℝ) + 1) * (L j : ℝ) * combV B L e n w (j - 1)
        ≤ 2 * ((B : ℝ) + 1) * combI B L e n w j * (L j : ℝ) ^ 2 := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    have hV := combV_le_two_mul hB hL2 hLstep e hwn hn (j := j - 1) (by omega)
    rw [show j - 1 + 1 = j by omega] at hV
    have hLnn : (0 : ℝ) ≤ (L j : ℝ) := Nat.cast_nonneg _
    have hcoef : (0 : ℝ) ≤ ((B : ℝ) + 1) * (L j : ℝ) := by nlinarith
    have := mul_le_mul_of_nonneg_left hV hcoef
    nlinarith [this]
  have hsum2 := Finset.sum_le_sum hother
  -- the root term is dominated by the level-one term
  have hone : (1 : ℕ) ∈ Finset.Icc 1 n := by simp [hn]
  have hnn : ∀ j ∈ Finset.Icc 1 n, (0 : ℝ)
      ≤ 2 * ((B : ℝ) + 1) * combI B L e n w j * (L j : ℝ) ^ 2 := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    have := combI_nonneg hB hL2 e hwn hn j hj.1 hj.2
    have hLnn : (0 : ℝ) ≤ (L j : ℝ) := Nat.cast_nonneg _
    positivity
  have hsingle := Finset.single_le_sum hnn hone
  have hsplit : ∑ j ∈ Finset.Icc 1 n, 4 * ((B : ℝ) + 1) * combI B L e n w j * (L j : ℝ) ^ 2
      = (∑ j ∈ Finset.Icc 1 n, 2 * ((B : ℝ) + 1) * combI B L e n w j * (L j : ℝ) ^ 2)
        + ∑ j ∈ Finset.Icc 1 n, 2 * ((B : ℝ) + 1) * combI B L e n w j * (L j : ℝ) ^ 2 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hsplit]
  linarith [hroot, hsum2, hsingle]

/-! ### Part (d): the spike contribution -/

open scoped Classical in
/-- The voltage on the first half of the terminal pipe is at least `I_n L_n/2`. -/
theorem combVoltage_firstHalf (hB : 2 ≤ B) (hL2 : ∀ j, 1 ≤ j → 2 ≤ L j) (e : Bool)
    (hwn : w.length = n) (hn : 1 ≤ n) {v : List (Fin B) × ℕ}
    (hv : v ∈ combFirstHalf B L n w) :
    (L n : ℝ) / 2 * combI B L e n w n ≤ combVoltage B L e n w v ∧
      v ∈ combSet B L n w := by
  obtain ⟨hv1, hv2, hv3⟩ := hv
  obtain ⟨u, i⟩ := v
  simp only at hv1 hv2 hv3
  rw [hv1]
  have hwtake : w.take n = w := by rw [← hwn]; simp
  have hLn : 2 ≤ L n := hL2 n hn
  have hiL : i ≤ L n - 1 := by omega
  have hmem : ((w : List (Fin B)), i) ∈ combSet B L n w := by
    have := mem_combSet_trunk (L := L) hwn hn le_rfl hv2 hiL
    rwa [hwtake] at this
  refine ⟨?_, hmem⟩
  have hlen : (w.take n).length = n := length_take_eq hwn le_rfl
  have haff := pipe_affine (B := B) (L := L) (by omega : 1 ≤ B)
    (one_le_of_two_le hL2) e hwn hn (take_ne_nil hwn hn le_rfl)
    (trunk_mem (L := L) hwn hn le_rfl) i (by rw [hlen]; omega)
  rw [show pipeAt B (w.take n) i = ((w.take n : List (Fin B)), i) by simp [pipeAt]; omega,
    dropLast_take hwn le_rfl, trunk_drop hL2 e hwn hn le_rfl, hwtake] at haff
  have hterm := terminal_step hB hL2 e hwn hn
  have hV : combVoltage B L e n w ((w.take (n - 1) : List (Fin B)), 0)
      = combV B L e n w (n - 1) := by simp [combV, combBranch]
  rw [hV, hterm] at haff
  have hI := combI_nonneg hB hL2 e hwn hn n hn le_rfl
  have hicast : (i : ℝ) ≤ (L n : ℝ) / 2 := by
    have : (2 : ℝ) * (i : ℝ) ≤ (L n : ℝ) := by exact_mod_cast hv3
    linarith
  rw [haff]
  nlinarith

open scoped Classical in
/-- **Part (d).**  A single site of the first half of the terminal pipe carrying
mass at least `K L_n - b` outweighs the negative background. -/
theorem comb_spike (hB : 2 ≤ B) (hL2 : ∀ j, 1 ≤ j → 2 ≤ L j) (e : Bool)
    (hwn : w.length = n) (hn : 1 ≤ n) {Ccomb : ℝ} (hC : 0 < Ccomb)
    (hmass : ∑ u ∈ combFinset B L n w, combVoltage B L e n w u
      ≤ Ccomb * combI B L e n w n * (L n : ℝ) ^ 2)
    (a : List (Fin B) × ℕ → ℝ) {b : ℝ} (hb : 0 ≤ b)
    (ha : ∀ u ∈ combSet B L n w, -b ≤ a u)
    {v : List (Fin B) × ℕ} (hv : v ∈ combFirstHalf B L n w)
    (hav : (2 + 2 * b * (Ccomb + 1)) * (L n : ℝ) - b ≤ a v) :
    combI B L e n w n * (L n : ℝ) ^ 2
      ≤ ∑ u ∈ combFinset B L n w, combVoltage B L e n w u * a u := by
  classical
  obtain ⟨hgv, hvmem⟩ := combVoltage_firstHalf hB hL2 e hwn hn hv
  have hvC : v ∈ combFinset B L n w := by
    rw [← Finset.mem_coe, coe_combFinset]; exact hvmem
  have hI := combI_nonneg hB hL2 e hwn hn n hn le_rfl
  have hLn : 2 ≤ L n := hL2 n hn
  have hLnr : (2 : ℝ) ≤ (L n : ℝ) := by exact_mod_cast hLn
  -- the sum away from the spike
  have hsplit := Finset.sum_erase_add (combFinset B L n w)
    (fun u => combVoltage B L e n w u * a u) hvC
  have hrest : -(b * (Ccomb * combI B L e n w n * (L n : ℝ) ^ 2))
      ≤ ∑ u ∈ (combFinset B L n w).erase v, combVoltage B L e n w u * a u := by
    have hterm : ∀ u ∈ (combFinset B L n w).erase v,
        -(b * combVoltage B L e n w u) ≤ combVoltage B L e n w u * a u := by
      intro u hu
      have huC : u ∈ combFinset B L n w := Finset.mem_of_mem_erase hu
      have huS : u ∈ combSet B L n w := by
        rw [← coe_combFinset (B := B) (L := L) n w]; exact_mod_cast huC
      have hgu := combVoltage_nonneg hL2 e hwn u
      nlinarith [ha u huS]
    have h1 := Finset.sum_le_sum hterm
    have h2 : ∑ u ∈ (combFinset B L n w).erase v, combVoltage B L e n w u
        ≤ ∑ u ∈ combFinset B L n w, combVoltage B L e n w u := by
      refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) ?_
      intro u _ _
      exact combVoltage_nonneg hL2 e hwn u
    have h3 : ∑ u ∈ (combFinset B L n w).erase v, -(b * combVoltage B L e n w u)
        = -(b * ∑ u ∈ (combFinset B L n w).erase v, combVoltage B L e n w u) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    rw [h3] at h1
    nlinarith [h1, h2, hmass]
  -- the spike term
  have hKnn : 0 ≤ (2 + 2 * b * (Ccomb + 1)) * (L n : ℝ) - b := by
    have h1 : (0 : ℝ) ≤ b * ((L n : ℝ) - 2) := mul_nonneg hb (by linarith)
    have h2 : (0 : ℝ) ≤ b * Ccomb * (L n : ℝ) :=
      mul_nonneg (mul_nonneg hb hC.le) (by linarith)
    nlinarith [h1, h2]
  have hgvnn : 0 ≤ combVoltage B L e n w v := combVoltage_nonneg hL2 e hwn v
  have hspike : (L n : ℝ) / 2 * combI B L e n w n
      * ((2 + 2 * b * (Ccomb + 1)) * (L n : ℝ) - b)
      ≤ combVoltage B L e n w v * a v := by
    have h1 : combVoltage B L e n w v * ((2 + 2 * b * (Ccomb + 1)) * (L n : ℝ) - b)
        ≤ combVoltage B L e n w v * a v := by nlinarith
    nlinarith
  -- assemble
  have hfin : combI B L e n w n * (L n : ℝ) ^ 2
      ≤ (L n : ℝ) / 2 * combI B L e n w n
          * ((2 + 2 * b * (Ccomb + 1)) * (L n : ℝ) - b)
        - b * (Ccomb * combI B L e n w n * (L n : ℝ) ^ 2) := by
    have hLsq : (L n : ℝ) ≤ (L n : ℝ) ^ 2 := by nlinarith
    nlinarith [mul_nonneg hI (mul_nonneg hb (sub_nonneg.2 hLsq))]
  linarith [hsplit, hrest, hspike]

end RWRS.Support
