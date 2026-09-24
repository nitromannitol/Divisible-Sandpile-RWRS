/-
The balls of the gadget `H(m)`.

Every site of the tree of pipes carries a depth: the branching vertex indexed by
a word of length `j` is at depth `R_j`, and the `i`-th interior site of the pipe
ending there is at depth `R_{j-1} + i`.  Along an edge the depth moves by at
most one, so the depth is a lower bound for the distance to the root, and a site
of the ball of radius `t` has depth at most `t`.  That bounds both the length of
its word and its position inside its pipe, which is what makes the ball small.
-/
import RWRS.Support.Gadget
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.Fintype.BigOperators

namespace RWRS.Support

variable {B : ℕ} {L : ℕ → ℕ}

/-! ### The radius as a function of the level -/

theorem gadgetRadius_zero (L : ℕ → ℕ) : gadgetRadius L 0 = 0 := rfl

theorem gadgetRadius_succ (L : ℕ → ℕ) (k : ℕ) :
    gadgetRadius L (k + 1) = gadgetRadius L k + L (k + 1) := by
  rw [gadgetRadius, gadgetRadius, Finset.sum_Icc_succ_top (Nat.le_add_left 1 k)]

theorem gadgetRadius_mono (L : ℕ → ℕ) {j k : ℕ} (h : j ≤ k) :
    gadgetRadius L j ≤ gadgetRadius L k :=
  Finset.sum_le_sum_of_subset (Finset.Icc_subset_Icc_right h)

/-! ### The depth of a site -/

/-- The depth of a site of the tree of pipes: the distance from the root along
the unique path of the tree. -/
def pipeDepth (L : ℕ → ℕ) (v : List (Fin B) × ℕ) : ℕ :=
  if v.2 = 0 then gadgetRadius L v.1.length else gadgetRadius L (v.1.length - 1) + v.2

theorem pipeDepth_root (L : ℕ → ℕ) :
    pipeDepth L (pipeRoot B) = 0 := by
  simp [pipeDepth, pipeRoot, gadgetRadius_zero]

/-- The depth of a site is at least the radius of the level below its word. -/
theorem gadgetRadius_pred_le_pipeDepth (L : ℕ → ℕ) (v : List (Fin B) × ℕ) :
    gadgetRadius L (v.1.length - 1) ≤ pipeDepth L v := by
  rw [pipeDepth]
  split
  · exact gadgetRadius_mono L (Nat.sub_le _ _)
  · exact Nat.le_add_right _ _

theorem snd_le_pipeDepth (L : ℕ → ℕ) (v : List (Fin B) × ℕ) : v.2 ≤ pipeDepth L v := by
  rw [pipeDepth]
  split
  · next h => omega
  · exact Nat.le_add_left _ _

theorem pipeDepth_zero (L : ℕ → ℕ) (w : List (Fin B)) :
    pipeDepth L (w, 0) = gadgetRadius L w.length := by
  rw [pipeDepth]; simp

theorem pipeDepth_succ' (L : ℕ → ℕ) (w : List (Fin B)) (i : ℕ) :
    pipeDepth L (w, i + 1) = gadgetRadius L (w.length - 1) + (i + 1) := by
  rw [pipeDepth]; simp

/-- Moving one step nearer the root does not increase the depth, and decreases
it by at most one. -/
theorem pipeDepth_pred (L : ℕ → ℕ) (v : List (Fin B) × ℕ) :
    pipeDepth L (pipePred B L v) ≤ pipeDepth L v ∧
      pipeDepth L v ≤ pipeDepth L (pipePred B L v) + 1 := by
  obtain ⟨w, i⟩ := v
  match i with
  | 0 =>
      by_cases hw : w = []
      · subst hw
        simp [pipePred]
      · have hlen : 1 ≤ w.length := List.length_pos_iff.2 hw
        obtain ⟨j, hj⟩ : ∃ j, w.length = j + 1 := ⟨w.length - 1, by omega⟩
        have hv : pipeDepth L (w, 0) = gadgetRadius L j + L w.length := by
          rw [pipeDepth_zero, hj, gadgetRadius_succ, ← hj]
        by_cases hL : 2 ≤ L w.length
        · simp only [pipePred, if_neg hw, if_pos hL]
          have hs : L w.length - 1 = (L w.length - 2) + 1 := by omega
          have hp : pipeDepth L (w, L w.length - 1)
              = gadgetRadius L j + (L w.length - 1) := by
            rw [hs, pipeDepth_succ', hj]
            simp
          omega
        · simp only [pipePred, if_neg hw, if_neg hL]
          have hp : pipeDepth L (w.dropLast, 0) = gadgetRadius L j := by
            rw [pipeDepth_zero, List.length_dropLast, hj]
            simp
          omega
  | i + 1 =>
      have hv : pipeDepth L (w, i + 1) = gadgetRadius L (w.length - 1) + (i + 1) :=
        pipeDepth_succ' L w i
      by_cases hi : i = 0
      · subst hi
        have hpe : pipePred B L ((w : List (Fin B)), 0 + 1) = (w.dropLast, 0) := by
          simp [pipePred]
        rw [hpe]
        have hp : pipeDepth L (w.dropLast, 0) = gadgetRadius L (w.length - 1) := by
          rw [pipeDepth_zero, List.length_dropLast]
        omega
      · simp only [pipePred, if_neg hi]
        obtain ⟨k, hk⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
        have hp : pipeDepth L (w, i) = gadgetRadius L (w.length - 1) + i := by
          rw [hk, pipeDepth_succ']
        omega

theorem pipeDepth_adj {e : Bool} {u v : List (Fin B) × ℕ}
    (h : (pipeGraph B L e).Adj u v) : pipeDepth L v ≤ pipeDepth L u + 1 := by
  rcases h.2.2.2 with hv | hu
  · subst hv
    exact le_trans (pipeDepth_pred L u).1 (Nat.le_succ _)
  · subst hu
    exact (pipeDepth_pred L v).2

/-! ### The depth is a lower bound for the distance to the root -/

theorem pipeDepth_le_walk_length {m : ℕ} {u v : gadgetSites B L m}
    (p : (gadgetGraph B L m).Walk u v) :
    pipeDepth L (v : List (Fin B) × ℕ)
      ≤ pipeDepth L (u : List (Fin B) × ℕ) + p.length := by
  induction p with
  | nil => simp
  | @cons a b c h q ih =>
      have hadj : (pipeGraph B L false).Adj (a : List (Fin B) × ℕ) (b : List (Fin B) × ℕ) := h
      have hstep := pipeDepth_adj hadj
      simp only [SimpleGraph.Walk.length_cons]
      omega

theorem pipeDepth_le_of_mem_ball {m t : ℕ} {v : gadgetSites B L m}
    (hv : v ∈ closedBall (gadgetGraph B L m) (gadgetRoot B L m) t) :
    pipeDepth L (v : List (Fin B) × ℕ) ≤ t := by
  have hedist : (gadgetGraph B L m).edist v (gadgetRoot B L m) ≤ (t : ℕ∞) := hv
  have hne : (gadgetGraph B L m).edist v (gadgetRoot B L m) ≠ ⊤ := by
    intro h
    rw [h] at hedist
    exact (by simp : ¬ ((⊤ : ℕ∞) ≤ (t : ℕ∞))) hedist
  obtain ⟨p, hp⟩ :=
    (SimpleGraph.reachable_of_edist_ne_top hne).exists_walk_length_eq_edist
  have hlen : (p.length : ℕ∞) ≤ (t : ℕ∞) := by rw [hp]; exact hedist
  have hlen' : p.length ≤ t := by exact_mod_cast hlen
  have hroot : pipeDepth L ((gadgetRoot B L m : List (Fin B) × ℕ)) = 0 :=
    pipeDepth_root L
  have hmain := pipeDepth_le_walk_length p.reverse
  rw [SimpleGraph.Walk.length_reverse] at hmain
  omega

/-! ### The level reached by a radius -/

/-- The first level whose radius reaches `t`. -/
noncomputable def gadgetLevel (L : ℕ → ℕ) (t : ℕ) : ℕ := sInf {k | t ≤ gadgetRadius L k}

theorem le_gadgetRadius_gadgetLevel (L : ℕ → ℕ) {t m : ℕ} (h : t ≤ gadgetRadius L m) :
    t ≤ gadgetRadius L (gadgetLevel L t) := by
  have hm : sInf {k | t ≤ gadgetRadius L k} ∈ {k | t ≤ gadgetRadius L k} :=
    Nat.sInf_mem ⟨m, h⟩
  exact hm

theorem gadgetRadius_lt_of_lt_gadgetLevel (L : ℕ → ℕ) {t k : ℕ}
    (h : k < gadgetLevel L t) : gadgetRadius L k < t := by
  by_contra hcon
  have hk : k ∈ {k | t ≤ gadgetRadius L k} := Nat.le_of_not_lt hcon
  have hle := Nat.sInf_le hk
  simp only [gadgetLevel] at h
  omega

variable {α : ℝ}

/-- A site of depth at most `t` lies in a level at most one beyond the level
whose radius first reaches `t`. -/
theorem word_length_le_of_depth (hc : CombCond B α) {t m : ℕ}
    (htm : t ≤ gadgetRadius (combLen B α) m)
    {v : List (Fin B) × ℕ} (hd : pipeDepth (combLen B α) v ≤ t) :
    v.1.length ≤ gadgetLevel (combLen B α) t + 1 := by
  by_contra hcon0
  have hcon : gadgetLevel (combLen B α) t + 1 < v.1.length := Nat.lt_of_not_le hcon0
  set j := gadgetLevel (combLen B α) t with hjdef
  have h1 : gadgetRadius (combLen B α) (j + 1)
      ≤ gadgetRadius (combLen B α) (v.1.length - 1) :=
    gadgetRadius_mono _ (by omega)
  have h2 := gadgetRadius_pred_le_pipeDepth (combLen B α) v
  have h3 : t ≤ gadgetRadius (combLen B α) j := le_gadgetRadius_gadgetLevel _ htm
  have h4 : gadgetRadius (combLen B α) (j + 1)
      = gadgetRadius (combLen B α) j + combLen B α (j + 1) := gadgetRadius_succ _ j
  have h5 : 0 < combLen B α (j + 1) := combLen_pos hc (by omega)
  omega

/-! ### Counting the sites of bounded level and position -/

open scoped Classical in
/-- The words of length at most `K`. -/
noncomputable def wordsLe (B K : ℕ) : Finset (List (Fin B)) :=
  (Finset.range (K + 1)).biUnion fun k =>
    (Finset.univ : Finset (List.Vector (Fin B) k)).image Subtype.val

open scoped Classical in
theorem mem_wordsLe {B K : ℕ} {w : List (Fin B)} (h : w.length ≤ K) :
    w ∈ wordsLe B K := by
  refine Finset.mem_biUnion.2 ⟨w.length, Finset.mem_range.2 (by omega), ?_⟩
  set v : List.Vector (Fin B) w.length := ⟨w, rfl⟩ with hvdef
  exact Finset.mem_image.2 ⟨v, Finset.mem_univ v, rfl⟩

open scoped Classical in
theorem card_wordsLe (B K : ℕ) : (wordsLe B K).card ≤ ∑ k ∈ Finset.range (K + 1), B ^ k := by
  refine le_trans Finset.card_biUnion_le (Finset.sum_le_sum fun k _ => ?_)
  have h1 : ((Finset.univ : Finset (List.Vector (Fin B) k)).image Subtype.val).card
      ≤ (Finset.univ : Finset (List.Vector (Fin B) k)).card := Finset.card_image_le
  have h2 : (Finset.univ : Finset (List.Vector (Fin B) k)).card = B ^ k := by
    simp [Finset.card_univ]
  omega

theorem sum_pow_range_le {B K : ℕ} (hB : 2 ≤ B) :
    ∑ k ∈ Finset.range (K + 1), B ^ k ≤ 2 * B ^ K := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Finset.sum_range_succ]
      have hstep : B ^ K * 2 ≤ B ^ K * B := Nat.mul_le_mul_left _ hB
      have hpow : B ^ (K + 1) = B ^ K * B := pow_succ B K
      omega

/-! ### The ball of the gadget -/

open scoped Classical in
theorem encard_ball_le_card (hc : CombCond B α) {m t : ℕ}
    (htm : t ≤ gadgetRadius (combLen B α) m) :
    (closedBall (gadgetGraph B (combLen B α) m) (gadgetRoot B (combLen B α) m) t
        \ {gadgetRoot B (combLen B α) m}).encard
      ≤ (((wordsLe B (gadgetLevel (combLen B α) t + 1)).card * (t + 1) : ℕ) : ℕ∞) := by
  classical
  set K := gadgetLevel (combLen B α) t + 1 with hK
  set S := closedBall (gadgetGraph B (combLen B α) m) (gadgetRoot B (combLen B α) m) t
      \ {gadgetRoot B (combLen B α) m} with hS
  set F : Finset (List (Fin B) × ℕ) := (wordsLe B K) ×ˢ Finset.range (t + 1) with hF
  have hinj : Set.InjOn
      (Subtype.val : gadgetSites B (combLen B α) m → List (Fin B) × ℕ) S :=
    Subtype.val_injective.injOn
  have hsub : (Subtype.val '' S) ⊆ (↑F : Set (List (Fin B) × ℕ)) := by
    rintro _ ⟨v, hv, rfl⟩
    have hd : pipeDepth (combLen B α) (v : List (Fin B) × ℕ) ≤ t :=
      pipeDepth_le_of_mem_ball hv.1
    have h1 : (v : List (Fin B) × ℕ).1.length ≤ K := word_length_le_of_depth hc htm hd
    have h2 : (v : List (Fin B) × ℕ).2 ≤ t := le_trans (snd_le_pipeDepth _ _) hd
    exact Finset.mem_coe.2
      (Finset.mem_product.2 ⟨mem_wordsLe h1, Finset.mem_range.2 (by omega)⟩)
  calc S.encard = (Subtype.val '' S).encard := (hinj.encard_image).symm
    _ ≤ (↑F : Set (List (Fin B) × ℕ)).encard := Set.encard_le_encard hsub
    _ = (F.card : ℕ∞) := Set.encard_coe_eq_coe_finsetCard F
    _ = _ := by rw [hF, Finset.card_product, Finset.card_range]

/-! ### The ball against a power of its radius -/

theorem base_pow_rpow_inv (hc : CombCond B α) (k : ℕ) :
    (((B : ℝ) ^ α) ^ k) ^ (1 / α) = (B : ℝ) ^ k := by
  have hB0 : (0 : ℝ) ≤ (B : ℝ) := (cast_B_pos hc).le
  have hα : α ≠ 0 := (alpha_pos hc).ne'
  have hexp : α * (k : ℝ) * (1 / α) = (k : ℝ) := by field_simp
  rw [← Real.rpow_natCast ((B : ℝ) ^ α) k, ← Real.rpow_mul hB0, ← Real.rpow_mul hB0,
    hexp, Real.rpow_natCast]

theorem pow_le_rpow_inv (hc : CombCond B α) {k : ℕ} {x : ℝ}
    (h : ((B : ℝ) ^ α) ^ k ≤ x) : (B : ℝ) ^ k ≤ x ^ (1 / α) := by
  have hαinv : (0 : ℝ) < 1 / α := by have := alpha_pos hc; positivity
  have h1 : (((B : ℝ) ^ α) ^ k) ^ (1 / α) ≤ x ^ (1 / α) :=
    Real.rpow_le_rpow (pow_nonneg (base_pos hc).le k) h hαinv.le
  rwa [base_pow_rpow_inv hc k] at h1

theorem base_level_le (hc : CombCond B α) {t : ℕ} (ht : 1 ≤ t) :
    (B : ℝ) ^ (gadgetLevel (combLen B α) t + 1)
      ≤ (B : ℝ) ^ 2 * (2 * (t : ℝ)) ^ (1 / α) := by
  set j := gadgetLevel (combLen B α) t with hj
  have hBpos := cast_B_pos hc
  have hB2 := cast_B_ge hc
  have hαinv : (0 : ℝ) < 1 / α := by have := alpha_pos hc; positivity
  have ht1 : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  have h2t : (1 : ℝ) ≤ 2 * (t : ℝ) := by linarith
  have hone : (1 : ℝ) ≤ (2 * (t : ℝ)) ^ (1 / α) := by
    calc (1 : ℝ) = (1 : ℝ) ^ (1 / α) := (Real.one_rpow _).symm
      _ ≤ (2 * (t : ℝ)) ^ (1 / α) := Real.rpow_le_rpow (by norm_num) h2t hαinv.le
  rcases Nat.lt_or_ge j 2 with hj2 | hj2
  · have hle : (B : ℝ) ^ (j + 1) ≤ (B : ℝ) ^ 2 :=
      pow_le_pow_right₀ (by linarith) (by omega)
    nlinarith [hle, hone, pow_pos hBpos 2]
  · have hlt : gadgetRadius (combLen B α) (j - 1) < t :=
      gadgetRadius_lt_of_lt_gadgetLevel _ (by omega)
    have hLle : combLen B α (j - 1) ≤ gadgetRadius (combLen B α) (j - 1) :=
      combLen_le_gadgetRadius (B := B) (α := α) (by omega)
    have hcast : (combLen B α (j - 1) : ℝ) ≤ (t : ℝ) := by
      have : combLen B α (j - 1) ≤ t := by omega
      exact_mod_cast this
    have hb : ((B : ℝ) ^ α) ^ (j - 1) ≤ 2 * (t : ℝ) := by
      have h1 := combLen_ge hc (j := j - 1) (by omega)
      linarith
    have hkey := pow_le_rpow_inv hc hb
    have hsplit : (B : ℝ) ^ (j + 1) = (B : ℝ) ^ 2 * (B : ℝ) ^ (j - 1) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hsplit]
    exact mul_le_mul_of_nonneg_left hkey (by positivity)

theorem card_bound_real (hc : CombCond B α) {d_f : ℝ} (hdf : d_f = 1 + 1 / α) {t : ℕ}
    (ht : 1 ≤ t) :
    (((wordsLe B (gadgetLevel (combLen B α) t + 1)).card * (t + 1) : ℕ) : ℝ)
      ≤ 4 * (B : ℝ) ^ 2 * (2 : ℝ) ^ (1 / α) * (t : ℝ) ^ d_f := by
  classical
  set K := gadgetLevel (combLen B α) t + 1 with hK
  have hB2 := cast_B_ge hc
  have hBnat : 2 ≤ B := hc.1
  have hcard : (wordsLe B K).card ≤ 2 * B ^ K :=
    le_trans (card_wordsLe B K) (sum_pow_range_le hBnat)
  have ht1 : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  have hcardR : ((wordsLe B K).card : ℝ) ≤ 2 * (B : ℝ) ^ K := by
    have : ((wordsLe B K).card : ℝ) ≤ ((2 * B ^ K : ℕ) : ℝ) := by exact_mod_cast hcard
    push_cast at this
    linarith
  have hlevel := base_level_le hc ht
  have hαinv : (0 : ℝ) < 1 / α := by have := alpha_pos hc; positivity
  have hsplit : (2 * (t : ℝ)) ^ (1 / α) = (2 : ℝ) ^ (1 / α) * (t : ℝ) ^ (1 / α) :=
    Real.mul_rpow (by norm_num) (by positivity)
  have hpow : (t : ℝ) ^ (1 / α) * (t : ℝ) = (t : ℝ) ^ d_f := by
    have htpos : (0 : ℝ) < (t : ℝ) := by linarith
    rw [hdf, show (1 : ℝ) + 1 / α = 1 / α + 1 by ring, Real.rpow_add htpos,
      Real.rpow_one]
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ (1 / α) := Real.rpow_pos_of_pos (by norm_num) _
  have htp : (0 : ℝ) < (t : ℝ) ^ (1 / α) := Real.rpow_pos_of_pos (by linarith) _
  have hBK : (0 : ℝ) < (B : ℝ) ^ K := by positivity
  have hstep : ((wordsLe B K).card : ℝ) * ((t : ℝ) + 1)
      ≤ 2 * ((B : ℝ) ^ 2 * ((2 : ℝ) ^ (1 / α) * (t : ℝ) ^ (1 / α))) * (2 * (t : ℝ)) := by
    have h1 : ((wordsLe B K).card : ℝ)
        ≤ 2 * ((B : ℝ) ^ 2 * ((2 : ℝ) ^ (1 / α) * (t : ℝ) ^ (1 / α))) := by
      rw [← hsplit]
      linarith [hcardR, hlevel]
    have h2 : (t : ℝ) + 1 ≤ 2 * (t : ℝ) := by linarith
    have h3 : (0 : ℝ) ≤ ((wordsLe B K).card : ℝ) := Nat.cast_nonneg _
    nlinarith [h1, h2, h3]
  push_cast
  calc ((wordsLe B K).card : ℝ) * ((t : ℝ) + 1)
      ≤ 2 * ((B : ℝ) ^ 2 * ((2 : ℝ) ^ (1 / α) * (t : ℝ) ^ (1 / α))) * (2 * (t : ℝ)) := hstep
    _ = 4 * (B : ℝ) ^ 2 * (2 : ℝ) ^ (1 / α) * ((t : ℝ) ^ (1 / α) * (t : ℝ)) := by ring
    _ = 4 * (B : ℝ) ^ 2 * (2 : ℝ) ^ (1 / α) * (t : ℝ) ^ d_f := by rw [hpow]

end RWRS.Support
