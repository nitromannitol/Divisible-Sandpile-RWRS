/-
The graph of `sec:recurrent-nonstab`: a ray from the root carrying a copy of the
gadget `H(m_k)` at the ray vertex `r_{s_k}`.

Two things are needed about it.  Downward, the depth of a site of a gadget,
measured from the root of the gadget, is realized by a path, so the whole of
`H(m_k)` sits inside the ball of radius `s_k + R_{m_k}` about the root of the
graph.  Upward, the depth of a site of the graph, measured as `i` on the ray
vertex `r_i` and as `s_k + ` the depth in the gadget on a gadget site, moves by
at most one along an edge, so it is a lower bound for the distance to the root
and the ball of radius `r` meets no gadget whose attachment point is beyond `r`.
-/
import RWRS.Support.GadgetBall
import Mathlib.Data.Set.Card.Arithmetic

namespace RWRS.Support

open scoped ENNReal

variable {B : ℕ} {L : ℕ → ℕ}

/-! ### The step towards the root -/

theorem pipeDepth_le_gadgetRadius {m : ℕ} {v : List (Fin B) × ℕ}
    (hv : v ∈ gadgetSites B L m) : pipeDepth L v ≤ gadgetRadius L m := by
  obtain ⟨hval, hlen⟩ := hv
  rcases hval with h0 | ⟨hne, h1, h2⟩
  · rw [pipeDepth, if_pos h0]
    exact gadgetRadius_mono L hlen
  · have hpos : 1 ≤ v.1.length := List.length_pos_iff.2 hne
    obtain ⟨j, hj⟩ : ∃ j, v.1.length = j + 1 := ⟨v.1.length - 1, by omega⟩
    have hne0 : v.2 ≠ 0 := by omega
    have hstep : gadgetRadius L (j + 1) = gadgetRadius L j + L (j + 1) :=
      gadgetRadius_succ L j
    have hmono : gadgetRadius L (j + 1) ≤ gadgetRadius L m := by
      rw [← hj]; exact gadgetRadius_mono L hlen
    rw [pipeDepth, if_neg hne0, hj]
    simp only [Nat.add_sub_cancel]
    rw [hj] at h2
    omega

theorem pipePred_valid {v : List (Fin B) × ℕ} (hv : PipeValid B L v) :
    PipeValid B L (pipePred B L v) := by
  obtain ⟨w, i⟩ := v
  match i with
  | 0 =>
      by_cases hw : w = []
      · subst hw; simp [pipePred, PipeValid]
      · simp only [pipePred, if_neg hw]
        by_cases hL2 : 2 ≤ L w.length
        · rw [if_pos hL2]
          exact Or.inr ⟨hw, by dsimp only; omega, by dsimp only; omega⟩
        · rw [if_neg hL2]
          exact Or.inl rfl
  | i + 1 =>
      rcases hv with h0 | ⟨hne, h1, h2⟩
      · exact absurd h0 (by simp)
      · dsimp only at hne h1 h2
        by_cases hi : i = 0
        · have hpe : pipePred B L ((w : List (Fin B)), i + 1) = (w.dropLast, 0) := by
            simp [pipePred, hi]
          rw [hpe]
          exact Or.inl rfl
        · have hpe : pipePred B L ((w : List (Fin B)), i + 1) = (w, i) := by
            simp [pipePred, hi]
          rw [hpe]
          exact Or.inr ⟨hne, by dsimp only; omega, by dsimp only; omega⟩

theorem pipePred_length_le (v : List (Fin B) × ℕ) :
    (pipePred B L v).1.length ≤ v.1.length := by
  obtain ⟨w, i⟩ := v
  match i with
  | 0 =>
      by_cases hw : w = []
      · subst hw; simp [pipePred]
      · simp only [pipePred, if_neg hw]
        by_cases hL2 : 2 ≤ L w.length
        · rw [if_pos hL2]
        · rw [if_neg hL2]; simp [List.length_dropLast]
  | i + 1 =>
      by_cases hi : i = 0
      · simp [pipePred, hi, List.length_dropLast]
      · simp [pipePred, hi]

theorem pipeDepth_pred_lt (hL : ∀ j, 1 ≤ j → 1 ≤ L j) {v : List (Fin B) × ℕ}
    (hv : PipeValid B L v) (hne : v ≠ pipeRoot B) :
    pipeDepth L (pipePred B L v) < pipeDepth L v := by
  obtain ⟨w, i⟩ := v
  match i with
  | 0 =>
      have hw : w ≠ [] := by
        intro h; exact hne (by simp [pipeRoot, h])
      have hpos : 1 ≤ w.length := List.length_pos_iff.2 hw
      obtain ⟨j, hj⟩ : ∃ j, w.length = j + 1 := ⟨w.length - 1, by omega⟩
      have hLpos : 1 ≤ L w.length := hL _ hpos
      have hv0 : pipeDepth L (w, 0) = gadgetRadius L j + L w.length := by
        rw [pipeDepth_zero, hj, gadgetRadius_succ, ← hj]
      simp only [pipePred, if_neg hw]
      by_cases hL2 : 2 ≤ L w.length
      · rw [if_pos hL2]
        have hs : L w.length - 1 = (L w.length - 2) + 1 := by omega
        have hp : pipeDepth L (w, L w.length - 1)
            = gadgetRadius L j + (L w.length - 1) := by
          rw [hs, pipeDepth_succ', hj]
          simp
        omega
      · rw [if_neg hL2]
        have hp : pipeDepth L (w.dropLast, 0) = gadgetRadius L j := by
          rw [pipeDepth_zero, List.length_dropLast, hj]
          simp
        omega
  | i + 1 =>
      have hv1 : pipeDepth L (w, i + 1) = gadgetRadius L (w.length - 1) + (i + 1) :=
        pipeDepth_succ' L w i
      by_cases hi : i = 0
      · have hpe : pipePred B L ((w : List (Fin B)), i + 1) = (w.dropLast, 0) := by
          simp [pipePred, hi]
        rw [hpe, hv1]
        have hp : pipeDepth L (w.dropLast, 0) = gadgetRadius L (w.length - 1) := by
          rw [pipeDepth_zero, List.length_dropLast]
        omega
      · have hpe : pipePred B L ((w : List (Fin B)), i + 1) = (w, i) := by
          simp [pipePred, hi]
        rw [hpe, hv1]
        obtain ⟨k, hk⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
        have hp : pipeDepth L (w, i) = gadgetRadius L (w.length - 1) + i := by
          rw [hk, pipeDepth_succ']
        omega

theorem pipePred_ne_self {v : List (Fin B) × ℕ}
    (hL : ∀ j, 1 ≤ j → 1 ≤ L j) (hv : PipeValid B L v) (hne : v ≠ pipeRoot B) :
    pipePred B L v ≠ v := by
  intro h
  have := pipeDepth_pred_lt hL hv hne
  rw [h] at this
  exact lt_irrefl _ this


/-! ### The depth is realized by a path -/

theorem le_gadgetRadius_self (hL : ∀ j, 1 ≤ j → 1 ≤ L j) (k : ℕ) :
    k ≤ gadgetRadius L k := by
  have h1 : ∑ j ∈ Finset.Icc 1 k, 1 ≤ ∑ j ∈ Finset.Icc 1 k, L j :=
    Finset.sum_le_sum fun j hj => hL j (Finset.mem_Icc.1 hj).1
  simpa [gadgetRadius, Nat.card_Icc] using h1

theorem eq_root_of_pipeDepth_zero (hL : ∀ j, 1 ≤ j → 1 ≤ L j)
    {v : List (Fin B) × ℕ} (hv : PipeValid B L v)
    (h : pipeDepth L v = 0) : v = pipeRoot B := by
  rcases hv with h0 | ⟨hne, h1, _⟩
  · rw [pipeDepth, if_pos h0] at h
    have := le_gadgetRadius_self hL v.1.length
    have hlen : v.1.length = 0 := by omega
    have : v.1 = [] := List.length_eq_zero_iff.1 hlen
    exact Prod.ext this h0
  · have hne0 : v.2 ≠ 0 := by omega
    rw [pipeDepth, if_neg hne0] at h
    omega

theorem gadgetGraph_adj_iff {m : ℕ} {u v : gadgetSites B L m} :
    (gadgetGraph B L m).Adj u v ↔ (pipeGraph B L false).Adj u v := Iff.rfl

theorem exists_walk_le_depth (hL : ∀ j, 1 ≤ j → 1 ≤ L j) {m : ℕ} :
    ∀ (n : ℕ) (v : gadgetSites B L m),
      pipeDepth L (v : List (Fin B) × ℕ) ≤ n →
      ∃ p : (gadgetGraph B L m).Walk (gadgetRoot B L m) v, p.length ≤ n := by
  intro n
  induction n with
  | zero =>
      intro v hv
      have hroot : (v : List (Fin B) × ℕ) = pipeRoot B :=
        eq_root_of_pipeDepth_zero hL v.2.1 (Nat.le_zero.1 hv)
      have : v = gadgetRoot B L m := Subtype.ext hroot
      subst this
      exact ⟨SimpleGraph.Walk.nil, by simp⟩
  | succ n ih =>
      intro v hv
      by_cases hz : pipeDepth L (v : List (Fin B) × ℕ) = 0
      · have hroot : (v : List (Fin B) × ℕ) = pipeRoot B :=
          eq_root_of_pipeDepth_zero hL v.2.1 hz
        have : v = gadgetRoot B L m := Subtype.ext hroot
        subst this
        exact ⟨SimpleGraph.Walk.nil, by simp⟩
      · have hne : (v : List (Fin B) × ℕ) ≠ pipeRoot B := by
          intro h
          rw [h, pipeDepth_root] at hz
          exact hz rfl
        have hdrop := pipeDepth_pred_lt hL v.2.1 hne
        have humem : pipePred B L (v : List (Fin B) × ℕ) ∈ gadgetSites B L m :=
          ⟨pipePred_valid v.2.1,
            le_trans (pipePred_length_le (v : List (Fin B) × ℕ)) v.2.2⟩
        obtain ⟨p, hp⟩ := ih ⟨pipePred B L (v : List (Fin B) × ℕ), humem⟩
          (Nat.lt_succ_iff.1 (lt_of_lt_of_le hdrop hv))
        have hadj : (gadgetGraph B L m).Adj
            ⟨pipePred B L (v : List (Fin B) × ℕ), humem⟩ v :=
          ⟨Or.inl (pipePred_valid v.2.1), Or.inl v.2.1,
            pipePred_ne_self hL v.2.1 hne, Or.inr rfl⟩
        refine ⟨p.concat hadj, ?_⟩
        rw [SimpleGraph.Walk.length_concat]
        omega

theorem edist_root_le_depth (hL : ∀ j, 1 ≤ j → 1 ≤ L j) {m : ℕ}
    (v : gadgetSites B L m) :
    (gadgetGraph B L m).edist (gadgetRoot B L m) v
      ≤ (pipeDepth L (v : List (Fin B) × ℕ) : ℕ∞) := by
  obtain ⟨p, hp⟩ := exists_walk_le_depth hL (pipeDepth L (v : List (Fin B) × ℕ)) v le_rfl
  exact le_trans (SimpleGraph.edist_le p) (by exact_mod_cast hp)


/-! ### Counting the sites at bounded depth -/

variable {α : ℝ}

open scoped Classical in
/-- The sites of a gadget at depth at most `t`, other than the root, inject into
the words of length at most one level past `t` times the positions `0,…,t`.
This is the bound behind `lem:rec-geometry`(c), for the sublevel set of the
depth rather than for the ball; the ball is contained in it. -/
theorem encard_depth_le_card (hc : CombCond B α) {m t : ℕ}
    (htm : t ≤ gadgetRadius (combLen B α) m) :
    ({v : gadgetSites B (combLen B α) m |
          pipeDepth (combLen B α) (v : List (Fin B) × ℕ) ≤ t}
        \ {gadgetRoot B (combLen B α) m}).encard
      ≤ (((wordsLe B (gadgetLevel (combLen B α) t + 1)).card * (t + 1) : ℕ) : ℕ∞) := by
  classical
  set K := gadgetLevel (combLen B α) t + 1 with hK
  set S := {v : gadgetSites B (combLen B α) m |
      pipeDepth (combLen B α) (v : List (Fin B) × ℕ) ≤ t}
      \ {gadgetRoot B (combLen B α) m} with hS
  set F : Finset (List (Fin B) × ℕ) := (wordsLe B K) ×ˢ Finset.range (t + 1) with hF
  have hinj : Set.InjOn
      (Subtype.val : gadgetSites B (combLen B α) m → List (Fin B) × ℕ) S :=
    Subtype.val_injective.injOn
  have hsub : (Subtype.val '' S) ⊆ (↑F : Set (List (Fin B) × ℕ)) := by
    rintro _ ⟨v, hv, rfl⟩
    have hd : pipeDepth (combLen B α) (v : List (Fin B) × ℕ) ≤ t := hv.1
    have h1 : (v : List (Fin B) × ℕ).1.length ≤ K := word_length_le_of_depth hc htm hd
    have h2 : (v : List (Fin B) × ℕ).2 ≤ t := le_trans (snd_le_pipeDepth _ _) hd
    exact Finset.mem_coe.2
      (Finset.mem_product.2 ⟨mem_wordsLe h1, Finset.mem_range.2 (by omega)⟩)
  calc S.encard = (Subtype.val '' S).encard := (hinj.encard_image).symm
    _ ≤ (↑F : Set (List (Fin B) × ℕ)).encard := Set.encard_le_encard hsub
    _ = (F.card : ℕ∞) := Set.encard_coe_eq_coe_finsetCard F
    _ = _ := by rw [hF, Finset.card_product, Finset.card_range]


/-! ### Counting the sites of a gadget from below -/

/-- The words of length exactly `k`. -/
noncomputable def wordsEq (B k : ℕ) : Finset (List (Fin B)) :=
  (Finset.univ : Finset (Fin k → Fin B)).image List.ofFn

theorem card_wordsEq (B k : ℕ) : (wordsEq B k).card = B ^ k := by
  rw [wordsEq, Finset.card_image_of_injective _ List.ofFn_injective, Finset.card_univ]
  simp

theorem length_of_mem_wordsEq {B k : ℕ} {w : List (Fin B)} (h : w ∈ wordsEq B k) :
    w.length = k := by
  obtain ⟨f, -, hf⟩ := Finset.mem_image.1 h
  rw [← hf]
  simp

open scoped Classical in
/-- The branching vertex of each word of length `1 ≤ j ≤ m` together with the
`L_j - 1` interior sites of the pipe above it. -/
noncomputable def gadgetFinset (B : ℕ) (L : ℕ → ℕ) (m : ℕ) : Finset (List (Fin B) × ℕ) :=
  (Finset.range m).biUnion fun j => (wordsEq B (j + 1)) ×ˢ Finset.range (L (j + 1))

open scoped Classical in
theorem gadgetFinset_subset (B : ℕ) (L : ℕ → ℕ) (m : ℕ) :
    (gadgetFinset B L m : Set (List (Fin B) × ℕ)) ⊆ gadgetSites B L m := by
  intro v hv
  simp only [gadgetFinset, Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe,
    Finset.mem_range] at hv
  obtain ⟨j, hj, hmem⟩ := hv
  rw [Finset.mem_product] at hmem
  obtain ⟨hw, hi⟩ := hmem
  have hlen : v.1.length = j + 1 := length_of_mem_wordsEq hw
  have hi' : v.2 < L (j + 1) := Finset.mem_range.1 hi
  refine ⟨?_, by omega⟩
  rcases Nat.eq_zero_or_pos v.2 with h0 | h0
  · exact Or.inl h0
  · refine Or.inr ⟨?_, h0, by rw [hlen]; omega⟩
    intro h
    rw [h] at hlen
    simp at hlen

open scoped Classical in
theorem card_gadgetFinset (B : ℕ) (L : ℕ → ℕ) (m : ℕ) :
    (gadgetFinset B L m).card = ∑ j ∈ Finset.range m, B ^ (j + 1) * L (j + 1) := by
  classical
  rw [gadgetFinset, Finset.card_biUnion]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.card_product, Finset.card_range, card_wordsEq]
  · intro i _ j _ hij
    refine Finset.disjoint_left.2 fun v hv hv' => ?_
    rw [Finset.mem_product] at hv hv'
    have h1 : v.1.length = i + 1 := length_of_mem_wordsEq hv.1
    have h2 : v.1.length = j + 1 := length_of_mem_wordsEq hv'.1
    exact hij (by omega)

theorem gadgetSize_eq_sum_range (B : ℕ) (L : ℕ → ℕ) (m : ℕ) :
    gadgetSize B L m = ∑ j ∈ Finset.range m, B ^ (j + 1) * L (j + 1) := by
  induction m with
  | zero => simp [gadgetSize]
  | succ m ih =>
      rw [Finset.sum_range_succ, ← ih, gadgetSize, gadgetSize,
        Finset.sum_Icc_succ_top (by omega)]

open scoped Classical in
/-- The gadget `H(m)` has at least `N_m` sites. -/
theorem gadgetSize_le_encard (B : ℕ) (L : ℕ → ℕ) (m : ℕ) :
    ((gadgetSize B L m : ℕ) : ℕ∞) ≤ (gadgetSites B L m).encard := by
  classical
  calc ((gadgetSize B L m : ℕ) : ℕ∞)
      = ((gadgetFinset B L m).card : ℕ∞) := by
        rw [card_gadgetFinset, gadgetSize_eq_sum_range]
    _ = (gadgetFinset B L m : Set (List (Fin B) × ℕ)).encard :=
        (Set.encard_coe_eq_coe_finsetCard _).symm
    _ ≤ (gadgetSites B L m).encard := Set.encard_le_encard (gadgetFinset_subset B L m)


open scoped Classical in
theorem mem_gadgetFinset (hL : ∀ j, 1 ≤ j → 1 ≤ L j) {m : ℕ} {v : List (Fin B) × ℕ}
    (hv : v ∈ gadgetSites B L m) (hne : v ≠ pipeRoot B) : v ∈ gadgetFinset B L m := by
  classical
  obtain ⟨hval, hlen⟩ := hv
  have hw : v.1 ≠ [] := by
    intro h
    rcases hval with h0 | ⟨hne', -, -⟩
    · exact hne (Prod.ext h h0)
    · exact hne' h
  have hpos : 1 ≤ v.1.length := List.length_pos_iff.2 hw
  obtain ⟨j, hj⟩ : ∃ j, v.1.length = j + 1 := ⟨v.1.length - 1, by omega⟩
  have hLpos : 1 ≤ L (j + 1) := hL _ (by omega)
  have hi : v.2 < L (j + 1) := by
    rcases hval with h0 | ⟨-, h1, h2⟩
    · omega
    · rw [hj] at h2; omega
  refine Finset.mem_biUnion.2 ⟨j, Finset.mem_range.2 (by omega), ?_⟩
  refine Finset.mem_product.2 ⟨?_, Finset.mem_range.2 hi⟩
  refine Finset.mem_image.2 ⟨fun i => v.1[(i : ℕ)]'(by omega), Finset.mem_univ _, ?_⟩
  apply List.ext_getElem
  · simp [hj]
  · intro n h1 h2
    rw [List.getElem_ofFn]

open scoped Classical in
/-- Every site of a gadget other than its root lies at depth at most `R_m`, and
there are at most `N_m` of them. -/
theorem encard_depthSet_le (hL : ∀ j, 1 ≤ j → 1 ≤ L j) {m t : ℕ} :
    ({v : ↥(gadgetSites B L m) | pipeDepth L (v : List (Fin B) × ℕ) ≤ t}
        \ {gadgetRoot B L m}).encard ≤ ((gadgetSize B L m : ℕ) : ℕ∞) := by
  classical
  set S := {v : ↥(gadgetSites B L m) | pipeDepth L (v : List (Fin B) × ℕ) ≤ t}
      \ {gadgetRoot B L m} with hS
  have hinj : Set.InjOn (Subtype.val : ↥(gadgetSites B L m) → List (Fin B) × ℕ) S :=
    Subtype.val_injective.injOn
  have hsub : (Subtype.val '' S) ⊆ (↑(gadgetFinset B L m) : Set (List (Fin B) × ℕ)) := by
    rintro _ ⟨v, hv, rfl⟩
    refine Finset.mem_coe.2 (mem_gadgetFinset hL v.2 ?_)
    intro h
    exact hv.2 (Subtype.ext h)
  calc S.encard = (Subtype.val '' S).encard := (hinj.encard_image).symm
    _ ≤ (↑(gadgetFinset B L m) : Set (List (Fin B) × ℕ)).encard :=
        Set.encard_le_encard hsub
    _ = ((gadgetFinset B L m).card : ℕ∞) := Set.encard_coe_eq_coe_finsetCard _
    _ = ((gadgetSize B L m : ℕ) : ℕ∞) := by
        rw [card_gadgetFinset, gadgetSize_eq_sum_range]

/-! ### The depth of a site of the global graph -/

variable {V : Type}

/-- The depth of a site of the graph of `sec:recurrent-nonstab`: the index `i`
on the ray vertex `r_i`, and `s_k` plus the depth in the gadget on a site of the
copy of `H(m_k)`.  The two agree at the attachment point, so this relation is a
function; that is `rayDepth_unique`. -/
def RayDepth (B : ℕ) (L : ℕ → ℕ) (m s : ℕ → ℕ) (ray : ℕ → V)
    (φ : ∀ k, gadgetSites B L (m k) → V) (x : V) (n : ℕ) : Prop :=
  (∃ i : ℕ, x = ray i ∧ n = i) ∨
    (∃ (k : ℕ) (v : gadgetSites B L (m k)),
      x = φ k v ∧ n = s k + pipeDepth L (v : List (Fin B) × ℕ))

variable {G : SimpleGraph V} {o : V} {m s : ℕ → ℕ} {ray : ℕ → V}
  {φ : ∀ k, gadgetSites B L (m k) → V}

theorem rayDepth_exists (hRG : RayGadget G o B L m s ray φ) (x : V) :
    ∃ n : ℕ, RayDepth B L m s ray φ x n := by
  rcases hRG.cover x with ⟨i, hi⟩ | ⟨k, v, hv⟩
  · exact ⟨i, Or.inl ⟨i, hi.symm, rfl⟩⟩
  · exact ⟨s k + pipeDepth L (v : List (Fin B) × ℕ), Or.inr ⟨k, v, hv, rfl⟩⟩

theorem rayDepth_root (hRG : RayGadget G o B L m s ray φ) :
    RayDepth B L m s ray φ o 0 :=
  Or.inl ⟨0, hRG.rayRoot.symm, rfl⟩

theorem rayDepth_ray (_hRG : RayGadget G o B L m s ray φ) (i : ℕ) :
    RayDepth B L m s ray φ (ray i) i := Or.inl ⟨i, rfl, rfl⟩

theorem rayDepth_gadget (k : ℕ) (v : gadgetSites B L (m k)) :
    RayDepth B L m s ray φ (φ k v) (s k + pipeDepth L (v : List (Fin B) × ℕ)) :=
  Or.inr ⟨k, v, rfl, rfl⟩

theorem rayDepth_unique (hRG : RayGadget G o B L m s ray φ) {x : V} {n n' : ℕ}
    (h : RayDepth B L m s ray φ x n) (h' : RayDepth B L m s ray φ x n') : n = n' := by
  have hrt : ∀ j : ℕ,
      ((gadgetRoot B L (m j) : gadgetSites B L (m j)) : List (Fin B) × ℕ) = pipeRoot B :=
    fun _ => rfl
  have hmix : ∀ (i k : ℕ) (v : gadgetSites B L (m k)),
      x = ray i → x = φ k v → i = s k + pipeDepth L (v : List (Fin B) × ℕ) := by
    intro i k v hi hv
    have hmem : φ k v ∈ Set.range ray := ⟨i, by rw [← hv, hi]⟩
    have hroot := hRG.meetsRay k v hmem
    subst hroot
    have hattach : ray (s k) = ray i := by rw [← hRG.attach k, ← hv, hi]
    have hsk : s k = i := hRG.rayInj hattach
    rw [hrt k, pipeDepth_root]
    omega
  rcases h with ⟨i, hi, hni⟩ | ⟨k, v, hv, hnk⟩
  · rcases h' with ⟨i', hi', hni'⟩ | ⟨k', v', hv', hnk'⟩
    · have hray : ray i = ray i' := by rw [← hi, hi']
      rw [hni, hni', hRG.rayInj hray]
    · rw [hni, hnk']
      exact hmix i k' v' hi hv'
  · rcases h' with ⟨i', hi', hni'⟩ | ⟨k', v', hv', hnk'⟩
    · rw [hnk, hni']
      exact (hmix i' k v hi' hv).symm
    · by_cases hkk : k = k'
      · subst hkk
        have hvv : v = v' := hRG.embInj k (by rw [← hv, hv'])
        rw [hnk, hnk', hvv]
      · obtain ⟨hr, hr'⟩ := hRG.disjoint k k' v v' hkk (by rw [← hv, hv'])
        subst hr
        subst hr'
        have hattach : ray (s k) = ray (s k') := by
          rw [← hRG.attach k, ← hRG.attach k', ← hv, hv']
        rw [hnk, hnk', hrt k, hrt k', pipeDepth_root, hRG.rayInj hattach]

theorem rayDepth_step (hRG : RayGadget G o B L m s ray φ) {x b : V} {n : ℕ}
    (hadj : G.Adj x b) (h : RayDepth B L m s ray φ x n) :
    ∃ n' : ℕ, RayDepth B L m s ray φ b n' ∧ n ≤ n' + 1 := by
  rcases (hRG.adj x b).1 hadj with ⟨i, hx, hb⟩ | ⟨i, hb, hx⟩ | ⟨k, v, w, hvw, hx, hb⟩
  · refine ⟨i + 1, hb ▸ rayDepth_ray hRG (i + 1), ?_⟩
    have : n = i := rayDepth_unique hRG h (hx ▸ rayDepth_ray hRG i)
    omega
  · refine ⟨i, hb ▸ rayDepth_ray hRG i, ?_⟩
    have : n = i + 1 := rayDepth_unique hRG h (hx ▸ rayDepth_ray hRG (i + 1))
    omega
  · refine ⟨s k + pipeDepth L (w : List (Fin B) × ℕ),
      hb ▸ rayDepth_gadget (φ := φ) k w, ?_⟩
    have hn : n = s k + pipeDepth L (v : List (Fin B) × ℕ) :=
      rayDepth_unique hRG h (hx ▸ rayDepth_gadget (φ := φ) k v)
    have hstep : pipeDepth L (v : List (Fin B) × ℕ)
        ≤ pipeDepth L (w : List (Fin B) × ℕ) + 1 :=
      pipeDepth_adj (e := false) hvw.symm
    omega

theorem rayDepth_le_add
    (hstep : ∀ (x b : V) (n : ℕ), G.Adj x b → RayDepth B L m s ray φ x n →
      ∃ n' : ℕ, RayDepth B L m s ray φ b n' ∧ n ≤ n' + 1)
    (huniq : ∀ (x : V) (n n' : ℕ), RayDepth B L m s ray φ x n →
      RayDepth B L m s ray φ x n' → n = n') :
    ∀ {x y : V} (p : G.Walk x y) {n n₀ : ℕ},
      RayDepth B L m s ray φ y n₀ → RayDepth B L m s ray φ x n → n ≤ n₀ + p.length := by
  intro x y p
  induction p with
  | nil =>
      intro n n₀ h0 hn
      rw [huniq _ _ _ hn h0]
      simp
  | cons h q ih =>
      intro n n₀ h0 hn
      obtain ⟨n', hn', hle⟩ := hstep _ _ _ h hn
      have := ih h0 hn'
      rw [SimpleGraph.Walk.length_cons]
      omega

theorem rayDepth_le_walk_length (hRG : RayGadget G o B L m s ray φ) {x : V}
    (p : G.Walk x o) {n : ℕ} (h : RayDepth B L m s ray φ x n) : n ≤ p.length := by
  have := rayDepth_le_add
    (fun x b n hadj hn => rayDepth_step hRG hadj hn)
    (fun _ _ _ h h' => rayDepth_unique hRG h h') p (rayDepth_root hRG) h
  omega

theorem rayDepth_le_of_mem_ball (hRG : RayGadget G o B L m s ray φ) {x : V} {r n : ℕ}
    (hx : x ∈ closedBall G o r) (h : RayDepth B L m s ray φ x n) : n ≤ r := by
  have hedist : G.edist x o ≤ (r : ℕ∞) := hx
  have hne : G.edist x o ≠ ⊤ := by
    intro htop
    rw [htop] at hedist
    exact (by simp : ¬ ((⊤ : ℕ∞) ≤ (r : ℕ∞))) hedist
  obtain ⟨p, hp⟩ :=
    (SimpleGraph.reachable_of_edist_ne_top hne).exists_walk_length_eq_edist
  have hlen : (p.length : ℕ∞) ≤ (r : ℕ∞) := by rw [hp]; exact hedist
  have hlen' : p.length ≤ r := by exact_mod_cast hlen
  exact le_trans (rayDepth_le_walk_length hRG p h) hlen'


/-! ### The ball of the global graph -/

/-- The part of the copy of `H(m_k)` that the ball of radius `r` can reach,
other than its root, which is the ray vertex `r_{s_k}`. -/
def gadgetPart (B : ℕ) (L : ℕ → ℕ) (m s : ℕ → ℕ) (r k : ℕ) :
    Set ↥(gadgetSites B L (m k)) :=
  {v | pipeDepth L (v : List (Fin B) × ℕ) ≤ r - s k} \ {gadgetRoot B L (m k)}

open scoped Classical in
/-- The indices of the gadgets the ball of radius `r` can reach. -/
noncomputable def reachedGadgets (s : ℕ → ℕ) (r : ℕ) : Finset ℕ :=
  (Finset.range (r + 2)).filter fun k => s k ≤ r

open scoped Classical in
/-- The last gadget the ball of radius `r` can reach. -/
noncomputable def lastGadget (s : ℕ → ℕ) (r : ℕ) : ℕ := (reachedGadgets s r).sup id

theorem sep_le_index {L : ℕ → ℕ} {m s : ℕ → ℕ}
    (hsep : ∀ k : ℕ, 2 ≤ k → s (k - 1) + gadgetRadius L (m (k - 1)) < s k) (j : ℕ) :
    j ≤ s (j + 1) := by
  induction j with
  | zero => omega
  | succ j ih =>
      show j + 1 ≤ s (j + 2)
      have h := hsep (j + 2) (by omega)
      have hpred : j + 2 - 1 = j + 1 := rfl
      rw [hpred] at h
      omega

theorem index_le_of_le {L : ℕ → ℕ} {m s : ℕ → ℕ}
    (hsep : ∀ k : ℕ, 2 ≤ k → s (k - 1) + gadgetRadius L (m (k - 1)) < s k) {r k : ℕ}
    (h : s k ≤ r) : k ≤ r + 1 := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · omega
  · obtain ⟨j, hj⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    subst hj
    have := sep_le_index (L := L) (m := m) hsep j
    omega

open scoped Classical in
theorem closedBall_subset (hRG : RayGadget G o B L m s ray φ)
    (hsep : ∀ k : ℕ, 2 ≤ k → s (k - 1) + gadgetRadius L (m (k - 1)) < s k) (r : ℕ) :
    closedBall G o r ⊆
      (ray '' Set.Iic r) ∪
        ⋃ k ∈ reachedGadgets s r,
          (fun v : ↥(gadgetSites B L (m k)) => φ k v) '' gadgetPart B L m s r k := by
  intro x hx
  rcases hRG.cover x with ⟨i, hi⟩ | ⟨k, v, hv⟩
  · have hn := rayDepth_le_of_mem_ball hRG hx (hi ▸ rayDepth_ray hRG i)
    exact Or.inl ⟨i, hn, hi⟩
  · by_cases hroot : v = gadgetRoot B L (m k)
    · subst hroot
      have hx' : x = ray (s k) := by rw [hv, hRG.attach k]
      have hn := rayDepth_le_of_mem_ball hRG hx (hx' ▸ rayDepth_ray hRG (s k))
      exact Or.inl ⟨s k, hn, hx'.symm⟩
    · have hn := rayDepth_le_of_mem_ball hRG hx (hv ▸ rayDepth_gadget (φ := φ) k v)
      refine Or.inr (Set.mem_iUnion₂.2 ⟨k, ?_, ?_⟩)
      · refine Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_range.2 ?_, ?_⟩)
        · have := index_le_of_le (L := L) (m := m) (r := r) (k := k) hsep (by omega)
          omega
        · omega
      · exact ⟨v, ⟨by simp only [Set.mem_setOf_eq]; omega, hroot⟩, hv.symm⟩

open scoped Classical in
theorem encard_closedBall_le (hRG : RayGadget G o B L m s ray φ)
    (hsep : ∀ k : ℕ, 2 ≤ k → s (k - 1) + gadgetRadius L (m (k - 1)) < s k)
    (hL : ∀ j, 1 ≤ j → 1 ≤ L j) (r : ℕ) :
    (closedBall G o r).encard
      ≤ ((r + 1 : ℕ) : ℕ∞)
        + ((∑ k ∈ Finset.range (lastGadget s r), gadgetSize B L (m k) : ℕ) : ℕ∞)
        + (gadgetPart B L m s r (lastGadget s r)).encard := by
  classical
  set k₀ := lastGadget s r with hk₀
  have hray : (ray '' Set.Iic r).encard ≤ ((r + 1 : ℕ) : ℕ∞) := by
    refine le_trans (Set.encard_image_le _ _) ?_
    have : (Set.Iic r) = (↑(Finset.Iic r) : Set ℕ) := by simp
    rw [this, Set.encard_coe_eq_coe_finsetCard]
    simp
  have hsub := closedBall_subset hRG hsep r
  have hun : ((ray '' Set.Iic r) ∪
      ⋃ k ∈ reachedGadgets s r,
        (fun v : ↥(gadgetSites B L (m k)) => φ k v) '' gadgetPart B L m s r k).encard
      ≤ ((r + 1 : ℕ) : ℕ∞)
        + ∑ k ∈ reachedGadgets s r, (gadgetPart B L m s r k).encard := by
    refine le_trans (Set.encard_union_le _ _) ?_
    have hbi := Finset.set_encard_biUnion_le (reachedGadgets s r)
      (fun k => (fun v : ↥(gadgetSites B L (m k)) => φ k v) '' gadgetPart B L m s r k)
    have hterm : ∑ k ∈ reachedGadgets s r,
        ((fun v : ↥(gadgetSites B L (m k)) => φ k v) '' gadgetPart B L m s r k).encard
        ≤ ∑ k ∈ reachedGadgets s r, (gadgetPart B L m s r k).encard :=
      Finset.sum_le_sum fun k _ => Set.encard_image_le _ _
    exact add_le_add hray (le_trans hbi hterm)
  refine le_trans (Set.encard_le_encard hsub) (le_trans hun ?_)
  have hsubset : reachedGadgets s r ⊆ Finset.range (k₀ + 1) := by
    intro k hk
    exact Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.le_sup (f := id) hk))
  have hmono : ∑ k ∈ reachedGadgets s r, (gadgetPart B L m s r k).encard
      ≤ ∑ k ∈ Finset.range (k₀ + 1), (gadgetPart B L m s r k).encard :=
    Finset.sum_le_sum_of_subset hsubset
  have hsplit : ∑ k ∈ Finset.range (k₀ + 1), (gadgetPart B L m s r k).encard
      = (∑ k ∈ Finset.range k₀, (gadgetPart B L m s r k).encard)
        + (gadgetPart B L m s r k₀).encard := Finset.sum_range_succ _ _
  have hbound : ∑ k ∈ Finset.range k₀, (gadgetPart B L m s r k).encard
      ≤ ∑ k ∈ Finset.range k₀, ((gadgetSize B L (m k) : ℕ) : ℕ∞) :=
    Finset.sum_le_sum fun k _ => encard_depthSet_le hL
  calc ((r + 1 : ℕ) : ℕ∞) + ∑ k ∈ reachedGadgets s r, (gadgetPart B L m s r k).encard
      ≤ ((r + 1 : ℕ) : ℕ∞) + ∑ k ∈ Finset.range (k₀ + 1), (gadgetPart B L m s r k).encard :=
        by gcongr
    _ = ((r + 1 : ℕ) : ℕ∞) + ((∑ k ∈ Finset.range k₀, (gadgetPart B L m s r k).encard)
          + (gadgetPart B L m s r k₀).encard) := by rw [hsplit]
    _ ≤ ((r + 1 : ℕ) : ℕ∞) + ((∑ k ∈ Finset.range k₀, ((gadgetSize B L (m k) : ℕ) : ℕ∞))
          + (gadgetPart B L m s r k₀).encard) :=
        by gcongr
    _ = _ := by rw [add_assoc, Nat.cast_sum]


/-! ### The whole gadget sits inside the ball of radius `s_k + R_{m_k}` -/

/-- The walk along the ray from the root to `r_i`. -/
def rayWalk (hRG : RayGadget G o B L m s ray φ) : ∀ i : ℕ, G.Walk o (ray i)
  | 0 => hRG.rayRoot ▸ SimpleGraph.Walk.nil
  | i + 1 => (rayWalk hRG i).concat ((hRG.adj _ _).2 (Or.inl ⟨i, rfl, rfl⟩))

theorem rayWalk_length (hRG : RayGadget G o B L m s ray φ) (i : ℕ) :
    (rayWalk hRG i).length = i := by
  induction i with
  | zero =>
      have : (rayWalk hRG 0).length = (SimpleGraph.Walk.nil : G.Walk o o).length := by
        rw [rayWalk]
        cases hRG.rayRoot
        rfl
      simpa using this
  | succ i ih => rw [rayWalk, SimpleGraph.Walk.length_concat, ih]

/-- The copy of the gadget `H(m_k)` as a graph homomorphism into `G`. -/
def gadgetHom (hRG : RayGadget G o B L m s ray φ) (k : ℕ) :
    gadgetGraph B L (m k) →g G where
  toFun := φ k
  map_rel' := fun {v w} h => (hRG.adj _ _).2 (Or.inr (Or.inr ⟨k, v, w, h, rfl, rfl⟩))

theorem edist_le_of_mem_gadget (hRG : RayGadget G o B L m s ray φ)
    (hL : ∀ j, 1 ≤ j → 1 ≤ L j) (k : ℕ) (v : ↥(gadgetSites B L (m k))) :
    G.edist (φ k v) o ≤ ((s k + gadgetRadius L (m k) : ℕ) : ℕ∞) := by
  obtain ⟨p, hp⟩ := exists_walk_le_depth hL
    (pipeDepth L (v : List (Fin B) × ℕ)) v le_rfl
  have hattach : ray (s k) = (gadgetHom hRG k) (gadgetRoot B L (m k)) :=
    (hRG.attach k).symm
  have h3 : pipeDepth L (v : List (Fin B) × ℕ) ≤ gadgetRadius L (m k) :=
    pipeDepth_le_gadgetRadius v.2
  have hlen : ((((rayWalk hRG (s k)).copy rfl hattach).append
      (p.map (gadgetHom hRG k)))).length ≤ s k + gadgetRadius L (m k) := by
    rw [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_copy, rayWalk_length,
      SimpleGraph.Walk.length_map]
    omega
  calc G.edist (φ k v) o = G.edist o (φ k v) := SimpleGraph.edist_comm
    _ ≤ (((((rayWalk hRG (s k)).copy rfl hattach).append
            (p.map (gadgetHom hRG k)))).length : ℕ∞) := SimpleGraph.edist_le _
    _ ≤ ((s k + gadgetRadius L (m k) : ℕ) : ℕ∞) := by exact_mod_cast hlen

theorem gadgetSize_le_encard_closedBall (hRG : RayGadget G o B L m s ray φ)
    (hL : ∀ j, 1 ≤ j → 1 ≤ L j) (k : ℕ) :
    ((gadgetSize B L (m k) : ℕ) : ℕ∞)
      ≤ (closedBall G o (s k + gadgetRadius L (m k))).encard := by
  have himg : (φ k) '' (Set.univ : Set ↥(gadgetSites B L (m k)))
      ⊆ closedBall G o (s k + gadgetRadius L (m k)) := by
    rintro _ ⟨v, -, rfl⟩
    exact edist_le_of_mem_gadget hRG hL k v
  have hA : ((Subtype.val : ↥(gadgetSites B L (m k)) → List (Fin B) × ℕ) '' Set.univ)
      = gadgetSites B L (m k) := Subtype.coe_image_univ _
  have huniv : (Set.univ : Set ↥(gadgetSites B L (m k))).encard
      = (gadgetSites B L (m k)).encard := by
    conv_rhs => rw [← hA]
    exact (Subtype.val_injective.injOn.encard_image).symm
  calc ((gadgetSize B L (m k) : ℕ) : ℕ∞) ≤ (gadgetSites B L (m k)).encard :=
        gadgetSize_le_encard B L (m k)
    _ = (Set.univ : Set ↥(gadgetSites B L (m k))).encard := huniv.symm
    _ = ((φ k) '' (Set.univ : Set ↥(gadgetSites B L (m k)))).encard :=
        ((hRG.embInj k).injOn.encard_image).symm
    _ ≤ _ := Set.encard_le_encard himg


/-! ### The two halves of the volume bound in real form -/

open scoped Classical in
theorem gadgetPart_subset_depth {m s : ℕ → ℕ} {r k : ℕ} :
    gadgetPart B L m s r k
      ⊆ {v : ↥(gadgetSites B L (m k)) |
          pipeDepth L (v : List (Fin B) × ℕ)
            ≤ min (r - s k) (gadgetRadius L (m k))}
        \ {gadgetRoot B L (m k)} := by
  rintro v ⟨hd, hne⟩
  exact ⟨le_min hd (pipeDepth_le_gadgetRadius v.2), hne⟩

open scoped Classical in
theorem gadgetPart_eq_empty_of_min_zero (hL : ∀ j, 1 ≤ j → 1 ≤ L j)
    {m s : ℕ → ℕ} {r k : ℕ}
    (h0 : min (r - s k) (gadgetRadius L (m k)) = 0) :
    gadgetPart B L m s r k = ∅ := by
  ext v
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨hd, hne⟩
  have hle : pipeDepth L (v : List (Fin B) × ℕ)
      ≤ min (r - s k) (gadgetRadius L (m k)) :=
    le_min hd (pipeDepth_le_gadgetRadius v.2)
  have : pipeDepth L (v : List (Fin B) × ℕ) = 0 := by omega
  exact hne (Subtype.ext (eq_root_of_pipeDepth_zero hL v.2.1 this))

open scoped Classical in
/-- The part of the last gadget the ball of radius `r` reaches has at most
`C_ball r^{d_f}` sites other than its root. -/
theorem encard_gadgetPart_le (hc : CombCond B α) {d_f : ℝ} (hdf : d_f = 1 + 1 / α)
    {m s : ℕ → ℕ} {r k : ℕ} :
    (gadgetPart B (combLen B α) m s r k).encard
      ≤ ENNReal.ofReal (4 * (B : ℝ) ^ 2 * (2 : ℝ) ^ (1 / α) * (r : ℝ) ^ d_f) := by
  classical
  have hL : ∀ j : ℕ, 1 ≤ j → 1 ≤ combLen B α j := fun j _ => combLen_pos' hc j
  set t := min (r - s k) (gadgetRadius (combLen B α) (m k)) with ht
  by_cases h0 : t = 0
  · rw [gadgetPart_eq_empty_of_min_zero hL h0]
    simp
  · have ht1 : 1 ≤ t := by omega
    have htm : t ≤ gadgetRadius (combLen B α) (m k) := min_le_right _ _
    have htr : t ≤ r := le_trans (min_le_left _ _) (Nat.sub_le _ _)
    have h1 := encard_depth_le_card (B := B) (α := α) hc (m := m k) (t := t) htm
    have h2 := card_bound_real (B := B) (α := α) hc hdf ht1
    have hstep : ((((wordsLe B (gadgetLevel (combLen B α) t + 1)).card * (t + 1) : ℕ)) : ℝ)
        ≤ 4 * (B : ℝ) ^ 2 * (2 : ℝ) ^ (1 / α) * (r : ℝ) ^ d_f := by
      refine le_trans h2 ?_
      have hdfpos : 0 < d_f := df_pos hc hdf
      have htr' : (t : ℝ) ≤ (r : ℝ) := by exact_mod_cast htr
      have hmono : (t : ℝ) ^ d_f ≤ (r : ℝ) ^ d_f :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) htr' hdfpos.le
      have hpos : (0 : ℝ) ≤ 4 * (B : ℝ) ^ 2 * (2 : ℝ) ^ (1 / α) := by
        have := cast_B_pos hc
        positivity
      exact mul_le_mul_of_nonneg_left hmono hpos
    set N := ((wordsLe B (gadgetLevel (combLen B α) t + 1)).card * (t + 1) : ℕ) with hN
    calc ((gadgetPart B (combLen B α) m s r k).encard : ℝ≥0∞)
        ≤ (({v : ↥(gadgetSites B (combLen B α) (m k)) |
              pipeDepth (combLen B α) (v : List (Fin B) × ℕ) ≤ t}
            \ {gadgetRoot B (combLen B α) (m k)}).encard : ℝ≥0∞) :=
          ENat.toENNReal_mono (Set.encard_le_encard gadgetPart_subset_depth)
      _ ≤ ((N : ℕ∞) : ℝ≥0∞) := ENat.toENNReal_mono h1
      _ = ENNReal.ofReal (N : ℝ) := by simp
      _ ≤ ENNReal.ofReal (4 * (B : ℝ) ^ 2 * (2 : ℝ) ^ (1 / α) * (r : ℝ) ^ d_f) :=
          ENNReal.ofReal_le_ofReal hstep

open scoped Classical in
theorem sum_gadgetSize_le {m s : ℕ → ℕ} {d_f : ℝ} (hdfpos : 0 < d_f)
    (hvol : ∀ k : ℕ, 2 ≤ k →
      (∑ j ∈ Finset.range k, (gadgetSize B L (m j) : ℝ)) ≤ (s k : ℝ) ^ d_f)
    (r : ℕ) :
    (∑ k ∈ Finset.range (lastGadget s r), (gadgetSize B L (m k) : ℝ))
      ≤ (gadgetSize B L (m 0) : ℝ) + (r : ℝ) ^ d_f := by
  classical
  set k₀ := lastGadget s r with hk₀
  have hnn : (0 : ℝ) ≤ (r : ℝ) ^ d_f := Real.rpow_nonneg (Nat.cast_nonneg _) _
  rcases Nat.lt_or_ge k₀ 2 with hlt | hge
  · interval_cases k₀ <;> simp <;> linarith [hnn]
  · have hne : (reachedGadgets s r).Nonempty := by
      by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty] at hempty
      rw [hk₀, lastGadget, hempty] at hge
      simp at hge
    obtain ⟨b, hb, hbeq⟩ := Finset.exists_mem_eq_sup (reachedGadgets s r) hne id
    have hk₀mem : k₀ ∈ reachedGadgets s r := by
      rw [hk₀, lastGadget, hbeq]; exact hb
    have hsk : s k₀ ≤ r := (Finset.mem_filter.1 hk₀mem).2
    have hle : (s k₀ : ℝ) ≤ (r : ℝ) := by exact_mod_cast hsk
    have hmono : (s k₀ : ℝ) ^ d_f ≤ (r : ℝ) ^ d_f :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) hle hdfpos.le
    have := hvol k₀ hge
    have hgz : (0 : ℝ) ≤ (gadgetSize B L (m 0) : ℝ) := Nat.cast_nonneg _
    linarith


open scoped Classical in
/-- **The volume upper bound of `prop:rec-growth`.** -/
theorem encard_closedBall_le_real (hc : CombCond B α) {d_f : ℝ} (hdf : d_f = 1 + 1 / α)
    {ψ : ∀ k : ℕ, ↥(gadgetSites B (combLen B α) (m k)) → V}
    (hRG : RayGadget G o B (combLen B α) m s ray ψ)
    (hsep : ∀ k : ℕ, 2 ≤ k →
      s (k - 1) + gadgetRadius (combLen B α) (m (k - 1)) < s k)
    (hvol : ∀ k : ℕ, 2 ≤ k →
      (∑ j ∈ Finset.range k, (gadgetSize B (combLen B α) (m j) : ℝ)) ≤ (s k : ℝ) ^ d_f)
    {r : ℕ} (hr : 1 ≤ r) :
    (closedBall G o r).encard
      ≤ ENNReal.ofReal ((7 + (gadgetSize B (combLen B α) (m 0) : ℝ)
          + 4 * (B : ℝ) ^ 2 * (2 : ℝ) ^ (1 / α)) * (r : ℝ) ^ d_f) := by
  classical
  have hL : ∀ j : ℕ, 1 ≤ j → 1 ≤ combLen B α j := fun j _ => combLen_pos' hc j
  have hdfpos : 0 < d_f := df_pos hc hdf
  have hdf1 : (1 : ℝ) ≤ d_f := by
    have hα := hc.2.2.1
    have hα0 := alpha_pos hc
    rw [hdf]
    have : 0 < 1 / α := by positivity
    linarith
  set k₀ := lastGadget s r with hk₀
  set Cb : ℝ := 4 * (B : ℝ) ^ 2 * (2 : ℝ) ^ (1 / α) with hCb
  have hCbpos : (0 : ℝ) ≤ Cb := by
    have := cast_B_pos hc
    rw [hCb]; positivity
  have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hrdf : (r : ℝ) ≤ (r : ℝ) ^ d_f := by
    calc (r : ℝ) = (r : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (r : ℝ) ^ d_f := Real.rpow_le_rpow_of_exponent_le hr1 hdf1
  have hone : (1 : ℝ) ≤ (r : ℝ) ^ d_f := le_trans hr1 hrdf
  have hN0 : (0 : ℝ) ≤ (gadgetSize B (combLen B α) (m 0) : ℝ) := Nat.cast_nonneg _
  have hnat := encard_closedBall_le hRG hsep hL r
  have hsumcast : ((((∑ k ∈ Finset.range k₀,
        gadgetSize B (combLen B α) (m k) : ℕ) : ℕ∞)) : ℝ≥0∞)
      = ENNReal.ofReal (∑ k ∈ Finset.range k₀,
          (gadgetSize B (combLen B α) (m k) : ℝ)) := by
    rw [← Nat.cast_sum (R := ℝ), ENNReal.ofReal_natCast]
    simp only [ENat.toENNReal_coe]
  have hsumle := sum_gadgetSize_le (L := combLen B α) hdfpos hvol r
  have hpart := encard_gadgetPart_le (B := B) (α := α) hc hdf
    (m := m) (s := s) (r := r) (k := k₀)
  have hfinal : ((r : ℝ) + 1)
      + (∑ k ∈ Finset.range k₀, (gadgetSize B (combLen B α) (m k) : ℝ))
      + Cb * (r : ℝ) ^ d_f
      ≤ (7 + (gadgetSize B (combLen B α) (m 0) : ℝ) + Cb) * (r : ℝ) ^ d_f := by
    have h1 : (∑ k ∈ Finset.range k₀, (gadgetSize B (combLen B α) (m k) : ℝ))
        ≤ (gadgetSize B (combLen B α) (m 0) : ℝ) + (r : ℝ) ^ d_f := hsumle
    have h2 : (gadgetSize B (combLen B α) (m 0) : ℝ)
        ≤ (gadgetSize B (combLen B α) (m 0) : ℝ) * (r : ℝ) ^ d_f := by
      nlinarith
    nlinarith
  calc ((closedBall G o r).encard : ℝ≥0∞)
      ≤ (((((r + 1 : ℕ) : ℕ∞)
            + ((∑ k ∈ Finset.range k₀, gadgetSize B (combLen B α) (m k) : ℕ) : ℕ∞)
            + (gadgetPart B (combLen B α) m s r k₀).encard : ℕ∞)) : ℝ≥0∞) :=
        ENat.toENNReal_mono hnat
    _ = ((((r + 1 : ℕ) : ℕ∞) : ℝ≥0∞))
          + (((((∑ k ∈ Finset.range k₀,
              gadgetSize B (combLen B α) (m k) : ℕ) : ℕ∞))) : ℝ≥0∞)
          + (((gadgetPart B (combLen B α) m s r k₀).encard : ℕ∞) : ℝ≥0∞) := by
        push_cast
        ring
    _ ≤ ENNReal.ofReal ((r : ℝ) + 1)
          + ENNReal.ofReal (∑ k ∈ Finset.range k₀,
              (gadgetSize B (combLen B α) (m k) : ℝ))
          + ENNReal.ofReal (Cb * (r : ℝ) ^ d_f) := by
        refine add_le_add (add_le_add (le_of_eq ?_) (le_of_eq hsumcast)) hpart
        push_cast
        rw [ENNReal.ofReal_add (by positivity) (by norm_num)]
        simp
    _ = ENNReal.ofReal (((r : ℝ) + 1)
          + (∑ k ∈ Finset.range k₀, (gadgetSize B (combLen B α) (m k) : ℝ))
          + Cb * (r : ℝ) ^ d_f) := by
        rw [← ENNReal.ofReal_add (by positivity)
              (Finset.sum_nonneg fun k _ => Nat.cast_nonneg _),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal hfinal


/-! ### The exponent of `eq:rec-rho` is below one -/

theorem log_base_pos (hc : CombCond B α) : 0 < Real.log B := by
  have hB2 : (2 : ℝ) ≤ (B : ℝ) := cast_B_ge hc
  exact Real.log_pos (by linarith)

theorem delta_pos (hc : CombCond B α) :
    0 < Real.log (combLambda B α) / (α * Real.log B) := by
  have hlog := log_base_pos hc
  have hα := alpha_pos hc
  have hlam : 1 < combLambda B α := hc.2.2.2.2.2.2
  exact div_pos (Real.log_pos hlam) (by positivity)

theorem delta_lt_one (hc : CombCond B α) :
    Real.log (combLambda B α) / (α * Real.log B) < 1 := by
  have hlog := log_base_pos hc
  have hα := alpha_pos hc
  have hα1 : α < 1 := hc.2.2.1
  have hBpos : (0 : ℝ) < (B : ℝ) := cast_B_pos hc
  have hlam : Real.log (combLambda B α) = (2 * α - 1) * Real.log B - Real.log 4 := by
    rw [combLambda, Real.log_div (by positivity) (by norm_num), Real.log_rpow hBpos]
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  rw [hlam, div_lt_one (by positivity)]
  nlinarith

theorem rho_lt_one (hc : CombCond B α) {d_f ρ : ℝ} (hdf : d_f = 1 + 1 / α)
    (hρ2 : ρ < Real.log (combLambda B α) / (α * Real.log B) / (d_f + 1)) : ρ < 1 := by
  have hα := alpha_pos hc
  have hδ := delta_pos hc
  have hδ1 := delta_lt_one hc
  have hdf1 : (1 : ℝ) ≤ d_f + 1 := by
    rw [hdf]
    have : 0 < 1 / α := by positivity
    linarith
  have := div_le_self hδ.le hdf1
  linarith

