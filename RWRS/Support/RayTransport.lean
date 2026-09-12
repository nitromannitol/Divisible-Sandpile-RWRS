/-
The comb of the `k`-th gadget, read inside the ray graph.

`cor:rec-loc` is a statement about `combVoltage`, the voltage of the comb inside
the tree of pipes with one extra boundary edge at its root.  The theorem needs
the voltage of `C_k` inside the global graph, restricted to the comb.  The two
agree, and the reason is a correspondence of neighbours: the comb sits inside
the `k`-th gadget, whose sites carry the same edges in the tree of pipes and in
the ray graph, and the only site where the two differ is the root of the comb,
which is the attachment vertex `r_{s_k}`.  There the ray graph has two extra
neighbours, `r_{s_k-1}` and `r_{s_k+1}`, against the one extra boundary vertex
of the comb; the voltage vanishes at `r_{s_k+1}`, which is outside `C_k`, and
drops by exactly one across the backbone edge to `r_{s_k-1}`, so the local
Laplacian of the transported function at the root is `-1`, which is the unit
source of the comb's own problem.  Uniqueness for the boundary value problem
finishes it.
-/
import RWRS.Support.RayFlux
import RWRS.Support.CombVolt

namespace RWRS.Support

open scoped Classical

variable {B : ℕ} {L : ℕ → ℕ}

/-! ### The extra boundary vertex -/

/-- The extra boundary vertex `([],1)` of the comb. -/
def pipeExtra (B : ℕ) : List (Fin B) × ℕ := ([], 1)

theorem not_pipeValid_pipeExtra : ¬ RWRS.PipeValid B L (pipeExtra B) := by
  rintro (h | ⟨h, -⟩)
  · exact absurd h (by simp [pipeExtra])
  · exact h rfl

theorem pipeValidPlus_false_iff {v : List (Fin B) × ℕ} :
    RWRS.PipeValidPlus B L false v ↔ RWRS.PipeValid B L v := by
  constructor
  · rintro (h | ⟨h, -⟩)
    · exact h
    · exact absurd h (by simp)
  · exact Or.inl

theorem ne_pipeExtra_of_valid {v : List (Fin B) × ℕ} (h : RWRS.PipeValid B L v) :
    v ≠ pipeExtra B := fun hc => not_pipeValid_pipeExtra (L := L) (hc ▸ h)

theorem pipe_adj_true_of_false {u v : List (Fin B) × ℕ}
    (h : (RWRS.pipeGraph B L false).Adj u v) : (RWRS.pipeGraph B L true).Adj u v :=
  ⟨Or.inl (pipeValidPlus_false_iff.mp h.1), Or.inl (pipeValidPlus_false_iff.mp h.2.1),
    h.2.2.1, h.2.2.2⟩

theorem pipe_adj_false_of_true {u v : List (Fin B) × ℕ}
    (hu : RWRS.PipeValid B L u) (hv : RWRS.PipeValid B L v)
    (h : (RWRS.pipeGraph B L true).Adj u v) : (RWRS.pipeGraph B L false).Adj u v :=
  ⟨Or.inl hu, Or.inl hv, h.2.2.1, h.2.2.2⟩

/-- The root of the tree of pipes is a site. -/
theorem pipeValid_pipeRoot : RWRS.PipeValid B L (RWRS.pipeRoot B) := Or.inl rfl

/-- **The extra boundary vertex is joined to the root and to nothing else.** -/
theorem pipeValid_of_adj_true {u v : List (Fin B) × ℕ}
    (hu : RWRS.PipeValid B L u) (hune : u ≠ RWRS.pipeRoot B)
    (h : (RWRS.pipeGraph B L true).Adj u v) : RWRS.PipeValid B L v := by
  rcases h.2.1 with hv | ⟨-, hv⟩
  · exact hv
  · exfalso
    subst hv
    obtain ⟨w, i⟩ := u
    rcases h.2.2.2 with hpred | hpred
    · match i with
      | 0 =>
          simp only [RWRS.pipePred] at hpred
          by_cases hw : w = []
          · subst hw; exact hune rfl
          · rw [if_neg hw] at hpred
            by_cases hL : 2 ≤ L w.length
            · rw [if_pos hL] at hpred
              exact hw (congrArg Prod.fst hpred).symm
            · rw [if_neg hL] at hpred
              exact absurd (congrArg Prod.snd hpred) (by simp)
      | i + 1 =>
          simp only [RWRS.pipePred] at hpred
          by_cases hi : i = 0
          · rw [if_pos hi] at hpred
            exact absurd (congrArg Prod.snd hpred) (by simp)
          · rw [if_neg hi] at hpred
            have h1 : w = [] := (congrArg Prod.fst hpred).symm
            have h2 : i = 1 := (congrArg Prod.snd hpred).symm
            subst h1
            rcases hu with h0 | ⟨hne, -⟩
            · simp at h0
            · exact hne rfl
    · simp only [RWRS.pipePred] at hpred
      exact hune hpred

/-- Away from the root, the extra boundary edge changes no neighbour. -/
theorem neighborFinset_pipe_true_eq {u : List (Fin B) × ℕ} (hu : RWRS.PipeValid B L u) (hune : u ≠ RWRS.pipeRoot B) :
    (RWRS.pipeGraph B L true).neighborFinset u
      = (RWRS.pipeGraph B L false).neighborFinset u := by
  ext y
  simp only [SimpleGraph.mem_neighborFinset]
  exact ⟨fun h => pipe_adj_false_of_true hu (pipeValid_of_adj_true hu hune h) h,
    pipe_adj_true_of_false⟩

theorem adj_true_root_extra : (RWRS.pipeGraph B L true).Adj (RWRS.pipeRoot B) (pipeExtra B) :=
  ⟨Or.inl pipeValid_pipeRoot, Or.inr ⟨rfl, rfl⟩, by simp [RWRS.pipeRoot, pipeExtra],
    Or.inr (by simp [pipeExtra, RWRS.pipePred, RWRS.pipeRoot])⟩

/-- At the root the extra boundary edge adds exactly the vertex `([],1)`. -/
theorem neighborFinset_pipe_true_root :
    (RWRS.pipeGraph B L true).neighborFinset (RWRS.pipeRoot B)
      = insert (pipeExtra B) ((RWRS.pipeGraph B L false).neighborFinset (RWRS.pipeRoot B)) := by
  ext y
  simp only [Finset.mem_insert, SimpleGraph.mem_neighborFinset]
  constructor
  · intro h
    by_cases hy : y = pipeExtra B
    · exact Or.inl hy
    · refine Or.inr (pipe_adj_false_of_true pipeValid_pipeRoot ?_ h)
      rcases h.2.1 with hv | ⟨-, hv⟩
      · exact hv
      · exact absurd hv hy
  · rintro (rfl | h)
    · exact adj_true_root_extra
    · exact pipe_adj_true_of_false h

theorem notMem_pipeExtra_false :
    pipeExtra B ∉ (RWRS.pipeGraph B L false).neighborFinset (RWRS.pipeRoot B) := by
  simp only [SimpleGraph.mem_neighborFinset]
  intro h
  exact not_pipeValid_pipeExtra (L := L) (pipeValidPlus_false_iff.mp h.2.1)

/-! ### The comb inside the gadget -/

/-- **Adjacency never leaves the gadget of the comb.**  A neighbour of a comb
site is a site of the same gadget: stepping towards the root shortens the word,
and stepping away from it can lengthen the word only at a branching vertex of
the trunk, which the comb keeps only below its depth. -/
theorem comb_nbr_mem_gadgetSites (hL2 : ∀ j, 1 ≤ j → 2 ≤ L j) {n : ℕ} {w : List (Fin B)}
    {u y : List (Fin B) × ℕ} (hu : u ∈ RWRS.combSet B L n w)
    (h : (RWRS.pipeGraph B L false).Adj u y) : y ∈ RWRS.gadgetSites B L n := by
  have hyv : RWRS.PipeValid B L y := pipeValidPlus_false_iff.mp h.2.1
  refine ⟨hyv, ?_⟩
  rcases h.2.2.2 with hy | hu'
  · calc y.1.length = (RWRS.pipePred B L u).1.length := by rw [hy]
      _ ≤ u.1.length := pipePred_length_le u
      _ ≤ n := hu.2.1
  · obtain ⟨v', j⟩ := y
    match j with
    | 0 =>
        simp only [RWRS.pipePred] at hu'
        by_cases hv : v' = []
        · simp [hv]
        · rw [if_neg hv] at hu'
          have hlen : 1 ≤ v'.length := List.length_pos_iff.mpr hv
          rw [if_pos (hL2 v'.length hlen)] at hu'
          have : u.1 = v' := by rw [hu']
          rw [← this]
          exact hu.2.1
    | j + 1 =>
        simp only [RWRS.pipePred] at hu'
        by_cases hj : j = 0
        · rw [if_pos hj] at hu'
          have hv : v' ≠ [] := by
            intro hc
            subst hc
            rcases hyv with h0 | ⟨hne, -⟩
            · simp at h0
            · exact hne rfl
          have h1 : u.1 = v'.dropLast := by rw [hu']
          have h2 : u.2 = 0 := by rw [hu']
          have hlt : u.1.length < n := by
            rcases hu.2.2.2 with h3 | ⟨-, h3⟩
            · omega
            · exact h3
          rw [h1] at hlt
          have hdl : v'.dropLast.length = v'.length - 1 := List.length_dropLast
          have hpos : 1 ≤ v'.length := List.length_pos_iff.mpr hv
          simp only [hdl] at hlt
          simp only []
          omega
        · rw [if_neg hj] at hu'
          have : u.1 = v' := by rw [hu']
          rw [← this]
          exact hu.2.1

theorem neighborFinset_gadget_image {n : ℕ} (u : RWRS.gadgetSites B L n)
    (hall : ∀ y, (RWRS.pipeGraph B L false).Adj u.1 y → y ∈ RWRS.gadgetSites B L n) :
    (RWRS.pipeGraph B L false).neighborFinset u.1
      = Finset.image Subtype.val ((RWRS.gadgetGraph B L n).neighborFinset u) := by
  ext y
  simp only [Finset.mem_image, SimpleGraph.mem_neighborFinset]
  constructor
  · intro hy
    exact ⟨⟨y, hall y hy⟩, hy, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact hz

/-! ### The gadget inside the ray graph -/

section
variable {m s : ℕ → ℕ}
variable [inst : (rayGraph B L m s).LocallyFinite]

/-- Away from its root, a gadget site has exactly its gadget neighbours. -/
theorem neighborFinset_ray_inr {k : ℕ} {v : RWRS.gadgetSites B L (m k)}
    (hv : v ≠ RWRS.gadgetRoot B L (m k)) :
    (rayGraph B L m s).neighborFinset (rayEmb B L m s k v)
      = ((RWRS.gadgetGraph B L (m k)).neighborFinset v).image (rayEmb B L m s k) := by
  ext y
  simp only [Finset.mem_image, SimpleGraph.mem_neighborFinset]
  constructor
  · intro h
    rw [rayEmb_of_ne hv] at h
    obtain ⟨w', hw', hy⟩ := nbr_inr_subset (s := s) k v hv h
    exact ⟨w', hw', hy⟩
  · rintro ⟨w', hw', rfl⟩
    exact Or.inr (Or.inr ⟨k, v, w', hw', rfl, rfl⟩)

/-- **At the attachment vertex the ray graph has two neighbours the comb does
not have.** -/
theorem neighborFinset_ray_attach (hs : StrictMono s) {k : ℕ} (hsk : 1 ≤ s k) :
    (rayGraph B L m s).neighborFinset (rayPt B L m (s k))
      = insert (rayPt B L m (s k - 1)) (insert (rayPt B L m (s k + 1))
          (((RWRS.gadgetGraph B L (m k)).neighborFinset
              (RWRS.gadgetRoot B L (m k))).image (rayEmb B L m s k))) := by
  ext y
  simp only [Finset.mem_insert, Finset.mem_image, SimpleGraph.mem_neighborFinset]
  constructor
  · rintro (⟨i, h1, h2⟩ | ⟨i, h1, h2⟩ | ⟨j, v, w', hvw, h1, h2⟩)
    · have hi : s k = i := Sum.inl.inj h1
      subst hi
      exact Or.inr (Or.inl h2)
    · have hi : s k = i + 1 := Sum.inl.inj h2
      refine Or.inl ?_
      rw [h1, rayPt, rayPt]
      congr 1
      omega
    · have hvroot : v = RWRS.gadgetRoot B L (m j) := by
        by_contra hc
        rw [rayEmb_of_ne hc] at h1
        exact Sum.inl_ne_inr h1
      subst hvroot
      rw [rayEmb_root] at h1
      have hjk : j = k := hs.injective (Sum.inl.inj h1).symm
      subst hjk
      exact Or.inr (Or.inr ⟨w', hvw, h2.symm⟩)
  · rintro (rfl | rfl | ⟨w', hw', rfl⟩)
    · refine Or.inr (Or.inl ⟨s k - 1, rfl, ?_⟩)
      rw [rayPt, rayPt]
      congr 1
      omega
    · exact Or.inl ⟨s k, rfl, rfl⟩
    · exact Or.inr (Or.inr ⟨k, RWRS.gadgetRoot B L (m k), w', hw',
        (rayEmb_root k).symm, rfl⟩)

omit inst in
theorem rayPt_notMem_image_gadget {k : ℕ} (i : ℕ) :
    rayPt B L m i ∉ (((RWRS.gadgetGraph B L (m k)).neighborFinset
        (RWRS.gadgetRoot B L (m k))).image (rayEmb B L m s k)) := by
  rw [Finset.mem_image]
  rintro ⟨w', hw', hy⟩
  rw [SimpleGraph.mem_neighborFinset] at hw'
  rw [rayEmb_of_ne (fun hc => hw'.ne' hc)] at hy
  exact Sum.inr_ne_inl hy

/-! ### The transport -/

omit inst in
/-- The sum over the neighbours of a gadget site, transported to the ray graph. -/
theorem sum_transport {k : ℕ} {u : List (Fin B) × ℕ} (hu : u ∈ RWRS.gadgetSites B L (m k))
    (hall : ∀ y, (RWRS.pipeGraph B L false).Adj u y → y ∈ RWRS.gadgetSites B L (m k))
    (F : RayV B L m → ℝ) :
    ∑ y ∈ (RWRS.pipeGraph B L false).neighborFinset u,
        (if h : y ∈ RWRS.gadgetSites B L (m k) then F (rayEmb B L m s k ⟨y, h⟩) else 0)
      = ∑ x ∈ ((RWRS.gadgetGraph B L (m k)).neighborFinset
          (⟨u, hu⟩ : RWRS.gadgetSites B L (m k))).image (rayEmb B L m s k), F x := by
  classical
  rw [neighborFinset_gadget_image (⟨u, hu⟩ : RWRS.gadgetSites B L (m k)) hall,
    Finset.sum_image (fun a _ b _ h => Subtype.ext h),
    Finset.sum_image (fun a _ b _ h => rayEmb_injective k h)]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [dif_pos z.2]

/-- **The voltage of `C_k` restricted to the comb is the comb's own voltage.**
The transported function solves the comb's boundary value problem: away from the
root it is harmonic because the neighbours agree, and at the root the two extra
ray neighbours contribute `0` (the vertex beyond the attachment point is outside
`C_k`) and `1` (the backbone drop), which is exactly the unit source. -/
theorem ray_eq_combVoltage (hB : 2 ≤ B) (hL2 : ∀ j, 1 ≤ j → 2 ≤ L j) (hs : StrictMono s)
    {k : ℕ} {w : List (Fin B)} (hw : w.length = m k) (hmk : 1 ≤ m k) (hsk : 1 ≤ s k)
    (v : RWRS.gadgetSites B L (m k)) :
    RWRS.killedGreenReal (rayGraph B L m s)
        ((recSet B L m s hs k w : Finset (RayV B L m)) : Set (RayV B L m))
        (rayPt B L m 0) (rayEmb B L m s k v)
      = RWRS.combVoltage B L true (m k) w (v : List (Fin B) × ℕ) := by
  classical
  have hL : ∀ j, 1 ≤ j → 1 ≤ L j := one_le_of_two_le hL2
  set g : RayV B L m → ℝ := fun x => RWRS.killedGreenReal (rayGraph B L m s)
      ((recSet B L m s hs k w : Finset (RayV B L m)) : Set (RayV B L m))
      (rayPt B L m 0) x with hgdef
  set f : List (Fin B) × ℕ → ℝ := fun u =>
    if h : u ∈ RWRS.gadgetSites B L (m k) then g (rayEmb B L m s k ⟨u, h⟩) else 0 with hfdef
  -- the transported function vanishes off the comb
  have hroot : (RWRS.pipeRoot B) ∈ RWRS.combSet B L (m k) w :=
    pipeRoot_mem_combSet w hmk
  have hne_root : ∀ (u : List (Fin B) × ℕ) (hu : u ∈ RWRS.gadgetSites B L (m k)),
      u ∉ RWRS.combSet B L (m k) w →
      (⟨u, hu⟩ : RWRS.gadgetSites B L (m k)) ≠ RWRS.gadgetRoot B L (m k) := by
    intro u hu hnc hc
    have heq : u = RWRS.pipeRoot B := congrArg Subtype.val hc
    exact hnc (heq ▸ hroot)
  have hout : ∀ u, u ∉ combFinset B L (m k) w → f u = 0 := by
    intro u hu
    have hu' : u ∉ RWRS.combSet B L (m k) w := by
      rw [← coe_combFinset (B := B) (L := L) (m k) w]
      exact_mod_cast hu
    rw [hfdef]
    by_cases hg' : u ∈ RWRS.gadgetSites B L (m k)
    · simp only [dif_pos hg']
      refine recVolt_eq_zero hL hs k w ?_
      rw [rayEmb_of_ne (hne_root u hg' hu')]
      rw [recSet, Finset.mem_union]
      rintro (h1 | h2)
      · rw [mem_rayBall] at h1
        have : s k ≤ s k - 1 := h1
        omega
      · rw [rayComb, Finset.mem_image] at h2
        obtain ⟨z, hz, hzeq⟩ := h2
        rw [mem_combGadget] at hz
        rw [← rayEmb_of_ne (hne_root u hg' hu')] at hzeq
        have := rayEmb_injective (s := s) k hzeq
        rw [this] at hz
        exact hu' hz
    · simp only [dif_neg hg']
  -- the transported function is harmonic away from the root
  have hlap : ∀ u ∈ combFinset B L (m k) w,
      RWRS.laplacian (RWRS.pipeGraph B L true) f u
        = -(@ite ℝ (u = RWRS.pipeRoot B) (Classical.propDecidable _) 1 0) := by
    intro u hu
    have huS : u ∈ RWRS.combSet B L (m k) w := by
      rw [← coe_combFinset (B := B) (L := L) (m k) w]
      exact_mod_cast hu
    have hug : u ∈ RWRS.gadgetSites B L (m k) := combSet_subset_gadgetSites (m k) w huS
    have hall : ∀ y, (RWRS.pipeGraph B L false).Adj u y →
        y ∈ RWRS.gadgetSites B L (m k) := fun y hy => comb_nbr_mem_gadgetSites hL2 huS hy
    have hfu : f u = g (rayEmb B L m s k ⟨u, hug⟩) := by rw [hfdef]; simp only [dif_pos hug]
    have hterm : ∀ y ∈ (RWRS.pipeGraph B L false).neighborFinset u,
        f y - f u
          = (if h : y ∈ RWRS.gadgetSites B L (m k) then
              (fun x => g x - f u) (rayEmb B L m s k ⟨y, h⟩) else 0) := by
      intro y hy
      have hyg : y ∈ RWRS.gadgetSites B L (m k) :=
        hall y ((SimpleGraph.mem_neighborFinset _ _ _).1 hy)
      simp only [dif_pos hyg, hfdef]
    have hsum : ∑ y ∈ (RWRS.pipeGraph B L false).neighborFinset u, (f y - f u)
        = ∑ x ∈ ((RWRS.gadgetGraph B L (m k)).neighborFinset
            (⟨u, hug⟩ : RWRS.gadgetSites B L (m k))).image (rayEmb B L m s k),
              (g x - f u) := by
      rw [Finset.sum_congr rfl hterm]
      exact sum_transport hug hall (fun x => g x - f u)
    by_cases huroot : u = RWRS.pipeRoot B
    · -- the root of the comb
      subst huroot
      rw [if_pos rfl]
      have hrootg : (⟨RWRS.pipeRoot B, hug⟩ : RWRS.gadgetSites B L (m k))
          = RWRS.gadgetRoot B L (m k) := rfl
      have hfr : f (RWRS.pipeRoot B) = g (rayPt B L m (s k)) := by
        rw [hfu, hrootg, rayEmb_root]
      have hextra : f (pipeExtra B) = 0 := by
        rw [hfdef]
        refine dif_neg fun hc => not_pipeValid_pipeExtra (L := L) hc.1
      -- the ray graph is harmonic at the attachment vertex
      have hharm : RWRS.laplacian (rayGraph B L m s) g (rayPt B L m (s k)) = 0 :=
        harmonic_killedGreenReal_of_escape (recSet B L m s hs k w) (ray_escape hL _)
          (fun z _ => ray_degree_pos hL z) (rayPt_zero_mem_recSet hs k w)
          (rayPt_attach_mem_recSet hs hmk)
          (fun hc => by
            have : s k = 0 := Sum.inl.inj hc
            omega)
      rw [RWRS.laplacian, neighborFinset_ray_attach hs hsk,
        Finset.sum_insert (by
          simp only [Finset.mem_insert]
          rintro (hc | hc)
          · exact absurd (Sum.inl.inj hc) (by omega)
          · exact rayPt_notMem_image_gadget (s := s) (k := k) (s k - 1) hc),
        Finset.sum_insert (rayPt_notMem_image_gadget (s := s) (k := k) (s k + 1))] at hharm
      have hzero : g (rayPt B L m (s k + 1)) = 0 :=
        recVolt_eq_zero hL hs k w (rayPt_succ_attach_notMem_recSet hs k w)
      have hdrop : g (rayPt B L m (s k - 1)) - g (rayPt B L m (s k)) = 1 := by
        have h1 := backbone_drop hL hs (m := m) (k := k) (w := w)
          (i := s k - 1) (by omega)
        rw [show s k - 1 + 1 = s k by omega] at h1
        exact h1
      rw [RWRS.laplacian, neighborFinset_pipe_true_root,
        Finset.sum_insert (notMem_pipeExtra_false (L := L)), hsum, hfr, hextra]
      have hgadget : ∑ x ∈ ((RWRS.gadgetGraph B L (m k)).neighborFinset
          (⟨RWRS.pipeRoot B, hug⟩ : RWRS.gadgetSites B L (m k))).image (rayEmb B L m s k),
            (g x - g (rayPt B L m (s k))) = -1 + g (rayPt B L m (s k)) := by
        rw [hrootg] at *
        linarith [hharm, hzero, hdrop]
      rw [show (⟨RWRS.pipeRoot B, hug⟩ : RWRS.gadgetSites B L (m k))
          = RWRS.gadgetRoot B L (m k) from rfl] at hgadget ⊢
      rw [hgadget]
      ring
    · -- away from the root
      rw [if_neg huroot]
      have hunotroot : (⟨u, hug⟩ : RWRS.gadgetSites B L (m k))
          ≠ RWRS.gadgetRoot B L (m k) := fun hc => huroot (congrArg Subtype.val hc)
      have hharm : RWRS.laplacian (rayGraph B L m s) g (rayEmb B L m s k ⟨u, hug⟩) = 0 := by
        refine harmonic_killedGreenReal_of_escape (recSet B L m s hs k w) (ray_escape hL _)
          (fun z _ => ray_degree_pos hL z) (rayPt_zero_mem_recSet hs k w) ?_ ?_
        · refine Finset.mem_union_right _ ?_
          rw [rayComb, Finset.mem_image]
          exact ⟨⟨u, hug⟩, (mem_combGadget _).2 huS, rfl⟩
        · rw [rayEmb_of_ne hunotroot]
          exact Sum.inr_ne_inl
      rw [RWRS.laplacian, neighborFinset_pipe_true_eq huS.1 huroot, hsum, hfu]
      rw [RWRS.laplacian, neighborFinset_ray_inr hunotroot] at hharm
      rw [hharm]
      norm_num
  -- uniqueness
  have hkey := eq_killedGreenReal_of_boundaryValue (G := RWRS.pipeGraph B L true)
    (combFinset B L (m k) w) (comb_esc hL2 true hw) (comb_deg hL2 true hB)
    (comb_root_mem (L := L) (w := w) hmk) f hlap hout (v : List (Fin B) × ℕ)
  rw [coe_combFinset] at hkey
  rw [hfdef] at hkey
  simp only [dif_pos v.2] at hkey
  rw [RWRS.combVoltage, ← hkey]

end

end RWRS.Support
