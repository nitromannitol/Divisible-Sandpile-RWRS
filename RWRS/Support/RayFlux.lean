/-
The voltage of `sec:recurrent-nonstab` on the backbone.

`C_k` is the ray segment up to the attachment vertex of the `k`-th gadget,
together with every earlier gadget and the comb of the `k`-th, and `g_k` is the
voltage it carries with the source at the root.  Two facts about `g_k` come from
Kirchhoff's node law.  The set of vertices at ray level at most `i` is separated
from the rest by the single backbone edge `r_i r_{i+1}`, so for `i` below the
attachment vertex the current across that edge is the whole unit current and the
voltage drops by exactly one; and the current leaving `C_k` itself is one, with
every term of the same sign, so the term carried by the edge `r_{s_k} r_{s_k+1}`
is at most one.  Together with the maximum principle at the source they bound
the voltage by `s_k + 1` everywhere.
-/
import RWRS.Support.RayRecurrent
import RWRS.Support.GreenUnique
import RWRS.Support.PipeNbr

namespace RWRS.Support

open scoped Classical
open LatticeProb.Network

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

/-- The double sum over the pairs leaving a finite set is the sum over its cut
pairs. -/
theorem sum_cut_eq_sum_cutPairs (U : Finset V) (F : V → V → ℝ) :
    ∑ u ∈ U, ∑ y ∈ (G.neighborFinset u).filter (fun y => y ∉ U), F u y
      = ∑ p ∈ cutPairs G U, F p.1 p.2 := by
  classical
  rw [cutPairs, Finset.sum_biUnion]
  · refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_image (fun a _ b _ h => (Prod.mk.injEq _ _ _ _ ▸ h).2)]
  · intro a _ b _ hab
    simp only [Function.onFun, Finset.disjoint_left, Finset.mem_image]
    rintro p ⟨y, -, rfl⟩ ⟨z, -, hz⟩
    exact hab (congrArg Prod.fst hz).symm

/-! ### The comb inside the ray graph -/

variable {B : ℕ} {L : ℕ → ℕ} {m s : ℕ → ℕ}

/-- Every site of the comb is a site of the gadget of the same depth. -/
theorem combSet_subset_gadgetSites (n : ℕ) (w : List (Fin B)) :
    RWRS.combSet B L n w ⊆ RWRS.gadgetSites B L n := fun _ hv => ⟨hv.1, hv.2.1⟩

/-- The comb as a finset of gadget sites. -/
noncomputable def combGadget (B : ℕ) (L : ℕ → ℕ) (n : ℕ) (w : List (Fin B)) :
    Finset (RWRS.gadgetSites B L n) :=
  (combFinset B L n w).subtype (fun v => v ∈ RWRS.gadgetSites B L n)

theorem mem_combGadget {n : ℕ} {w : List (Fin B)} (v : RWRS.gadgetSites B L n) :
    v ∈ combGadget B L n w ↔ (v : List (Fin B) × ℕ) ∈ RWRS.combSet B L n w := by
  rw [combGadget, Finset.mem_subtype, ← Finset.mem_coe, coe_combFinset]

/-- The comb of the `k`-th gadget, read in the ray graph. -/
noncomputable def rayComb (B : ℕ) (L : ℕ → ℕ) (m s : ℕ → ℕ) (k : ℕ) (w : List (Fin B)) :
    Finset (RayV B L m) :=
  (combGadget B L (m k) w).image (rayEmb B L m s k)

/-- **The set `C_k`**: the ray up to the attachment vertex of the `k`-th gadget
together with the earlier gadgets, and the comb of the `k`-th gadget. -/
noncomputable def recSet (B : ℕ) (L : ℕ → ℕ) (m s : ℕ → ℕ) (hs : StrictMono s)
    (k : ℕ) (w : List (Fin B)) : Finset (RayV B L m) :=
  rayBall B L m s hs (s k - 1) ∪ rayComb B L m s k w

theorem rayBall_subset_recSet (hs : StrictMono s) (k : ℕ) (w : List (Fin B))
    {i : ℕ} (hi : i ≤ s k - 1) :
    rayBall B L m s hs i ⊆ recSet B L m s hs k w :=
  fun _ hx => Finset.mem_union_left _ (rayBall_mono hs hi hx)

theorem rayPt_zero_mem_rayBall (hs : StrictMono s) (i : ℕ) :
    rayPt B L m 0 ∈ rayBall B L m s hs i := by
  rw [mem_rayBall]; exact Nat.zero_le _

theorem rayPt_zero_mem_recSet (hs : StrictMono s) (k : ℕ) (w : List (Fin B)) :
    rayPt B L m 0 ∈ recSet B L m s hs k w :=
  rayBall_subset_recSet hs k w le_rfl (rayPt_zero_mem_rayBall hs _)

/-- The attachment vertex of the `k`-th gadget lies in `C_k`, through the comb. -/
theorem rayPt_attach_mem_recSet (hs : StrictMono s) {k : ℕ} {w : List (Fin B)}
    (hmk : 1 ≤ m k) :
    rayPt B L m (s k) ∈ recSet B L m s hs k w := by
  refine Finset.mem_union_right _ ?_
  rw [rayComb, Finset.mem_image]
  refine ⟨RWRS.gadgetRoot B L (m k), ?_, rayEmb_root k⟩
  rw [mem_combGadget]
  exact pipeRoot_mem_combSet w hmk

/-- The ray vertex just beyond the attachment vertex lies outside `C_k`. -/
theorem rayPt_succ_attach_notMem_recSet (hs : StrictMono s) (k : ℕ) (w : List (Fin B)) :
    rayPt B L m (s k + 1) ∉ recSet B L m s hs k w := by
  rw [recSet, Finset.mem_union]
  rintro (hx | hx)
  · rw [mem_rayBall] at hx
    have hle : s k + 1 ≤ s k - 1 := hx
    omega
  · rw [rayComb, Finset.mem_image] at hx
    obtain ⟨v, -, hv⟩ := hx
    by_cases hroot : v = RWRS.gadgetRoot B L (m k)
    · rw [hroot, rayEmb_root] at hv
      exact absurd (Sum.inl.inj hv) (by omega)
    · rw [rayEmb_of_ne hroot] at hv
      exact Sum.inr_ne_inl hv

section
variable [inst : (rayGraph B L m s).LocallyFinite]

omit inst in
/-- The escape hypothesis on the ray graph. -/
theorem ray_escape (hL : ∀ j, 1 ≤ j → 1 ≤ L j) (C : Finset (RayV B L m))
    (x : RayV B L m) :
    ∃ (q : RayV B L m) (_ : (rayGraph B L m s).Walk x q), q ∉ (C : Set (RayV B L m)) := by
  haveI : Infinite (RayV B L m) := infinite_rayV
  exact escape_of_finite (rayGraph_connected hL) C x

/-- Every vertex of the ray graph has a neighbour. -/
theorem ray_degree_pos (hL : ∀ j, 1 ≤ j → 1 ≤ L j) (x : RayV B L m) :
    0 < (rayGraph B L m s).degree x := by
  haveI : Infinite (RayV B L m) := infinite_rayV
  haveI : Nontrivial (RayV B L m) := Infinite.instNontrivial _
  exact degree_pos_of_connected (rayGraph_connected hL) x

theorem recVolt_nonneg (hL : ∀ j, 1 ≤ j → 1 ≤ L j) (hs : StrictMono s)
    (k : ℕ) (w : List (Fin B)) (x : RayV B L m) :
    0 ≤ RWRS.killedGreenReal (rayGraph B L m s)
      ((recSet B L m s hs k w : Finset (RayV B L m)) : Set (RayV B L m))
      (rayPt B L m 0) x :=
  killedGreenReal_nonneg_of_escape (recSet B L m s hs k w) (ray_escape hL _) _ _

theorem recVolt_eq_zero (hL : ∀ j, 1 ≤ j → 1 ≤ L j) (hs : StrictMono s)
    (k : ℕ) (w : List (Fin B)) {x : RayV B L m} (hx : x ∉ recSet B L m s hs k w) :
    RWRS.killedGreenReal (rayGraph B L m s)
      ((recSet B L m s hs k w : Finset (RayV B L m)) : Set (RayV B L m))
      (rayPt B L m 0) x = 0 :=
  killedGreenReal_eq_zero_of_not_mem_of_escape (recSet B L m s hs k w) (ray_escape hL _)
    (by exact_mod_cast hx) _

/-- **Unit current traverses every backbone edge below the attachment vertex.** -/
theorem backbone_drop (hL : ∀ j, 1 ≤ j → 1 ≤ L j) (hs : StrictMono s)
    {k : ℕ} {w : List (Fin B)} {i : ℕ} (hi : i < s k) :
    RWRS.killedGreenReal (rayGraph B L m s) ((recSet B L m s hs k w : Finset (RayV B L m)) : Set (RayV B L m)) (rayPt B L m 0) (rayPt B L m i)
      - RWRS.killedGreenReal (rayGraph B L m s) ((recSet B L m s hs k w : Finset (RayV B L m)) : Set (RayV B L m)) (rayPt B L m 0) (rayPt B L m (i + 1)) = 1 := by
  classical
  have hcut := current_across_cut (G := rayGraph B L m s) (recSet B L m s hs k w)
    (ray_escape hL _) (fun v _ => ray_degree_pos hL v)
    (rayPt_zero_mem_recSet hs k w) (rayBall B L m s hs i)
    (rayBall_subset_recSet hs k w (by omega)) (rayPt_zero_mem_rayBall hs i)
  rw [sum_cut_eq_sum_cutPairs, cutPairs_rayBall hs i, Finset.sum_singleton] at hcut
  exact hcut

/-- **The voltage at the attachment vertex is at most one.** -/
theorem recVolt_attach_le_one (hL : ∀ j, 1 ≤ j → 1 ≤ L j) (hs : StrictMono s)
    {k : ℕ} {w : List (Fin B)} (hmk : 1 ≤ m k) :
    RWRS.killedGreenReal (rayGraph B L m s) ((recSet B L m s hs k w : Finset (RayV B L m)) : Set (RayV B L m)) (rayPt B L m 0) (rayPt B L m (s k)) ≤ 1 := by
  classical
  set C := recSet B L m s hs k w with hC
  have hcut := current_across_cut (G := rayGraph B L m s) C
    (ray_escape hL _) (fun v _ => ray_degree_pos hL v)
    (rayPt_zero_mem_recSet hs k w) C (Finset.Subset.refl _)
    (rayPt_zero_mem_recSet hs k w)
  rw [sum_cut_eq_sum_cutPairs] at hcut
  have hnn : ∀ p ∈ cutPairs (rayGraph B L m s) C,
      0 ≤ RWRS.killedGreenReal (rayGraph B L m s) ((recSet B L m s hs k w : Finset (RayV B L m)) : Set (RayV B L m)) (rayPt B L m 0) p.1 - RWRS.killedGreenReal (rayGraph B L m s) ((recSet B L m s hs k w : Finset (RayV B L m)) : Set (RayV B L m)) (rayPt B L m 0) p.2 := by
    intro p hp
    rw [mem_cutPairs] at hp
    rw [recVolt_eq_zero hL hs k w hp.2.1, sub_zero]
    exact recVolt_nonneg hL hs k w p.1
  have hmem : ((rayPt B L m (s k), rayPt B L m (s k + 1)) : RayV B L m × RayV B L m)
      ∈ cutPairs (rayGraph B L m s) C := by
    rw [mem_cutPairs]
    exact ⟨rayPt_attach_mem_recSet hs hmk, rayPt_succ_attach_notMem_recSet hs k w,
      rayGraph_adj_ray (s := s) (s k)⟩
  have hsingle := Finset.single_le_sum (f := fun p : RayV B L m × RayV B L m =>
    RWRS.killedGreenReal (rayGraph B L m s) ((recSet B L m s hs k w : Finset (RayV B L m)) : Set (RayV B L m)) (rayPt B L m 0) p.1 - RWRS.killedGreenReal (rayGraph B L m s) ((recSet B L m s hs k w : Finset (RayV B L m)) : Set (RayV B L m)) (rayPt B L m 0) p.2) hnn hmem
  rw [hcut] at hsingle
  have hzero := recVolt_eq_zero (m := m) hL hs k w (rayPt_succ_attach_notMem_recSet hs k w)
  simp only at hsingle
  linarith [hsingle, hzero]

/-- The voltage along the backbone: it drops by one at every step. -/
theorem recVolt_ray (hL : ∀ j, 1 ≤ j → 1 ≤ L j) (hs : StrictMono s)
    {k : ℕ} {w : List (Fin B)} :
    ∀ (d i : ℕ), i + d = s k →
      RWRS.killedGreenReal (rayGraph B L m s)
          ((recSet B L m s hs k w : Finset (RayV B L m)) : Set (RayV B L m))
          (rayPt B L m 0) (rayPt B L m i)
        = RWRS.killedGreenReal (rayGraph B L m s)
            ((recSet B L m s hs k w : Finset (RayV B L m)) : Set (RayV B L m))
            (rayPt B L m 0) (rayPt B L m (s k)) + (d : ℝ) := by
  intro d
  induction d with
  | zero =>
      intro i hi
      have : i = s k := by omega
      subst this
      simp
  | succ d ih =>
      intro i hi
      have hilt : i < s k := by omega
      have hstep := backbone_drop hL hs (m := m) (k := k) (w := w) hilt
      have hnext := ih (i + 1) (by omega)
      push_cast
      linarith [hstep, hnext]

/-- **The voltage is at most `s_k + 1` everywhere.** -/
theorem recVolt_le (hL : ∀ j, 1 ≤ j → 1 ≤ L j) (hs : StrictMono s)
    {k : ℕ} {w : List (Fin B)} (hmk : 1 ≤ m k) (x : RayV B L m) :
    RWRS.killedGreenReal (rayGraph B L m s) ((recSet B L m s hs k w : Finset (RayV B L m)) : Set (RayV B L m)) (rayPt B L m 0) x ≤ (s k : ℝ) + 1 := by
  have hroot : RWRS.killedGreenReal (rayGraph B L m s) ((recSet B L m s hs k w : Finset (RayV B L m)) : Set (RayV B L m)) (rayPt B L m 0) (rayPt B L m 0)
      = RWRS.killedGreenReal (rayGraph B L m s) ((recSet B L m s hs k w : Finset (RayV B L m)) : Set (RayV B L m)) (rayPt B L m 0) (rayPt B L m (s k)) + (s k : ℕ) := by
    have := recVolt_ray hL hs (m := m) (k := k) (w := w) (s k) 0 (by omega)
    simpa using this
  have hle := killedGreenReal_le_source (G := rayGraph B L m s)
    (recSet B L m s hs k w) (ray_escape hL _)
    (fun v _ => ray_degree_pos hL v) (rayPt_zero_mem_recSet hs k w) x
  have hatt := recVolt_attach_le_one hL hs (m := m) (k := k) (w := w) hmk
  linarith [hle, hroot, hatt]

end

end RWRS.Support
