import RWRS.Support.Comb

namespace RWRS.Support

open scoped ENNReal

variable {B : ℕ} {L : ℕ → ℕ}

/-- The sites of the tree of pipes, as a set. -/
def pipeSites (B : ℕ) (L : ℕ → ℕ) : Set (List (Fin B) × ℕ) := {v | PipeValid B L v}

/-- The tree of pipes as a graph on its own sites. -/
abbrev pipeSub (B : ℕ) (L : ℕ → ℕ) : SimpleGraph (pipeSites B L) :=
  (pipeGraph B L false).induce (pipeSites B L)

theorem pipeSub_adj_iff {u v : pipeSites B L} :
    (pipeSub B L).Adj u v ↔ (pipeGraph B L false).Adj u.1 v.1 := Iff.rfl

/-- Adjacency in the tree of pipes never leaves the sites. -/
theorem mem_pipeSites_of_adj {u v : List (Fin B) × ℕ}
    (h : (pipeGraph B L false).Adj u v) : v ∈ pipeSites B L := by
  rcases h.2.1 with hv | ⟨he, -⟩
  · exact hv
  · exact absurd he (by simp)

noncomputable instance pipeSubLocallyFinite (B : ℕ) (L : ℕ → ℕ) :
    (pipeSub B L).LocallyFinite := by
  intro u
  have hfin : (Subtype.val ⁻¹' ((pipeGraph B L false).neighborSet u.1) :
      Set (pipeSites B L)).Finite :=
    Set.Finite.preimage Subtype.val_injective.injOn (Set.toFinite _)
  exact Set.Finite.fintype hfin

/-! ### The neighbours, the degree and the walk average -/

open scoped Classical in
theorem neighborFinset_pipeSub_image (u : pipeSites B L) :
    (pipeGraph B L false).neighborFinset u.1
      = Finset.image Subtype.val ((pipeSub B L).neighborFinset u) := by
  apply Finset.ext
  intro y
  simp only [Finset.mem_image, SimpleGraph.mem_neighborFinset]
  constructor
  · intro hy
    exact ⟨⟨y, mem_pipeSites_of_adj hy⟩, hy, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact hz

open scoped Classical in
theorem sum_neighborFinset_pipeSub (u : pipeSites B L) (f : (List (Fin B) × ℕ) → ℝ) :
    ∑ y ∈ (pipeSub B L).neighborFinset u, f y.1
      = ∑ y ∈ (pipeGraph B L false).neighborFinset u.1, f y := by
  rw [neighborFinset_pipeSub_image u,
    Finset.sum_image (fun a _ b _ h => Subtype.ext h)]

open scoped Classical in
theorem degree_pipeSub (u : pipeSites B L) :
    (pipeSub B L).degree u = (pipeGraph B L false).degree u.1 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree,
    neighborFinset_pipeSub_image u,
    Finset.card_image_of_injective _ Subtype.val_injective]

theorem walkOp_pipeSub (f : (List (Fin B) × ℕ) → ℝ) (u : pipeSites B L) :
    RWRS.walkOp (pipeSub B L) (fun y => f y.1) u = RWRS.walkOp (pipeGraph B L false) f u.1 := by
  rw [RWRS.walkOp, RWRS.walkOp, sum_neighborFinset_pipeSub, degree_pipeSub]

/-- The root of the tree of pipes, as a site. -/
def pipeRootSub (B : ℕ) (L : ℕ → ℕ) : pipeSites B L := ⟨pipeRoot B, Or.inl rfl⟩

/-! ### The killed Green function of the tree of pipes -/

theorem killedHeat_pipeSub (C : Set (List (Fin B) × ℕ)) :
    ∀ (k : ℕ) (u v : pipeSites B L),
      RWRS.killedHeat (pipeSub B L) (Subtype.val ⁻¹' C) k u v
        = RWRS.killedHeat (pipeGraph B L false) C k u.1 v.1 := by
  intro k
  induction k with
  | zero =>
      intro u v
      by_cases hu : (u : List (Fin B) × ℕ) ∈ C
      · have hu' : u ∈ Subtype.val ⁻¹' C := hu
        simp only [RWRS.killedHeat, if_pos hu, if_pos hu']
        by_cases huv : u = v
        · simp [huv]
        · have : (u : List (Fin B) × ℕ) ≠ v.1 := fun h => huv (Subtype.ext h)
          simp [huv, this]
      · have hu' : u ∉ Subtype.val ⁻¹' C := hu
        simp only [RWRS.killedHeat, if_neg hu, if_neg hu']
  | succ k ih =>
      intro u v
      by_cases hu : (u : List (Fin B) × ℕ) ∈ C
      · have hu' : u ∈ Subtype.val ⁻¹' C := hu
        simp only [RWRS.killedHeat, if_pos hu, if_pos hu']
        have hw := walkOp_pipeSub (fun y : List (Fin B) × ℕ =>
          RWRS.killedHeat (pipeGraph B L false) C k y v.1) u
        rw [← hw]
        congr 1
        funext z
        exact ih z v
      · have hu' : u ∉ Subtype.val ⁻¹' C := hu
        simp only [RWRS.killedHeat, if_neg hu, if_neg hu']

theorem killedGreen_pipeSub (C : Set (List (Fin B) × ℕ)) (u v : pipeSites B L) :
    RWRS.killedGreen (pipeSub B L) (Subtype.val ⁻¹' C) u v
      = RWRS.killedGreen (pipeGraph B L false) C u.1 v.1 := by
  rw [RWRS.killedGreen, RWRS.killedGreen, degree_pipeSub]
  congr 1
  exact tsum_congr fun k => by rw [killedHeat_pipeSub C k u v]

theorem killedGreenReal_pipeSub (C : Set (List (Fin B) × ℕ)) (u v : pipeSites B L) :
    RWRS.killedGreenReal (pipeSub B L) (Subtype.val ⁻¹' C) u v
      = RWRS.killedGreenReal (pipeGraph B L false) C u.1 v.1 := by
  rw [RWRS.killedGreenReal, RWRS.killedGreenReal, killedGreen_pipeSub]


/-! ### Connectivity, infinitude and the degree bound -/

theorem reachable_pipeRootSub (hL : ∀ j, 1 ≤ j → 1 ≤ L j) :
    ∀ (n : ℕ) (v : pipeSites B L), pipeDepth L (v : List (Fin B) × ℕ) ≤ n →
      (pipeSub B L).Reachable (pipeRootSub B L) v := by
  intro n
  induction n with
  | zero =>
      intro v hv
      have hroot : (v : List (Fin B) × ℕ) = pipeRoot B :=
        eq_root_of_pipeDepth_zero hL v.2 (Nat.le_zero.1 hv)
      have : v = pipeRootSub B L := Subtype.ext hroot
      subst this
      exact SimpleGraph.Reachable.refl _
  | succ n ih =>
      intro v hv
      by_cases hz : (v : List (Fin B) × ℕ) = pipeRoot B
      · have : v = pipeRootSub B L := Subtype.ext hz
        subst this
        exact SimpleGraph.Reachable.refl _
      · have hdrop := pipeDepth_pred_lt hL v.2 hz
        have humem : pipePred B L (v : List (Fin B) × ℕ) ∈ pipeSites B L :=
          pipePred_valid v.2
        have hadj : (pipeSub B L).Adj ⟨pipePred B L (v : List (Fin B) × ℕ), humem⟩ v :=
          ⟨Or.inl humem, Or.inl v.2, pipePred_ne_self hL v.2 hz, Or.inr rfl⟩
        exact (ih ⟨pipePred B L (v : List (Fin B) × ℕ), humem⟩
          (Nat.lt_succ_iff.1 (lt_of_lt_of_le hdrop hv))).trans hadj.reachable

theorem pipeSub_connected (hL : ∀ j, 1 ≤ j → 1 ≤ L j) : (pipeSub B L).Connected := by
  haveI : Nonempty (pipeSites B L) := ⟨pipeRootSub B L⟩
  refine SimpleGraph.Connected.mk ?_
  intro u v
  exact ((reachable_pipeRootSub hL _ u le_rfl).symm).trans
    (reachable_pipeRootSub hL _ v le_rfl)


theorem pipeSites_infinite (hB : 1 ≤ B) : Infinite (pipeSites B L) := by
  haveI : Nonempty (Fin B) := ⟨⟨0, hB⟩⟩
  refine Infinite.of_injective
    (fun w : List (Fin B) => (⟨(w, 0), Or.inl rfl⟩ : pipeSites B L)) ?_
  intro a b h
  have h1 : ((a, 0) : List (Fin B) × ℕ) = (b, 0) := congrArg Subtype.val h
  exact (Prod.mk.injEq _ _ _ _ ▸ h1).1

open scoped Classical in
theorem degree_pipeGraph_le (e : Bool) (u : List (Fin B) × ℕ) :
    (pipeGraph B L e).degree u ≤ 2 * B + 3 := by
  have hsub : (pipeGraph B L e).neighborFinset u ⊆ (pipeNbrList B L u).toFinset := by
    intro y hy
    simp only [List.mem_toFinset]
    exact pipe_nbr_subset B L e u ((SimpleGraph.mem_neighborFinset _ _ _).mp hy)
  have h1 : (pipeGraph B L e).degree u ≤ (pipeNbrList B L u).length := by
    calc (pipeGraph B L e).degree u
        = ((pipeGraph B L e).neighborFinset u).card :=
          (SimpleGraph.card_neighborFinset_eq_degree _ _).symm
      _ ≤ (pipeNbrList B L u).toFinset.card := Finset.card_le_card hsub
      _ ≤ (pipeNbrList B L u).length := List.toFinset_card_le _
  have h2 : (pipeNbrList B L u).length = 2 * B + 3 := by
    simp [pipeNbrList, List.length_flatMap]
    ring
  omega

open scoped Classical in
theorem degree_induce_le {W : Type*} (H : SimpleGraph W) [H.LocallyFinite] (S : Set W)
    (u : S) [Fintype ((H.induce S).neighborSet u)] :
    (H.induce S).degree u ≤ H.degree u.1 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree]
  refine Finset.card_le_card_of_injOn (fun y => (y : W)) ?_ (fun a _ b _ h => Subtype.ext h)
  intro y hy
  rw [Finset.mem_coe, SimpleGraph.mem_neighborFinset] at hy
  exact (SimpleGraph.mem_neighborFinset _ _ _).2 hy

open scoped Classical in
theorem boundedDegree_pipeSub : RWRS.BoundedDegree (pipeSub B L) (2 * B + 3) := by
  intro u
  rw [degree_pipeSub]
  have hsub : (pipeGraph B L false).neighborFinset u.1 ⊆ (pipeNbrList B L u.1).toFinset := by
    intro y hy
    simp only [List.mem_toFinset]
    exact pipe_nbr_subset B L false u.1 ((SimpleGraph.mem_neighborFinset _ _ _).mp hy)
  have h1 : (pipeGraph B L false).degree u.1 ≤ (pipeNbrList B L u.1).length := by
    calc (pipeGraph B L false).degree u.1
        = ((pipeGraph B L false).neighborFinset u.1).card :=
          (SimpleGraph.card_neighborFinset_eq_degree _ _).symm
      _ ≤ (pipeNbrList B L u.1).toFinset.card := Finset.card_le_card hsub
      _ ≤ (pipeNbrList B L u.1).length := List.toFinset_card_le _
  have h2 : (pipeNbrList B L u.1).length = 2 * B + 3 := by
    simp [pipeNbrList, List.length_flatMap]
    ring
  omega


end RWRS.Support
