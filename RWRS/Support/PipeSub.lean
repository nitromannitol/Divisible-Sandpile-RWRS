import RWRS.Support.Comb

/-!
# The tree of pipes as an induced subgraph

`pipeSites B L` is the set of valid pipe sites and `pipeSub B L` is the subgraph of the
ambient `pipeGraph` induced on them. This module transfers the basic graph invariants —
neighbor sets, degree, the walk-averaging operator, and the killed heat kernel and killed
Green's function — from the ambient graph to the induced one, then uses these transfers to
show `pipeSub` is connected, has infinitely many sites, and has degree bounded by `2B + 3`.
-/

namespace RWRS.Support

open scoped ENNReal

variable {B : ℕ} {L : ℕ → ℕ}

/-- The sites of the tree of pipes, as a set. -/
def pipeSites (B : ℕ) (L : ℕ → ℕ) : Set (List (Fin B) × ℕ) := {v | PipeValid B L v}

/-- The tree of pipes as a graph on its own sites. -/
abbrev pipeSub (B : ℕ) (L : ℕ → ℕ) : SimpleGraph (pipeSites B L) :=
  (pipeGraph B L false).induce (pipeSites B L)

/-- Adjacency in the induced subgraph `pipeSub` is definitionally adjacency in the ambient
`pipeGraph`. -/
theorem pipeSub_adj_iff {u v : pipeSites B L} :
    (pipeSub B L).Adj u v ↔ (pipeGraph B L false).Adj u.1 v.1 := Iff.rfl

/-- Adjacency in the tree of pipes never leaves the sites. -/
theorem mem_pipeSites_of_adj {u v : List (Fin B) × ℕ}
    (h : (pipeGraph B L false).Adj u v) : v ∈ pipeSites B L := by
  rcases h.2.1 with hv | ⟨he, -⟩
  · exact hv
  · exact absurd he (by simp)

/-- The tree of pipes is locally finite: the neighbor set of a site is the preimage under
`Subtype.val` of a finite set in the ambient `pipeGraph`. -/
noncomputable instance pipeSubLocallyFinite (B : ℕ) (L : ℕ → ℕ) :
    (pipeSub B L).LocallyFinite := by
  intro u
  have hfin : (Subtype.val ⁻¹' ((pipeGraph B L false).neighborSet u.1) :
      Set (pipeSites B L)).Finite :=
    Set.Finite.preimage Subtype.val_injective.injOn (Set.toFinite _)
  exact Set.Finite.fintype hfin

/-! ### The neighbours, the degree and the walk average -/

open scoped Classical in
/-- The ambient neighbor `Finset` of `u.1` in `pipeGraph` is the image under `Subtype.val` of
the neighbor `Finset` of `u` in the induced subgraph `pipeSub`, since adjacency never leaves
the sites. -/
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
/-- A sum of `f` over the `pipeSub`-neighbors of `u` equals the sum of `f` over the ambient
`pipeGraph`-neighbors of `u.1`, by reindexing along `neighborFinset_pipeSub_image`. -/
theorem sum_neighborFinset_pipeSub (u : pipeSites B L) (f : (List (Fin B) × ℕ) → ℝ) :
    ∑ y ∈ (pipeSub B L).neighborFinset u, f y.1
      = ∑ y ∈ (pipeGraph B L false).neighborFinset u.1, f y := by
  rw [neighborFinset_pipeSub_image u,
    Finset.sum_image (fun a _ b _ h => Subtype.ext h)]

open scoped Classical in
/-- The degree of a site in the induced subgraph `pipeSub` equals its degree in the ambient
`pipeGraph`, since the neighbor sets correspond bijectively via `Subtype.val`. -/
theorem degree_pipeSub (u : pipeSites B L) :
    (pipeSub B L).degree u = (pipeGraph B L false).degree u.1 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree,
    neighborFinset_pipeSub_image u,
    Finset.card_image_of_injective _ Subtype.val_injective]

/-- The averaging walk operator on `pipeSub` agrees with the one on the ambient `pipeGraph`,
combining `sum_neighborFinset_pipeSub` and `degree_pipeSub`. -/
theorem walkOp_pipeSub (f : (List (Fin B) × ℕ) → ℝ) (u : pipeSites B L) :
    RWRS.walkOp (pipeSub B L) (fun y => f y.1) u = RWRS.walkOp (pipeGraph B L false) f u.1 := by
  rw [RWRS.walkOp, RWRS.walkOp, sum_neighborFinset_pipeSub, degree_pipeSub]

/-- The root of the tree of pipes, as a site. -/
def pipeRootSub (B : ℕ) (L : ℕ → ℕ) : pipeSites B L := ⟨pipeRoot B, Or.inl rfl⟩

/-! ### The killed Green function of the tree of pipes -/

/-- The killed heat kernel on the induced graph `pipeSub`, killed on the preimage of `C`,
equals the ambient killed heat kernel killed on `C`, by induction on the time step using
`walkOp_pipeSub`. -/
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

/-- The killed Green's function transfers from `pipeSub` to the ambient graph the same way
as the heat kernel, summing `killedHeat_pipeSub` over time and dividing by the shared
degree. -/
theorem killedGreen_pipeSub (C : Set (List (Fin B) × ℕ)) (u v : pipeSites B L) :
    RWRS.killedGreen (pipeSub B L) (Subtype.val ⁻¹' C) u v
      = RWRS.killedGreen (pipeGraph B L false) C u.1 v.1 := by
  rw [RWRS.killedGreen, RWRS.killedGreen, degree_pipeSub]
  congr 1
  exact tsum_congr fun k => by rw [killedHeat_pipeSub C k u v]

/-- The real-valued killed Green's function on `pipeSub` agrees with the ambient one, taking
`ENNReal.toReal` of `killedGreen_pipeSub`. -/
theorem killedGreenReal_pipeSub (C : Set (List (Fin B) × ℕ)) (u v : pipeSites B L) :
    RWRS.killedGreenReal (pipeSub B L) (Subtype.val ⁻¹' C) u v
      = RWRS.killedGreenReal (pipeGraph B L false) C u.1 v.1 := by
  rw [RWRS.killedGreenReal, RWRS.killedGreenReal, killedGreen_pipeSub]


/-! ### Connectivity, infinitude and the degree bound -/

/-- Every site of `pipeDepth` at most `n` is reachable from `pipeRootSub` in the tree of
pipes, by induction on `n` walking back one step at a time via `pipePred`. -/
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

/-- The tree of pipes `pipeSub` is connected: every site reaches the root by
`reachable_pipeRootSub`, hence any two sites reach each other. -/
theorem pipeSub_connected (hL : ∀ j, 1 ≤ j → 1 ≤ L j) : (pipeSub B L).Connected := by
  haveI : Nonempty (pipeSites B L) := ⟨pipeRootSub B L⟩
  refine SimpleGraph.Connected.mk ?_
  intro u v
  exact ((reachable_pipeRootSub hL _ u le_rfl).symm).trans
    (reachable_pipeRootSub hL _ v le_rfl)


/-- The site set `pipeSites B L` is infinite whenever `B ≥ 1`: the map sending a word `w` to
`(w, 0)` is an injection from the infinite type of words. -/
theorem pipeSites_infinite (hB : 1 ≤ B) : Infinite (pipeSites B L) := by
  haveI : Nonempty (Fin B) := ⟨⟨0, hB⟩⟩
  refine Infinite.of_injective
    (fun w : List (Fin B) => (⟨(w, 0), Or.inl rfl⟩ : pipeSites B L)) ?_
  intro a b h
  have h1 : ((a, 0) : List (Fin B) × ℕ) = (b, 0) := congrArg Subtype.val h
  exact (Prod.mk.injEq _ _ _ _ ▸ h1).1

open scoped Classical in
/-- Every vertex of the ambient `pipeGraph` has degree at most `2 * B + 3`, since its
neighbors all lie in the explicit list `pipeNbrList` of that length. -/
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
/-- The degree of a vertex in an induced subgraph is at most its degree in the ambient
locally finite graph `H`, since the induced neighbor set injects into the ambient one. -/
theorem degree_induce_le {W : Type*} (H : SimpleGraph W) [H.LocallyFinite] (S : Set W)
    (u : S) [Fintype ((H.induce S).neighborSet u)] :
    (H.induce S).degree u ≤ H.degree u.1 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree]
  refine Finset.card_le_card_of_injOn (fun y => (y : W)) ?_ (fun a _ b _ h => Subtype.ext h)
  intro y hy
  rw [Finset.mem_coe, SimpleGraph.mem_neighborFinset] at hy
  exact (SimpleGraph.mem_neighborFinset _ _ _).2 hy

open scoped Classical in
/-- The tree of pipes has bounded degree `2 * B + 3`: transferring to the ambient graph via
`degree_pipeSub` reduces this to the same neighbor-list bound as `degree_pipeGraph_le`. -/
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
