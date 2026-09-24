/-
The ray with the tree-of-pipes gadgets attached, the graph of
`sec:recurrent-nonstab`.  A vertex is either a position on the ray or a non-root
site of one of the gadgets; the root of the `k`-th gadget is the ray vertex
`r_{s_k}` itself.  What is proved here is that this graph satisfies the
`RWRS.RayGadget` predicate the estimates of that section are stated for, that it
is connected and infinite, and that it is locally finite, the gadgets attached
at a given ray vertex being at most one because the attachment points are
strictly increasing.
-/
import RWRS.Support.PipeSub

namespace RWRS.Support

open scoped Classical

/-- The subgraph induced on a set of vertices of a locally finite graph is
locally finite. -/
@[reducible] noncomputable def induceLocallyFinite {V : Type*} (G : SimpleGraph V) [G.LocallyFinite]
    (S : Set V) : (G.induce S).LocallyFinite := by
  intro u
  have hfin : (Subtype.val ⁻¹' (G.neighborSet u.1) : Set S).Finite :=
    Set.Finite.preimage Subtype.val_injective.injOn (Set.toFinite _)
  exact Set.Finite.fintype hfin

variable {B : ℕ} {L : ℕ → ℕ}

noncomputable instance gadgetLocallyFinite (m : ℕ) :
    (gadgetGraph B L m).LocallyFinite :=
  induceLocallyFinite _ _

/-- The vertices of the ray with the gadgets attached: the ray positions, and
the non-root sites of each gadget. -/
abbrev RayV (B : ℕ) (L : ℕ → ℕ) (m : ℕ → ℕ) : Type :=
  ℕ ⊕ (Σ k : ℕ, {v : gadgetSites B L (m k) // v ≠ gadgetRoot B L (m k)})

/-- The embedding of the `k`-th gadget: its root goes to the ray vertex it is
attached to, every other site to its own copy. -/
noncomputable def rayEmb (B : ℕ) (L : ℕ → ℕ) (m s : ℕ → ℕ) (k : ℕ)
    (v : gadgetSites B L (m k)) : RayV B L m :=
  if h : v = gadgetRoot B L (m k) then Sum.inl (s k) else Sum.inr ⟨k, ⟨v, h⟩⟩

/-- The ray. -/
def rayPt (B : ℕ) (L : ℕ → ℕ) (m : ℕ → ℕ) (i : ℕ) : RayV B L m := Sum.inl i

/-- The ray with the gadgets attached. -/
noncomputable def rayGraph (B : ℕ) (L : ℕ → ℕ) (m s : ℕ → ℕ) : SimpleGraph (RayV B L m) where
  Adj x y :=
    (∃ i, x = rayPt B L m i ∧ y = rayPt B L m (i + 1)) ∨
    (∃ i, y = rayPt B L m i ∧ x = rayPt B L m (i + 1)) ∨
    (∃ (k : ℕ) (v w : gadgetSites B L (m k)),
      (gadgetGraph B L (m k)).Adj v w ∧ x = rayEmb B L m s k v ∧ y = rayEmb B L m s k w)
  symm := ⟨by
    rintro x y (⟨i, h1, h2⟩ | ⟨i, h1, h2⟩ | ⟨k, v, w, hvw, h1, h2⟩)
    · exact Or.inr (Or.inl ⟨i, h1, h2⟩)
    · exact Or.inl ⟨i, h1, h2⟩
    · exact Or.inr (Or.inr ⟨k, w, v, hvw.symm, h2, h1⟩)⟩
  loopless := ⟨by
    rintro x (⟨i, h1, h2⟩ | ⟨i, h1, h2⟩ | ⟨k, v, w, hvw, h1, h2⟩)
    · rw [h1] at h2
      exact absurd (Sum.inl.inj h2) (by omega)
    · rw [h1] at h2
      exact absurd (Sum.inl.inj h2).symm (by omega)
    · have hne : v ≠ w := hvw.ne
      rw [h1] at h2
      by_cases hv : v = gadgetRoot B L (m k) <;> by_cases hw : w = gadgetRoot B L (m k)
      · exact hne (hv.trans hw.symm)
      · simp only [rayEmb, dif_pos hv, dif_neg hw] at h2
        exact Sum.inl_ne_inr h2
      · simp only [rayEmb, dif_neg hv, dif_pos hw] at h2
        exact Sum.inr_ne_inl h2
      · simp only [rayEmb, dif_neg hv, dif_neg hw, Sum.inr.injEq, Sigma.mk.injEq,
          heq_eq_eq, Subtype.mk.injEq, true_and] at h2
        exact hne h2⟩

variable {m s : ℕ → ℕ}

theorem rayEmb_root (k : ℕ) :
    rayEmb B L m s k (gadgetRoot B L (m k)) = rayPt B L m (s k) := dif_pos rfl

theorem rayEmb_of_ne {k : ℕ} {v : gadgetSites B L (m k)} (hv : v ≠ gadgetRoot B L (m k)) :
    rayEmb B L m s k v = Sum.inr ⟨k, ⟨v, hv⟩⟩ := dif_neg hv

theorem rayEmb_injective (k : ℕ) : Function.Injective (rayEmb B L m s k) := by
  intro v w h
  by_cases hv : v = gadgetRoot B L (m k) <;> by_cases hw : w = gadgetRoot B L (m k)
  · exact hv.trans hw.symm
  · rw [rayEmb, dif_pos hv, rayEmb, dif_neg hw] at h
    exact absurd h (Sum.inl_ne_inr)
  · rw [rayEmb, dif_neg hv, rayEmb, dif_pos hw] at h
    exact absurd h (Sum.inr_ne_inl)
  · rw [rayEmb, dif_neg hv, rayEmb, dif_neg hw] at h
    simp only [Sum.inr.injEq, Sigma.mk.injEq, heq_eq_eq, Subtype.mk.injEq, true_and] at h
    exact h

/-- **The ray with the gadgets attached is the graph of `sec:recurrent-nonstab`.** -/
theorem rayGadget_rayGraph :
    RayGadget (rayGraph B L m s) (rayPt B L m 0) B L m s (rayPt B L m) (rayEmb B L m s) where
  rayRoot := rfl
  rayInj := fun i j h => Sum.inl.inj h
  embInj := rayEmb_injective
  attach := rayEmb_root
  meetsRay := by
    rintro k v ⟨i, hi⟩
    by_contra hv
    rw [rayEmb_of_ne hv] at hi
    exact Sum.inl_ne_inr hi
  disjoint := by
    intro k l v w hkl h
    by_cases hv : v = gadgetRoot B L (m k) <;> by_cases hw : w = gadgetRoot B L (m l)
    · exact ⟨hv, hw⟩
    · rw [rayEmb, dif_pos hv, rayEmb, dif_neg hw] at h
      exact absurd h Sum.inl_ne_inr
    · rw [rayEmb, dif_neg hv, rayEmb, dif_pos hw] at h
      exact absurd h Sum.inr_ne_inl
    · rw [rayEmb, dif_neg hv, rayEmb, dif_neg hw] at h
      simp only [Sum.inr.injEq, Sigma.mk.injEq] at h
      exact absurd h.1 hkl
  adj := fun _ _ => Iff.rfl
  cover := by
    rintro (i | ⟨k, ⟨v, hv⟩⟩)
    · exact Or.inl ⟨i, rfl⟩
    · exact Or.inr ⟨k, v, (rayEmb_of_ne hv).symm⟩

/-- The `k`-th gadget maps into the ray graph. -/
noncomputable def rayEmbHom (k : ℕ) : gadgetGraph B L (m k) →g rayGraph B L m s where
  toFun := rayEmb B L m s k
  map_rel' := fun {v w} h => Or.inr (Or.inr ⟨k, v, w, h, rfl, rfl⟩)

theorem rayGraph_adj_ray (i : ℕ) :
    (rayGraph B L m s).Adj (rayPt B L m i) (rayPt B L m (i + 1)) := Or.inl ⟨i, rfl, rfl⟩

theorem reachable_rayPt_zero (i : ℕ) :
    (rayGraph B L m s).Reachable (rayPt B L m i) (rayPt B L m 0) := by
  induction i with
  | zero => exact SimpleGraph.Reachable.refl _
  | succ i ih => exact ((rayGraph_adj_ray (s := s) i).symm.reachable).trans ih

theorem reachable_rayEmb_zero (hL : ∀ j, 1 ≤ j → 1 ≤ L j) (k : ℕ)
    (v : gadgetSites B L (m k)) :
    (rayGraph B L m s).Reachable (rayEmb B L m s k v) (rayPt B L m 0) := by
  obtain ⟨p, -⟩ := exists_walk_le_depth hL (pipeDepth L (v : List (Fin B) × ℕ)) v le_rfl
  have hreach : (rayGraph B L m s).Reachable (rayEmb B L m s k (gadgetRoot B L (m k)))
      (rayEmb B L m s k v) := ⟨p.map (rayEmbHom (s := s) k)⟩
  rw [rayEmb_root] at hreach
  exact hreach.symm.trans (reachable_rayPt_zero (s := s) (s k))

theorem rayGraph_connected (hL : ∀ j, 1 ≤ j → 1 ≤ L j) :
    (rayGraph B L m s).Connected := by
  haveI : Nonempty (RayV B L m) := ⟨rayPt B L m 0⟩
  refine SimpleGraph.Connected.mk ?_
  have hall : ∀ x : RayV B L m, (rayGraph B L m s).Reachable x (rayPt B L m 0) := by
    rintro (i | ⟨k, ⟨v, hv⟩⟩)
    · exact reachable_rayPt_zero (s := s) i
    · rw [show (Sum.inr ⟨k, ⟨v, hv⟩⟩ : RayV B L m) = rayEmb B L m s k v from
        (rayEmb_of_ne hv).symm]
      exact reachable_rayEmb_zero hL k v
  exact fun x y => (hall x).trans (hall y).symm

theorem infinite_rayV : Infinite (RayV B L m) :=
  Infinite.of_injective (fun i : ℕ => (Sum.inl i : RayV B L m)) fun _ _ h => Sum.inl.inj h

/-! ### The ray graph is locally finite -/

theorem nbr_inl_subset (hs : StrictMono s) (i : ℕ) :
    (rayGraph B L m s).neighborSet (Sum.inl i) ⊆
      ({Sum.inl (i + 1), Sum.inl (i - 1)} : Set (RayV B L m)) ∪
      ⋃ k ∈ Set.Iic i,
        (rayEmb B L m s k) ''
          ((gadgetGraph B L (m k)).neighborSet (gadgetRoot B L (m k))) := by
  rintro y (⟨j, h1, h2⟩ | ⟨j, h1, h2⟩ | ⟨k, v, w, hvw, h1, h2⟩)
  · have hj : i = j := Sum.inl.inj h1
    subst hj
    exact Or.inl (by simp [h2, rayPt])
  · have hj : i = j + 1 := Sum.inl.inj h2
    subst hj
    refine Or.inl ?_
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, h1, rayPt]
    right
    simp
  · by_cases hv : v = gadgetRoot B L (m k)
    · subst hv
      rw [rayEmb_root] at h1
      have hk : i = s k := Sum.inl.inj h1
      refine Or.inr ?_
      refine Set.mem_biUnion (show k ∈ Set.Iic i from ?_) ⟨w, hvw, h2.symm⟩
      have := hs.le_apply (x := k)
      simp only [Set.mem_Iic, hk]
      omega
    · rw [rayEmb_of_ne hv] at h1
      exact absurd h1 Sum.inl_ne_inr

theorem nbr_inr_subset (k : ℕ) (v : gadgetSites B L (m k))
    (hv : v ≠ gadgetRoot B L (m k)) :
    (rayGraph B L m s).neighborSet (Sum.inr ⟨k, ⟨v, hv⟩⟩) ⊆
      (rayEmb B L m s k) '' ((gadgetGraph B L (m k)).neighborSet v) := by
  rintro y (⟨j, h1, h2⟩ | ⟨j, h1, h2⟩ | ⟨k', v', w, hvw, h1, h2⟩)
  · exact absurd h1 Sum.inr_ne_inl
  · exact absurd h2 Sum.inr_ne_inl
  · by_cases hv' : v' = gadgetRoot B L (m k')
    · rw [hv', rayEmb_root] at h1
      exact absurd h1 Sum.inr_ne_inl
    · rw [rayEmb_of_ne hv'] at h1
      simp only [Sum.inr.injEq, Sigma.mk.injEq] at h1
      obtain ⟨hk, hvv⟩ := h1
      subst hk
      have : v = v' := by
        have h3 := eq_of_heq hvv
        exact congrArg Subtype.val h3
      subst this
      exact ⟨w, hvw, h2.symm⟩

@[reducible] noncomputable def rayLocallyFinite (hs : StrictMono s) :
    (rayGraph B L m s).LocallyFinite := by
  rintro (i | ⟨k, ⟨v, hv⟩⟩)
  · refine Set.Finite.fintype (Set.Finite.subset ?_ (nbr_inl_subset hs i))
    refine Set.Finite.union (Set.toFinite _) ?_
    exact Set.Finite.biUnion (Set.finite_Iic i)
      (fun k _ => Set.Finite.image _ (Set.toFinite _))
  · exact Set.Finite.fintype (Set.Finite.subset
      (Set.Finite.image _ (Set.toFinite _)) (nbr_inr_subset k v hv))

end RWRS.Support
