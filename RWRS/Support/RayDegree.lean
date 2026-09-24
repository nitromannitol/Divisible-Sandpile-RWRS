import RWRS.Support.RayBuild

namespace RWRS.Support

open scoped Classical

variable {B : ℕ} {L : ℕ → ℕ} {m s : ℕ → ℕ}

theorem degree_gadget_le (M : ℕ) (v : gadgetSites B L M) :
    (gadgetGraph B L M).degree v ≤ 2 * B + 3 := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have hstep : ((gadgetGraph B L M).neighborFinset v).card
      ≤ ((pipeGraph B L false).neighborFinset (v : List (Fin B) × ℕ)).card := by
    refine Finset.card_le_card_of_injOn (fun y => (y : List (Fin B) × ℕ)) ?_
      (fun a _ b _ h => Subtype.ext h)
    intro y hy
    rw [Finset.mem_coe, SimpleGraph.mem_neighborFinset] at hy
    exact (SimpleGraph.mem_neighborFinset _ _ _).2 hy
  rw [SimpleGraph.card_neighborFinset_eq_degree] at hstep
  exact le_trans hstep (degree_pipeGraph_le false (v : List (Fin B) × ℕ))

/-- The gadgets attached at the ray vertex `i`; there is at most one. -/
noncomputable def gadgetAt (s : ℕ → ℕ) (i : ℕ) : Finset ℕ :=
  (Finset.range (i + 1)).filter fun k => s k = i

theorem card_gadgetAt_le (hs : StrictMono s) (i : ℕ) : (gadgetAt s i).card ≤ 1 := by
  refine Finset.card_le_one.2 fun a ha b hb => ?_
  rw [gadgetAt, Finset.mem_filter] at ha hb
  exact hs.injective (ha.2.trans hb.2.symm)

/-- A finite superset of the neighbours of a ray vertex. -/
noncomputable def rayNbrInl (B : ℕ) (L : ℕ → ℕ) (m s : ℕ → ℕ) (i : ℕ) :
    Finset (RayV B L m) :=
  insert (Sum.inl (i + 1)) (insert (Sum.inl (i - 1))
    ((gadgetAt s i).biUnion fun k =>
      ((gadgetGraph B L (m k)).neighborFinset (gadgetRoot B L (m k))).image
        (rayEmb B L m s k)))

theorem nbr_inl_subset' (hs : StrictMono s) (i : ℕ) :
    (rayGraph B L m s).neighborSet (Sum.inl i) ⊆ ↑(rayNbrInl B L m s i) := by
  rintro y (⟨j, h1, h2⟩ | ⟨j, h1, h2⟩ | ⟨k, v, w, hvw, h1, h2⟩)
  · have hj : i = j := Sum.inl.inj h1
    subst hj
    simp [rayNbrInl, h2, rayPt]
  · have hj : i = j + 1 := Sum.inl.inj h2
    subst hj
    simp [rayNbrInl, h1, rayPt]
  · by_cases hv : v = gadgetRoot B L (m k)
    · subst hv
      rw [rayEmb_root] at h1
      have hk : i = s k := Sum.inl.inj h1
      have hle : k ≤ i := by
        have := hs.le_apply (x := k)
        omega
      refine Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ?_))
      refine Finset.mem_biUnion.2 ⟨k, ?_, ?_⟩
      · rw [gadgetAt, Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, hk.symm⟩
      · exact Finset.mem_image.2 ⟨w, (SimpleGraph.mem_neighborFinset _ _ _).2 hvw, h2.symm⟩
    · rw [rayEmb_of_ne hv] at h1
      exact absurd h1 Sum.inl_ne_inr

theorem degree_le_of_subset {W : Type*} {H : SimpleGraph W} (inst : H.LocallyFinite)
    (x : W) (F : Finset W) (hsub : ∀ y, H.Adj x y → y ∈ F) (n : ℕ) (hn : F.card ≤ n) :
    @SimpleGraph.degree _ H x (inst x) ≤ n := by
  have h1 : @SimpleGraph.neighborFinset _ H x (inst x) ⊆ F := by
    intro y hy
    exact hsub y ((@SimpleGraph.mem_neighborFinset _ H x (inst x) y).1 hy)
  calc @SimpleGraph.degree _ H x (inst x)
      = (@SimpleGraph.neighborFinset _ H x (inst x)).card :=
        (@SimpleGraph.card_neighborFinset_eq_degree _ H x (inst x)).symm
    _ ≤ F.card := Finset.card_le_card h1
    _ ≤ n := hn

theorem card_rayNbrInl_le (hs : StrictMono s) (i : ℕ) :
    (rayNbrInl B L m s i).card ≤ 2 * B + 5 := by
  have hins1 := Finset.card_insert_le (Sum.inl (i + 1) : RayV B L m)
    (insert (Sum.inl (i - 1) : RayV B L m)
      ((gadgetAt s i).biUnion fun k =>
        ((gadgetGraph B L (m k)).neighborFinset (gadgetRoot B L (m k))).image
          (rayEmb B L m s k)))
  have hins2 := Finset.card_insert_le (Sum.inl (i - 1) : RayV B L m)
    ((gadgetAt s i).biUnion fun k =>
      ((gadgetGraph B L (m k)).neighborFinset (gadgetRoot B L (m k))).image
        (rayEmb B L m s k))
  have hbi : ((gadgetAt s i).biUnion fun k =>
      ((gadgetGraph B L (m k)).neighborFinset (gadgetRoot B L (m k))).image
        (rayEmb B L m s k)).card ≤ 2 * B + 3 := by
    refine le_trans Finset.card_biUnion_le ?_
    have hterm : ∀ k ∈ gadgetAt s i,
        (((gadgetGraph B L (m k)).neighborFinset (gadgetRoot B L (m k))).image
          (rayEmb B L m s k)).card ≤ 2 * B + 3 := by
      intro k _
      refine le_trans Finset.card_image_le ?_
      rw [SimpleGraph.card_neighborFinset_eq_degree]
      exact degree_gadget_le (m k) (gadgetRoot B L (m k))
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_const, smul_eq_mul]
    exact le_trans (Nat.mul_le_mul_right _ (card_gadgetAt_le hs i)) (by omega)
  rw [rayNbrInl]
  omega

theorem boundedDegree_rayGraph (hs : StrictMono s) :
    ∀ x : RayV B L m,
      @SimpleGraph.degree _ (rayGraph B L m s) x (rayLocallyFinite hs x) ≤ 2 * B + 5 := by
  rintro (i | ⟨k, ⟨v, hv⟩⟩)
  · refine degree_le_of_subset _ _ (rayNbrInl B L m s i) (fun y hy => ?_) _
      (card_rayNbrInl_le hs i)
    exact Finset.mem_coe.1 (nbr_inl_subset' hs i hy)
  · refine degree_le_of_subset _ _
      (((gadgetGraph B L (m k)).neighborFinset v).image (rayEmb B L m s k))
      (fun y hy => ?_) _ ?_
    · obtain ⟨w, hw, rfl⟩ := nbr_inr_subset (s := s) k v hv hy
      exact Finset.mem_image.2 ⟨w, (SimpleGraph.mem_neighborFinset _ _ _).2 hw, rfl⟩
    · refine le_trans Finset.card_image_le ?_
      rw [SimpleGraph.card_neighborFinset_eq_degree]
      exact le_trans (degree_gadget_le (m k) v) (by omega)

end RWRS.Support
