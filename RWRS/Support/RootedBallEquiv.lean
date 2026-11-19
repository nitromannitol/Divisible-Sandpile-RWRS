import RWRS.Support.RootedBallCommon

/-!
# Isomorphisms of finite rooted balls

A common finite code yields a root-preserving adjacency isomorphism of the
corresponding balls.
-/

namespace RWRS.Support

/-- The root lies in every rooted ball. -/
theorem netRoot_mem_netBallSet {m : ℕ} (N : Net m) (r : ℕ) :
    netRoot N ∈ netBallSet N r :=
  netBallSet_mono N (Nat.zero_le r) (show netRoot N ∈ netBallSet N 0 from rfl)

/-- A common finite code gives a root-preserving adjacency equivalence of balls. -/
theorem exists_ballEquiv_of_netBallMatches {m : ℕ} {N N' : Net m}
    {r : ℕ} {c : RootedFiniteGraph}
    (h : NetBallMatches N r c) (h' : NetBallMatches N' r c) :
    ∃ φ : netBallSet N r ≃ netBallSet N' r,
      (φ ⟨netRoot N, netRoot_mem_netBallSet N r⟩ : ℕ) = netRoot N' ∧
      ∀ x y : netBallSet N r,
        (netGraph N).Adj x y ↔ (netGraph N').Adj (φ x) (φ y) := by
  classical
  obtain ⟨e, he, heroot, heball, headj⟩ := h
  obtain ⟨e', he', he'root, he'ball, he'adj⟩ := h'
  let f : Fin c.1 → netBallSet N r := fun i => ⟨e i, (heball (e i)).2 ⟨i, rfl⟩⟩
  let f' : Fin c.1 → netBallSet N' r := fun i => ⟨e' i, (he'ball (e' i)).2 ⟨i, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j hij
      exact he (congrArg Subtype.val hij)
    · intro x
      obtain ⟨i, hi⟩ := (heball x).1 x.property
      exact ⟨i, Subtype.ext hi⟩
  have hf' : Function.Bijective f' := by
    constructor
    · intro i j hij
      exact he' (congrArg Subtype.val hij)
    · intro x
      obtain ⟨i, hi⟩ := (he'ball x).1 x.property
      exact ⟨i, Subtype.ext hi⟩
  let E := Equiv.ofBijective f hf
  let E' := Equiv.ofBijective f' hf'
  refine ⟨E.symm.trans E', ?_, ?_⟩
  · have hroot : f c.2.1 = ⟨netRoot N, netRoot_mem_netBallSet N r⟩ :=
      Subtype.ext heroot.symm
    change (E' (E.symm ⟨netRoot N, netRoot_mem_netBallSet N r⟩) : ℕ) = netRoot N'
    rw [← hroot]
    change (E' (E.symm (E c.2.1)) : ℕ) = netRoot N'
    rw [Equiv.symm_apply_apply]
    exact he'root.symm
  · intro x y
    have hx : e (E.symm x) = x := congrArg Subtype.val (E.apply_symm_apply x)
    have hy : e (E.symm y) = y := congrArg Subtype.val (E.apply_symm_apply y)
    change (netGraph N).Adj x y ↔
      (netGraph N').Adj (E' (E.symm x)) (E' (E.symm y))
    calc
      (netGraph N).Adj x y ↔ c.2.2 (E.symm x) (E.symm y) = true := by
        simpa only [hx, hy] using headj (E.symm x) (E.symm y)
      _ ↔ (netGraph N').Adj (E' (E.symm x)) (E' (E.symm y)) :=
        (he'adj (E.symm x) (E.symm y)).symm

/-- Equal canonical types give a root-preserving adjacency equivalence of balls. -/
theorem exists_ballEquiv_of_netBallType_eq {m : ℕ} {N N' : Net m} {r : ℕ}
    (h : netBallType N r = netBallType N' r) :
    ∃ φ : netBallSet N r ≃ netBallSet N' r,
      (φ ⟨netRoot N, netRoot_mem_netBallSet N r⟩ : ℕ) = netRoot N' ∧
      ∀ x y : netBallSet N r,
        (netGraph N).Adj x y ↔ (netGraph N').Adj (φ x) (φ y) := by
  obtain ⟨c, hc, hc'⟩ := exists_common_netBallMatches_of_netBallType_eq h
  exact exists_ballEquiv_of_netBallMatches hc hc'

end RWRS.Support
