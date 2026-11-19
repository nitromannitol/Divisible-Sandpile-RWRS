import RWRS.Support.RootedBallCompatible

/-!
# Rooted graph isomorphism from compatible balls

Compatible rooted-ball isomorphisms on connected networks assemble into an
isomorphism of their full graphs.
-/

namespace RWRS.Support

/-- A radius whose rooted ball contains the given vertex. -/
noncomputable def netBallRadius {m : ℕ} {N : Net m} (hN : NetGood N) (x : ℕ) : ℕ :=
  Classical.choose (exists_mem_netBallSet hN x)

/-- The radius chosen by `netBallRadius` contains the vertex. -/
theorem mem_netBallSet_netBallRadius {m : ℕ} {N : Net m} (hN : NetGood N) (x : ℕ) :
    x ∈ netBallSet N (netBallRadius hN x) :=
  Classical.choose_spec (exists_mem_netBallSet hN x)

/-- The vertex map obtained from a family of rooted ball isomorphisms. -/
noncomputable def rootedBallIsoLimit {m : ℕ} {N N' : Net m} (hN : NetGood N)
    (f : ∀ r, RootedBallIso N N' r) (x : ℕ) : ℕ :=
  (f (netBallRadius hN x)).1 ⟨x, mem_netBallSet_netBallRadius hN x⟩

/-- Compatible ball isomorphisms agree on every vertex in a smaller ball. -/
theorem rootedBallIso_coe_eq {m : ℕ} {N N' : Net m}
    (f : ∀ r, RootedBallIso N N' r)
    (hf : ∀ ⦃i j⦄ (hij : i ≤ j), (f j).restrict hij = f i)
    {i j : ℕ} (hij : i ≤ j) (x : netBallSet N i) :
    ((f j).1 ⟨x, netBallSet_mono N hij x.property⟩ : ℕ) = ((f i).1 x : ℕ) := by
  have h := congrArg (fun φ : RootedBallIso N N' i => (φ.1 x : ℕ)) (hf hij)
  exact h

/-- The limit map agrees with any ball isomorphism whose ball contains the vertex. -/
theorem rootedBallIsoLimit_eq_at {m : ℕ} {N N' : Net m} (hN : NetGood N)
    (f : ∀ r, RootedBallIso N N' r)
    (hf : ∀ ⦃i j⦄ (hij : i ≤ j), (f j).restrict hij = f i)
    (r x : ℕ) (hx : x ∈ netBallSet N r) :
    rootedBallIsoLimit hN f x = ((f r).1 ⟨x, hx⟩ : ℕ) := by
  let r₀ := netBallRadius hN x
  have h₀ : x ∈ netBallSet N r₀ := mem_netBallSet_netBallRadius hN x
  have h₁ := rootedBallIso_coe_eq f hf (Nat.le_max_left r₀ r) ⟨x, h₀⟩
  have h₂ := rootedBallIso_coe_eq f hf (Nat.le_max_right r₀ r) ⟨x, hx⟩
  exact h₁.symm.trans h₂

/-- A compatible family on connected networks gives a rooted graph isomorphism. -/
theorem netIso_of_compatible_rootedBallIso {N N' : Net 0}
    (hN : NetGood N) (hN' : NetGood N') (f : ∀ r, RootedBallIso N N' r)
    (hf : ∀ ⦃i j⦄ (hij : i ≤ j), (f j).restrict hij = f i) : NetIso N N' := by
  let F : ℕ → ℕ := rootedBallIsoLimit hN f
  have hFinj : Function.Injective F := by
    intro x y hxy
    let rx := netBallRadius hN x
    let ry := netBallRadius hN y
    let r := max rx ry
    have hx : x ∈ netBallSet N r :=
      netBallSet_mono N (Nat.le_max_left rx ry) (mem_netBallSet_netBallRadius hN x)
    have hy : y ∈ netBallSet N r :=
      netBallSet_mono N (Nat.le_max_right rx ry) (mem_netBallSet_netBallRadius hN y)
    have heq : (f r).1 ⟨x, hx⟩ = (f r).1 ⟨y, hy⟩ := by
      apply Subtype.ext
      calc
        ((f r).1 ⟨x, hx⟩ : ℕ) = F x := (rootedBallIsoLimit_eq_at hN f hf r x hx).symm
        _ = F y := hxy
        _ = ((f r).1 ⟨y, hy⟩ : ℕ) := rootedBallIsoLimit_eq_at hN f hf r y hy
    exact congrArg Subtype.val ((f r).1.injective heq)
  have hFsurj : Function.Surjective F := by
    intro y
    obtain ⟨r, hr⟩ := exists_mem_netBallSet hN' y
    obtain ⟨x, hx⟩ := (f r).1.surjective ⟨y, hr⟩
    refine ⟨x, ?_⟩
    calc
      F x = ((f r).1 x : ℕ) := rootedBallIsoLimit_eq_at hN f hf r x x.property
      _ = y := congrArg Subtype.val hx
  let φ : ℕ ≃ ℕ := Equiv.ofBijective F ⟨hFinj, hFsurj⟩
  refine ⟨φ, ?_, ?_, ?_⟩
  · intro x y
    obtain ⟨rx, hx⟩ := exists_mem_netBallSet hN x
    obtain ⟨ry, hy⟩ := exists_mem_netBallSet hN y
    let r := max rx ry
    have hx' : x ∈ netBallSet N r := netBallSet_mono N (Nat.le_max_left rx ry) hx
    have hy' : y ∈ netBallSet N r := netBallSet_mono N (Nat.le_max_right rx ry) hy
    have heq := (f r).2.2 ⟨x, hx'⟩ ⟨y, hy'⟩
    rw [← rootedBallIsoLimit_eq_at hN f hf r x hx',
      ← rootedBallIsoLimit_eq_at hN f hf r y hy'] at heq
    exact heq
  · calc
      φ (netRoot N) = ((f 0).1 ⟨netRoot N, netRoot_mem_netBallSet N 0⟩ : ℕ) :=
        rootedBallIsoLimit_eq_at hN f hf 0 (netRoot N) (netRoot_mem_netBallSet N 0)
      _ = netRoot N' := (f 0).2.1
  · intro i
    exact Subsingleton.elim _ _

/-- Connected rooted graphs with identical ball-type sequences are isomorphic. -/
theorem netIso_of_netBallTypes_eq {N N' : Net 0} (hN : NetGood N) (hN' : NetGood N')
    (h : netBallTypes N = netBallTypes N') : NetIso N N' := by
  have hr : ∀ r, netBallType N r = netBallType N' r := fun r => congrFun h r
  obtain ⟨f, hf⟩ := exists_compatible_rootedBallIso hr
  exact netIso_of_compatible_rootedBallIso hN hN' f hf

end RWRS.Support
