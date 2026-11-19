import RWRS.Support.RootedBallRestriction

/-!
# Projection of rooted ball isomorphisms

An isomorphism of rooted balls restricts to each smaller radius, and these
restrictions form an inverse system.
-/

namespace RWRS.Support

/-- Restrict a rooted ball isomorphism to a smaller radius. -/
def RootedBallIso.restrict {m : ℕ} {N N' : Net m} {r s : ℕ}
    (φ : RootedBallIso N N' r) (hs : s ≤ r) : RootedBallIso N N' s := by
  let lift : netBallSet N s → netBallSet N r :=
    fun x => ⟨x, netBallSet_mono N hs x.property⟩
  let lift' : netBallSet N' s → netBallSet N' r :=
    fun x => ⟨x, netBallSet_mono N' hs x.property⟩
  let f : netBallSet N s → netBallSet N' s :=
    fun x => ⟨φ.1 (lift x), φ.mem_ball_image s hs (lift x) x.property⟩
  let g : netBallSet N' s → netBallSet N s :=
    fun y => ⟨φ.symm.1 (lift' y), φ.symm.mem_ball_image s hs (lift' y) y.property⟩
  have hleft : Function.LeftInverse g f := by
    intro x
    apply Subtype.ext
    change ((φ.1.symm (lift' (f x))) : ℕ) = (x : ℕ)
    have hlift : lift' (f x) = φ.1 (lift x) := Subtype.ext rfl
    rw [hlift, Equiv.symm_apply_apply]
  have hright : Function.RightInverse g f := by
    intro y
    apply Subtype.ext
    change ((φ.1 (lift (g y))) : ℕ) = (y : ℕ)
    have hlift : lift (g y) = φ.1.symm (lift' y) := Subtype.ext rfl
    rw [hlift, Equiv.apply_symm_apply]
  let E : netBallSet N s ≃ netBallSet N' s := ⟨f, g, hleft, hright⟩
  refine ⟨E, ?_, ?_⟩
  · exact φ.2.1
  · intro x y
    exact φ.2.2 (lift x) (lift y)

/-- Restricting to the same radius leaves a rooted ball isomorphism unchanged. -/
theorem RootedBallIso.restrict_refl {m : ℕ} {N N' : Net m} {r : ℕ}
    (φ : RootedBallIso N N' r) : φ.restrict (le_refl r) = φ := by
  apply Subtype.ext
  apply Equiv.ext
  intro x
  apply Subtype.ext
  rfl

/-- Restriction to two successively smaller radii agrees with direct restriction. -/
theorem RootedBallIso.restrict_restrict {m : ℕ} {N N' : Net m} {r s t : ℕ}
    (φ : RootedBallIso N N' r) (hst : t ≤ s) (hsr : s ≤ r) :
    (φ.restrict hsr).restrict hst = φ.restrict (hst.trans hsr) := by
  apply Subtype.ext
  apply Equiv.ext
  intro x
  apply Subtype.ext
  rfl

end RWRS.Support
