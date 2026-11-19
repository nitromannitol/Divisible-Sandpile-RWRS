import RWRS.Support.RootedBallEquiv
import Mathlib.Data.Finite.Prod

/-!
# Restrictions of rooted ball isomorphisms

A root-preserving adjacency equivalence of two balls carries each smaller
concentric ball onto the corresponding ball.
-/

namespace RWRS.Support

/-- A root-preserving adjacency equivalence between two finite rooted balls. -/
def RootedBallIso {m : ℕ} (N N' : Net m) (r : ℕ) :=
  {φ : netBallSet N r ≃ netBallSet N' r //
    (φ ⟨netRoot N, netRoot_mem_netBallSet N r⟩ : ℕ) = netRoot N' ∧
    ∀ x y : netBallSet N r,
      (netGraph N).Adj x y ↔ (netGraph N').Adj (φ x) (φ y)}

/-- Rooted isomorphisms of two finite balls form a finite type. -/
theorem finite_rootedBallIso {m : ℕ} (N N' : Net m) (r : ℕ) :
    Finite (RootedBallIso N N' r) := by
  classical
  letI : Fintype (netBallSet N r) := (finite_netBallSet N r).fintype
  letI : Fintype (netBallSet N' r) := (finite_netBallSet N' r).fintype
  unfold RootedBallIso
  infer_instance

/-- Equal rooted-ball types have a rooted ball isomorphism. -/
theorem nonempty_rootedBallIso_of_netBallType_eq {m : ℕ} {N N' : Net m} {r : ℕ}
    (h : netBallType N r = netBallType N' r) : Nonempty (RootedBallIso N N' r) := by
  obtain ⟨φ, hroot, hadj⟩ := exists_ballEquiv_of_netBallType_eq h
  exact ⟨⟨φ, hroot, hadj⟩⟩

/-- The inverse of a rooted ball isomorphism is a rooted ball isomorphism. -/
def RootedBallIso.symm {m : ℕ} {N N' : Net m} {r : ℕ}
    (φ : RootedBallIso N N' r) : RootedBallIso N' N r := by
  refine ⟨φ.1.symm, ?_, ?_⟩
  · have hroot : φ.1 ⟨netRoot N, netRoot_mem_netBallSet N r⟩ =
        ⟨netRoot N', netRoot_mem_netBallSet N' r⟩ := Subtype.ext φ.2.1
    have h := congrArg φ.1.symm hroot
    simpa only [Equiv.symm_apply_apply] using (congrArg Subtype.val h).symm
  · intro x y
    have h := (φ.2.2 (φ.1.symm x) (φ.1.symm y)).symm
    simpa only [Equiv.apply_symm_apply] using h

/-- A rooted ball isomorphism maps each smaller ball into the corresponding ball. -/
theorem RootedBallIso.mem_ball_image {m : ℕ} {N N' : Net m} {r : ℕ}
    (φ : RootedBallIso N N' r) :
    ∀ s ≤ r, ∀ x : netBallSet N r,
      (x : ℕ) ∈ netBallSet N s → (φ.1 x : ℕ) ∈ netBallSet N' s := by
  intro s
  induction s with
  | zero =>
      intro _ x hx
      have hxroot : (x : ℕ) = netRoot N := hx
      have hx' : x = ⟨netRoot N, netRoot_mem_netBallSet N r⟩ := Subtype.ext hxroot
      subst x
      exact φ.2.1
  | succ s ih =>
      intro hsr x hx
      have hle : s ≤ r := (Nat.le_succ s).trans hsr
      rcases hx with hx | ⟨w, hw, hadj⟩
      · exact Or.inl (ih hle x hx)
      · let w' : netBallSet N r := ⟨w, netBallSet_mono N hle hw⟩
        have hw' : (φ.1 w' : ℕ) ∈ netBallSet N' s := ih hle w' hw
        have hadj' := (φ.2.2 w' x).1 hadj
        exact Or.inr ⟨φ.1 w', hw', hadj'⟩

/-- A rooted ball isomorphism preserves membership in every smaller ball. -/
theorem RootedBallIso.mem_ball_iff {m : ℕ} {N N' : Net m} {r s : ℕ}
    (φ : RootedBallIso N N' r) (hs : s ≤ r) (x : netBallSet N r) :
    (x : ℕ) ∈ netBallSet N s ↔ (φ.1 x : ℕ) ∈ netBallSet N' s := by
  constructor
  · exact φ.mem_ball_image s hs x
  · intro hx
    have h := φ.symm.mem_ball_image s hs (φ.1 x) hx
    simpa only [RootedBallIso.symm, Equiv.symm_apply_apply] using h

end RWRS.Support
