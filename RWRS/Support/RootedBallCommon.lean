import RWRS.Support.RootedGraphFactor

/-!
# Common finite-ball codes

Equality of the canonical type at a radius supplies a common finite rooted
adjacency code for the two balls.
-/

namespace RWRS.Support

/-- The enumeration of finite rooted adjacency matrices is injective. -/
theorem rootedFiniteGraphCode_injective : Function.Injective rootedFiniteGraphCode := by
  exact @Encodable.encode_injective RootedFiniteGraph
    (Encodable.ofCountable RootedFiniteGraph)

/-- Equal ball types have a common matching finite rooted graph. -/
theorem exists_common_netBallMatches_of_netBallType_eq {m : ℕ} {N N' : Net m}
    {r : ℕ} (h : netBallType N r = netBallType N' r) :
    ∃ c : RootedFiniteGraph, NetBallMatches N r c ∧ NetBallMatches N' r c := by
  classical
  have hN : HasNetBallCode N r (netBallType N r) :=
    Nat.find_spec (exists_netBallCode N r)
  have hN' : HasNetBallCode N' r (netBallType N r) := by
    rw [h]
    exact Nat.find_spec (exists_netBallCode N' r)
  obtain ⟨c, hc, hmatch⟩ := hN
  obtain ⟨c', hc', hmatch'⟩ := hN'
  have heq : c = c' := rootedFiniteGraphCode_injective (hc.trans hc'.symm)
  subst c'
  exact ⟨c, hmatch, hmatch'⟩

end RWRS.Support
