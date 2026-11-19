import RWRS.Support.NetGoodMeasurable

/-!
# Connectedness and rooted isomorphism

Connectedness is preserved by relabelling the vertices and by rerooting.
-/

namespace RWRS.Support

open MeasureTheory

/-- Isomorphic networks are connected simultaneously. -/
theorem netGood_iff_of_netIso {m : ℕ} {N N' : Net m} (h : NetIso N N') :
    NetGood N ↔ NetGood N' := by
  obtain ⟨φ, hadj, -, -⟩ := h
  let e : netGraph N ≃g netGraph N' :=
    ⟨φ, fun {i j} => (hadj i j).symm⟩
  exact e.connected_iff

/-- Connected networks form an event in the rerooting-invariant σ-algebra. -/
theorem measurableSet_netGood_invariantSigma {m : ℕ} :
    MeasurableSet[invariantSigma m] {N : Net m | NetGood N} := by
  refine ⟨measurableSet_netGood, ?_, ?_⟩
  · intro N N' h
    exact netGood_iff_of_netIso h
  · intro N y _
    rfl

end RWRS.Support
