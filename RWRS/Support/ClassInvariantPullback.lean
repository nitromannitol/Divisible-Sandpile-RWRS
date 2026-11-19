import RWRS.Support.RootedClassSigma

/-!
# Pullback of invariant class events

An invariant class event extends by the empty event outside connected network
codes, giving an event in the network invariant σ-algebra.
-/

namespace RWRS.Support

open MeasureTheory

/-- Extend a rooted class event by the empty event on disconnected networks. -/
def classInvariantLift (D : Set RootedBallClass) : Set (Net 0) :=
  {N | ∃ hN : NetGood N, goodNetClass ⟨N, hN⟩ ∈ D}

/-- On connected networks, the extended event is the original class event. -/
theorem mem_classInvariantLift_iff (D : Set RootedBallClass) (N : GoodNet) :
    N.1 ∈ classInvariantLift D ↔ goodNetClass N ∈ D := by
  constructor
  · rintro ⟨hN, h⟩
    exact h
  · intro h
    exact ⟨N.2, h⟩

/-- The extension of an invariant class event is a network invariant event. -/
theorem measurableSet_classInvariantLift {D : Set RootedBallClass}
    (hD : MeasurableSet[rootedClassInvariantSigma] D) :
    MeasurableSet[invariantSigma 0] (classInvariantLift D) := by
  have heq : classInvariantLift D =
      (Subtype.val : GoodNet → Net 0) '' (goodNetClass ⁻¹' D) := by
    ext N
    constructor
    · rintro ⟨hN, h⟩
      exact ⟨⟨N, hN⟩, h, rfl⟩
    · rintro ⟨⟨M, hM⟩, h, rfl⟩
      exact ⟨hM, h⟩
  have hmeas : MeasurableSet (classInvariantLift D) := by
    rw [heq]
    exact (MeasurableEmbedding.subtype_coe measurableSet_netGood).measurableSet_image.mpr
      (measurable_goodNetClass hD.1)
  refine ⟨hmeas, ?_, ?_⟩
  · intro N N' h
    constructor
    · rintro ⟨hN, hd⟩
      have hN' : NetGood N' := (netGood_iff_of_netIso h).1 hN
      refine ⟨hN', ?_⟩
      have hc := (goodNetClass_eq_iff_netIso ⟨N, hN⟩ ⟨N', hN'⟩).2 h
      rw [← hc]
      exact hd
    · rintro ⟨hN', hd⟩
      have hN : NetGood N := (netGood_iff_of_netIso h).2 hN'
      refine ⟨hN, ?_⟩
      have hc := (goodNetClass_eq_iff_netIso ⟨N, hN⟩ ⟨N', hN'⟩).2 h
      rw [hc]
      exact hd
  · intro N y _
    constructor
    · rintro ⟨hN, hd⟩
      exact ⟨hN, (hD.2 ⟨N, hN⟩ y).1 hd⟩
    · rintro ⟨hN, hd⟩
      exact ⟨hN, (hD.2 ⟨N, hN⟩ y).2 hd⟩

end RWRS.Support
