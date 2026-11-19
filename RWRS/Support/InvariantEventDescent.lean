import RWRS.Support.RootedGraphClasses

/-!
# Descent of invariant events

An isomorphism-invariant measurable event on network codes descends to a
measurable event of the realized rooted ball classes.
-/

namespace RWRS.Support

open MeasureTheory

/-- A measurable isomorphism-invariant event descends to the rooted ball classes. -/
theorem exists_measurable_class_event {A : Set (Net 0)}
    (hA : MeasurableSet A) (hiso : NetInvariantSet A) :
    ∃ D : Set RootedBallClass, MeasurableSet D ∧
      ∀ N : GoodNet, N.1 ∈ A ↔ goodNetClass N ∈ D := by
  classical
  let D : Set RootedBallClass := {y | (Classical.choose y.property).1 ∈ A}
  have hpre : goodNetClass ⁻¹' D = {N : GoodNet | N.1 ∈ A} := by
    ext N
    change (Classical.choose (goodNetClass N).property).1 ∈ A ↔ N.1 ∈ A
    have hclass : goodNetClass (Classical.choose (goodNetClass N).property) = goodNetClass N := by
      apply Subtype.ext
      exact Classical.choose_spec (goodNetClass N).property
    exact hiso _ _ ((goodNetClass_eq_iff_netIso _ _).1 hclass)
  have hD : MeasurableSet D :=
    (measurable_goodNetClass.measurableSet_preimage_iff_of_surjective
      goodNetClass_surjective).1 (by rw [hpre]; exact hA.preimage measurable_subtype_coe)
  refine ⟨D, hD, ?_⟩
  intro N
  change N.1 ∈ A ↔ N ∈ goodNetClass ⁻¹' D
  rw [hpre]
  rfl

/-- Every invariant event descends to a measurable event of rooted ball classes. -/
theorem exists_measurable_class_event_of_invariantSigma {A : Set (Net 0)}
    (hA : MeasurableSet[invariantSigma 0] A) :
    ∃ D : Set RootedBallClass, MeasurableSet D ∧
      ∀ N : GoodNet, N.1 ∈ A ↔ goodNetClass N ∈ D :=
  exists_measurable_class_event hA.1 hA.2.1

/-- An invariant event descends to a measurable class event unchanged by rerooting. -/
theorem exists_measurable_rerootInvariant_class_event {A : Set (Net 0)}
    (hA : MeasurableSet[invariantSigma 0] A) :
    ∃ D : Set RootedBallClass, MeasurableSet D ∧
      (∀ N : GoodNet, N.1 ∈ A ↔ goodNetClass N ∈ D) ∧
      (∀ (N : GoodNet) (y : ℕ),
        goodNetClass N ∈ D ↔ goodNetClass ⟨netReroot N.1 y, N.2⟩ ∈ D) := by
  obtain ⟨D, hD, hdesc⟩ := exists_measurable_class_event_of_invariantSigma hA
  refine ⟨D, hD, hdesc, ?_⟩
  intro N y
  exact (hdesc N).symm.trans
    ((mem_iff_netReroot_of_netGood hA.2.2 N.2 y).trans
      (hdesc ⟨netReroot N.1 y, N.2⟩))

end RWRS.Support
