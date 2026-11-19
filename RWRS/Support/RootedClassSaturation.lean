import RWRS.Support.RootedClassSigma

/-!
# Rerooting saturation of class events

The set of rooted graph classes obtained by moving the root to an arbitrary
vertex of a class event is measurable and rerooting invariant.
-/

namespace RWRS.Support

open MeasureTheory

/-- Reroot a connected network at a specified vertex. -/
def goodNetReroot (N : GoodNet) (y : ℕ) : GoodNet :=
  ⟨netReroot N.1 y, netGood_netReroot N.2 y⟩

/-- Rerooting a connected network at a specified vertex is measurable. -/
theorem measurable_goodNetReroot (y : ℕ) : Measurable (fun N => goodNetReroot N y) := by
  exact ((measurable_netReroot y).comp measurable_subtype_coe).subtype_mk

/-- Rerooted classes correspond under a graph isomorphism. -/
theorem goodNetClass_reroot_eq_of_netIso {N N' : GoodNet} (h : NetIso N.1 N'.1) :
    ∃ φ : ℕ ≃ ℕ, ∀ y, goodNetClass (goodNetReroot N y) =
      goodNetClass (goodNetReroot N' (φ y)) := by
  obtain ⟨φ, hadj, _, hmark⟩ := h
  refine ⟨φ, fun y => (goodNetClass_eq_iff_netIso _ _).2 ?_⟩
  exact ⟨φ, hadj, rfl, hmark⟩

/-- The rerooting saturation of a class event. -/
noncomputable def rootedClassSaturation (D : Set RootedBallClass) : Set RootedBallClass :=
  {c | ∃ y, goodNetClass (goodNetReroot (goodNetClassRepresentative c) y) ∈ D}

/-- Membership in the saturation may be tested on any connected representative. -/
theorem mem_rootedClassSaturation_iff (D : Set RootedBallClass) (N : GoodNet) :
    goodNetClass N ∈ rootedClassSaturation D ↔
      ∃ y, goodNetClass (goodNetReroot N y) ∈ D := by
  let R := goodNetClassRepresentative (goodNetClass N)
  have hR : NetIso R.1 N.1 := (goodNetClass_eq_iff_netIso R N).1
    (goodNetClass_representative (goodNetClass N))
  obtain ⟨φ, hφ⟩ := goodNetClass_reroot_eq_of_netIso hR
  change (∃ y, goodNetClass (goodNetReroot R y) ∈ D) ↔ _
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨φ y, (hφ y) ▸ hy⟩
  · rintro ⟨y, hy⟩
    refine ⟨φ.symm y, ?_⟩
    rw [hφ, Equiv.apply_symm_apply]
    exact hy

/-- The saturation of a measurable class event is measurable. -/
theorem measurableSet_rootedClassSaturation {D : Set RootedBallClass} (hD : MeasurableSet D) :
    MeasurableSet (rootedClassSaturation D) := by
  apply (measurable_goodNetClass.measurableSet_preimage_iff_of_surjective
    goodNetClass_surjective).1
  have heq : goodNetClass ⁻¹' rootedClassSaturation D =
      ⋃ y : ℕ, (fun N => goodNetClass (goodNetReroot N y)) ⁻¹' D := by
    ext N
    simp only [Set.mem_preimage, Set.mem_iUnion, mem_rootedClassSaturation_iff]
  rw [heq]
  exact MeasurableSet.iUnion fun y =>
    hD.preimage (measurable_goodNetClass.comp (measurable_goodNetReroot y))

/-- The saturation of a measurable class event is invariant under rerooting. -/
theorem measurableSet_rootedClassSaturation_invariantSigma {D : Set RootedBallClass}
    (hD : MeasurableSet D) : MeasurableSet[rootedClassInvariantSigma] (rootedClassSaturation D) := by
  refine ⟨measurableSet_rootedClassSaturation hD, ?_⟩
  intro N y
  rw [mem_rootedClassSaturation_iff, mem_rootedClassSaturation_iff]
  rfl

end RWRS.Support
