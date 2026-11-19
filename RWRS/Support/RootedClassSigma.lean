import RWRS.Support.RootedClassInvariant
import RWRS.Support.InvariantEventDescent

/-!
# The rerooting-invariant class σ-algebra

Measurable class events unchanged by moving the root form a σ-algebra. Every
invariant event of connected network codes descends to this σ-algebra.
-/

namespace RWRS.Support

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- The σ-algebra of measurable class events invariant under rerooting. -/
@[reducible] def rootedClassInvariantSigma : MeasurableSpace RootedBallClass where
  MeasurableSet' D := MeasurableSet D ∧
    ∀ (N : GoodNet) (y : ℕ),
      goodNetClass N ∈ D ↔ goodNetClass ⟨netReroot N.1 y, N.2⟩ ∈ D
  measurableSet_empty := ⟨MeasurableSet.empty, fun _ _ => Iff.rfl⟩
  measurableSet_compl := by
    rintro D ⟨hD, hre⟩
    exact ⟨hD.compl, fun N y => not_congr (hre N y)⟩
  measurableSet_iUnion := by
    intro D hD
    refine ⟨MeasurableSet.iUnion fun i => (hD i).1, ?_⟩
    intro N y
    simp only [Set.mem_iUnion]
    exact exists_congr fun i => (hD i).2 N y

/-- The invariant class σ-algebra is contained in the class Borel σ-algebra. -/
theorem rootedClassInvariantSigma_le :
    rootedClassInvariantSigma ≤ (inferInstance : MeasurableSpace RootedBallClass) :=
  fun _ hD => hD.1

/-- The class transition kernel fixes each invariant class event. -/
theorem classRerootKernel_apply_of_invariantSigma {D : Set RootedBallClass}
    (hD : MeasurableSet[rootedClassInvariantSigma] D) (c : RootedBallClass) :
    classRerootKernel c D = D.indicator (fun _ => (1 : ℝ≥0∞)) c :=
  classRerootKernel_apply_of_rerootInvariant hD.1 hD.2 c

/-- Each invariant network event descends to an invariant class event on connected codes. -/
theorem exists_classInvariant_event {A : Set (Net 0)}
    (hA : MeasurableSet[invariantSigma 0] A) :
    ∃ D : Set RootedBallClass, MeasurableSet[rootedClassInvariantSigma] D ∧
      ∀ N : GoodNet, N.1 ∈ A ↔ goodNetClass N ∈ D := by
  obtain ⟨D, hD, hdesc, hre⟩ := exists_measurable_rerootInvariant_class_event hA
  exact ⟨D, ⟨hD, hre⟩, hdesc⟩

end RWRS.Support
