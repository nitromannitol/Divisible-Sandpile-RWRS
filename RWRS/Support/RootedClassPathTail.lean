import RWRS.Support.RootedClassPathInvariant
import RWRS.Support.RootedClassPathShift

/-!
# Invariant events as path tail events

A rerooting-invariant class event agrees almost surely with the event that the
class walk eventually remains in it. The latter is exactly shift invariant.
-/

namespace RWRS.Support

open MeasureTheory ProbabilityTheory

/-- The event that a class walk eventually stays in a given class event. -/
def rootedClassPathTailEvent (D : Set RootedBallClass) : Set (ℕ → RootedBallClass) :=
  {x | ∃ n : ℕ, ∀ m ≥ n, x m ∈ D}

/-- A measurable class event gives a measurable path tail event. -/
theorem measurableSet_rootedClassPathTailEvent {D : Set RootedBallClass}
    (hD : MeasurableSet D) : MeasurableSet (rootedClassPathTailEvent D) := by
  have heq : rootedClassPathTailEvent D =
      ⋃ n : ℕ, ⋂ m : {m : ℕ // n ≤ m}, (fun x : ℕ → RootedBallClass => x m.1) ⁻¹' D := by
    ext x
    simp only [rootedClassPathTailEvent, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_iInter,
      Set.mem_preimage, Subtype.forall]
  rw [heq]
  exact MeasurableSet.iUnion fun n => MeasurableSet.iInter fun m =>
    hD.preimage (measurable_pi_apply m.1)

/-- A path tail event is invariant under dropping the initial state. -/
theorem measurableSet_rootedClassPathTailEvent_invariants {D : Set RootedBallClass}
    (hD : MeasurableSet D) :
    MeasurableSet[MeasurableSpace.invariants rootedClassPathShift] (rootedClassPathTailEvent D) := by
  refine ⟨measurableSet_rootedClassPathTailEvent hD, ?_⟩
  ext x
  change (∃ n : ℕ, ∀ m ≥ n, x (m + 1) ∈ D) ↔ ∃ n : ℕ, ∀ m ≥ n, x m ∈ D
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n + 1, ?_⟩
    intro m hm
    have heq : m - 1 + 1 = m := by omega
    rw [← heq]
    apply hn
    omega
  · rintro ⟨n, hn⟩
    exact ⟨n, fun m hm => hn (m + 1) (by omega)⟩

/-- Along a class walk, an invariant class event agrees almost surely with its tail event. -/
theorem rootedClassPathTailEvent_ae_eq (ν : Measure RootedBallClass)
    [IsProbabilityMeasure ν] {D : Set RootedBallClass}
    (hD : MeasurableSet[rootedClassInvariantSigma] D) :
    rootedClassPathTailEvent D =ᵐ[rootedClassPathLaw ν] (fun x : ℕ → RootedBallClass => x 0) ⁻¹' D := by
  filter_upwards [ae_rootedClassPathLaw_mem_iff_zero ν hD] with x hx
  apply propext
  change (∃ n : ℕ, ∀ m ≥ n, x m ∈ D) ↔ x 0 ∈ D
  constructor
  · rintro ⟨n, hn⟩
    exact (hx n).1 (hn n le_rfl)
  · intro h
    exact ⟨0, fun m _ => (hx m).2 h⟩

end RWRS.Support
