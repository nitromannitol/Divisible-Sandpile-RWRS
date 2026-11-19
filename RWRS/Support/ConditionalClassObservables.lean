import RWRS.Support.RootedClassInvariantVersion
import RWRS.Support.ConditionalNet

/-!
# Invariant class observables on conditional network laws

Invariant observables of connected rooted classes extend to invariant network
observables and are constant along almost every conditional network fiber.
-/

namespace RWRS.Support

open MeasureTheory ProbabilityTheory Function

/-- Extend a real class observable by zero outside the connected networks. -/
noncomputable def invariantClassObservable (f : RootedBallClass → ℝ) : Net 0 → ℝ :=
  Function.extend (Subtype.val : GoodNet → Net 0) (f ∘ goodNetClass) (fun _ => 0)

/-- On connected networks the extended observable has its class value. -/
theorem invariantClassObservable_of_good (f : RootedBallClass → ℝ) (N : GoodNet) :
    invariantClassObservable f N.1 = f (goodNetClass N) := by
  exact Subtype.val_injective.extend_apply (f ∘ goodNetClass) (fun _ => 0) N

/-- The extension vanishes on disconnected networks. -/
theorem invariantClassObservable_of_not_good (f : RootedBallClass → ℝ) (N : Net 0)
    (hN : ¬ NetGood N) : invariantClassObservable f N = 0 := by
  apply Function.extend_apply'
  rintro ⟨⟨M, hM⟩, hMN⟩
  exact hN (hMN ▸ hM)

/-- A class-invariant observable extends to an invariant network observable. -/
theorem measurable_invariantClassObservable {f : RootedBallClass → ℝ}
    (hf : Measurable[rootedClassInvariantSigma] f) :
    Measurable[invariantSigma 0] (invariantClassObservable f) := by
  have hf' : Measurable f := hf.mono rootedClassInvariantSigma_le le_rfl
  have hmeas : Measurable (invariantClassObservable f) :=
    (MeasurableEmbedding.subtype_coe measurableSet_netGood).measurable_extend
      (hf'.comp measurable_goodNetClass) measurable_const
  have hre (N : GoodNet) (y : ℕ) :
      f (goodNetClass N) = f (goodNetClass (goodNetReroot N y)) := by
    have h := hf (measurableSet_singleton (f (goodNetClass N)))
    have h' := (h.2 N y).1 (Set.mem_singleton _)
    exact (Set.mem_singleton_iff.mp h').symm
  intro S hS
  refine ⟨hmeas hS, ?_, ?_⟩
  · intro N N' hiso
    change invariantClassObservable f N ∈ S ↔ invariantClassObservable f N' ∈ S
    by_cases hN : NetGood N
    · have hN' : NetGood N' := (netGood_iff_of_netIso hiso).1 hN
      have heq : invariantClassObservable f N = invariantClassObservable f N' := by
        rw [invariantClassObservable_of_good f ⟨N, hN⟩,
          invariantClassObservable_of_good f ⟨N', hN'⟩,
          (goodNetClass_eq_iff_netIso ⟨N, hN⟩ ⟨N', hN'⟩).2 hiso]
      rw [heq]
    · have hN' : ¬ NetGood N' := fun h => hN ((netGood_iff_of_netIso hiso).2 h)
      rw [show invariantClassObservable f N = 0 from invariantClassObservable_of_not_good f N hN,
        show invariantClassObservable f N' = 0 from invariantClassObservable_of_not_good f N' hN']
  · intro N y _
    change invariantClassObservable f N ∈ S ↔ invariantClassObservable f (netReroot N y) ∈ S
    by_cases hN : NetGood N
    · have hNr : NetGood (netReroot N y) := netGood_netReroot hN y
      rw [invariantClassObservable_of_good f ⟨N, hN⟩,
        invariantClassObservable_of_good f ⟨netReroot N y, hNr⟩,
        hre ⟨N, hN⟩ y]
      rfl
    · have hNr : ¬ NetGood (netReroot N y) := hN
      rw [invariantClassObservable_of_not_good f N hN,
        invariantClassObservable_of_not_good f (netReroot N y) hNr]

/-- A countable family of invariant class observables is constant in almost every conditional fiber. -/
theorem ae_ae_invariantClassObservable (Q : Measure (Net 0)) [IsProbabilityMeasure Q]
    (f : ℕ → RootedBallClass → ℝ)
    (hf : ∀ j, Measurable[rootedClassInvariantSigma] (f j)) :
    ∀ᵐ N ∂Q, ∀ j, ∀ᵐ M ∂condExpKernel Q (invariantSigma 0) N,
      invariantClassObservable (f j) M = invariantClassObservable (f j) N := by
  apply ae_all_iff.mpr
  intro j
  exact LatticeProb.ae_ae_eq_of_measurable_conditionalMeasure (m := invariantSigma 0) Q
    (fun _ h => h.1) (measurable_invariantClassObservable (hf j))

end RWRS.Support
