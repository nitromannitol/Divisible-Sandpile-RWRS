import RWRS.Support.ConditionalClassStationarity
import RWRS.Support.RootedClassPathKernel

/-!
# Conditional rooted-class path laws

Almost-sure path properties of a stationary network's class walk pass to the
walks started from almost all its conditional network laws.
-/

namespace RWRS.Support

open MeasureTheory ProbabilityTheory

/-- Almost-sure class-path properties pass to almost every conditional network law. -/
theorem ae_ae_conditional_rootedClassPathLaw (Q : Measure (Net 0)) [IsProbabilityMeasure Q]
    (hgood : ∀ᵐ N ∂Q, NetGood N) {p : (ℕ → RootedBallClass) → Prop}
    (hp : ∀ᵐ x ∂rootedClassPathLaw (goodNetClassLaw Q), p x) :
    ∀ᵐ N ∂Q, ∀ᵐ x ∂rootedClassPathLaw (goodNetClassLaw (condExpKernel Q (invariantSigma 0) N)),
      p x := by
  obtain ⟨N, hN⟩ := hgood.exists
  let N₀ : GoodNet := ⟨N, hN⟩
  have hmix := conditionalClassKernel_comp_restrict N₀ Q hgood
    (MeasurableSet.univ : MeasurableSet[invariantSigma 0] Set.univ)
  simp only [Measure.restrict_univ] at hmix
  have hP : rootedClassPathLaw (goodNetClassLaw Q) =
      (rootedClassPathKernel ∘ₖ conditionalClassKernel N₀ Q) ∘ₘ Q.trim invariantSigma_zero_le := by
    rw [← rootedClassPathKernel_comp, ← hmix, Measure.comp_assoc]
  rw [hP] at hp
  have hcond := ae_of_ae_trim invariantSigma_zero_le (Measure.ae_ae_of_ae_comp hp)
  have hsupport := LatticeProb.ae_ae_conditionalMeasure Q invariantSigma_zero_le hgood
  filter_upwards [hcond, hsupport] with M hM hMg
  have heq : conditionalClassKernel N₀ Q M = goodNetClassLaw (condExpKernel Q (invariantSigma 0) M) := by
    rw [conditionalClassKernel, Kernel.map_apply _ (measurable_goodNetClassTotal N₀),
      goodNetClassLaw_eq_map_total N₀ _ hMg]
  rw [Kernel.comp_apply, heq, rootedClassPathKernel_comp] at hM
  exact hM

end RWRS.Support
