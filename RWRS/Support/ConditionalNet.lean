import RWRS.Network
import LatticeProb.Prob.ConditionalMeasure

/-!
# Conditional laws of rooted graphs

The regular conditional law given rerooting-invariant events preserves
almost-sure support on connected networks. The construction uses the
conditional-measure theorem in `LatticeProb.Prob.ConditionalMeasure`.
-/

namespace RWRS.Support

open MeasureTheory
open scoped ENNReal

/-- Conditional laws given invariant events retain almost-sure connectedness. -/
theorem exists_conditional_net_laws (Q : Measure (Net 0)) [IsProbabilityMeasure Q]
    (hgood : ∀ᵐ N ∂Q, NetGood N) :
    ∃ K : Net 0 → Measure (Net 0),
      (∀ N, IsProbabilityMeasure (K N)) ∧
      (∀ A : Set (Net 0), MeasurableSet A →
        Measurable[invariantSigma 0] fun N => K N A) ∧
      (∀ A : Set (Net 0), MeasurableSet A →
        ∀ B : Set (Net 0), MeasurableSet[invariantSigma 0] B →
          (∫⁻ N in B, K N A ∂Q) = Q (A ∩ B)) ∧
      (∀ᵐ N ∂Q, ∀ᵐ M ∂(K N), NetGood M) := by
  apply LatticeProb.exists_conditionalMeasures Q ?_ hgood
  intro A hA
  exact hA.1

end RWRS.Support
