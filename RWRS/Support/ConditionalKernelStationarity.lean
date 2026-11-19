import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.Probability.Kernel.Composition.MeasureComp

/-!
# Conditional stationarity from restricted mixtures

If every measurable restriction of a mixing measure produces a stationary
mixture, almost every measure in the kernel is stationary.
-/

namespace RWRS.Support

open MeasureTheory ProbabilityTheory

/-- Stationarity of all restricted mixtures implies stationarity of almost every kernel fiber. -/
theorem ae_kernel_stationary_of_restrict {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace.CountablyGenerated β] (μ : Measure α) [IsFiniteMeasure μ]
    (K : Kernel α β) [IsMarkovKernel K] (P : Kernel β β) [IsMarkovKernel P]
    (h : ∀ B : Set α, MeasurableSet B → P ∘ₘ (K ∘ₘ μ.restrict B) = K ∘ₘ μ.restrict B) :
    ∀ᵐ x ∂μ, P ∘ₘ K x = K x := by
  have hprod : μ ⊗ₘ (P ∘ₖ K) = μ ⊗ₘ K := by
    apply Measure.ext_prod
    intro B A hB hA
    rw [Measure.compProd_apply_prod hB hA, Measure.compProd_apply_prod hB hA,
      ← Measure.bind_apply hA (Kernel.aemeasurable (P ∘ₖ K)),
      ← Measure.bind_apply hA (Kernel.aemeasurable K), ← Measure.comp_assoc, h B hB]
  have hae := Kernel.ae_eq_of_compProd_eq hprod
  filter_upwards [hae] with x hx
  exact hx

end RWRS.Support
