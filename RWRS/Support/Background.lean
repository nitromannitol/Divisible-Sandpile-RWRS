/-
The background of `lem:moment-sharpness`: a weighted sum of independent centred
masses is small with high probability.

The weighted sum splits at a level `M` into a bounded part and a tail part.  The
tail part has small mean absolute value, so Markov's inequality controls it; the
bounded part has variance at most `M^2` times the sum of the squared weights, so
Chebyshev's inequality controls it.  Both halves use the weighted-sum machinery
of `prop:critical`(a).
-/
import RWRS.Support.SecondMoment

namespace RWRS.Support

open MeasureTheory
open scoped ENNReal Classical

variable {V : Type*}

/-- **The triangle inequality for a weighted sum.** -/
theorem integral_abs_weighted_le {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (S : Finset V) (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) {f : ℝ → ℝ}
    (hint : Integrable f ν) :
    ∫ ξ, |∑ v ∈ S, w v * f (ξ v)| ∂(RWRS.iidLaw V ν)
      ≤ (∑ v ∈ S, w v) * ∫ z, |f z| ∂ν := by
  haveI : IsProbabilityMeasure (RWRS.iidLaw V ν) := instIsProbabilityMeasureIid ν
  have hcoord : ∀ v : V, Integrable (fun ξ : V → ℝ => w v * f (ξ v)) (RWRS.iidLaw V ν) :=
    fun v => (integrable_coord ν v hint).const_mul (w v)
  calc ∫ ξ, |∑ v ∈ S, w v * f (ξ v)| ∂(RWRS.iidLaw V ν)
      ≤ ∫ ξ, ∑ v ∈ S, |w v * f (ξ v)| ∂(RWRS.iidLaw V ν) := by
        refine integral_mono ?_ ?_ fun ξ => Finset.abs_sum_le_sum_abs _ _
        · exact (integrable_finsetSum _ fun v _ => hcoord v).abs
        · exact integrable_finsetSum _ fun v _ => (hcoord v).abs
    _ = ∑ v ∈ S, ∫ ξ, |w v * f (ξ v)| ∂(RWRS.iidLaw V ν) :=
        integral_finsetSum _ fun v _ => (hcoord v).abs
    _ = ∑ v ∈ S, w v * ∫ z, |f z| ∂ν := by
        refine Finset.sum_congr rfl fun v _ => ?_
        have habs : ∀ ξ : V → ℝ, |w v * f (ξ v)| = w v * |f (ξ v)| := by
          intro ξ; rw [abs_mul, abs_of_nonneg (hw v)]
        rw [integral_congr_ae (Filter.Eventually.of_forall habs), integral_const_mul,
          integral_coord ν v hint.abs.aestronglyMeasurable]
    _ = (∑ v ∈ S, w v) * ∫ z, |f z| ∂ν := by rw [Finset.sum_mul]

end RWRS.Support
