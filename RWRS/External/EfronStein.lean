/-
External input: the Efron--Stein inequality, quoted in the proof of
`prop:critical` (`rwrs.tex:694-699`) from Efron and Stein, *The jackknife
estimate of variance*.

Assumed here.  It enters only as an explicit hypothesis of the results whose
proofs use it.
-/
import RWRS.Setting
import Mathlib.Probability.Moments.Variance

open MeasureTheory
open scoped ENNReal

-- FROZEN-STATEMENT-BEGIN
/-- The Efron--Stein inequality for a measurable, square integrable function of
an i.i.d. field indexed by a countable set: the variance is at most half the sum
over coordinates of the mean squared change made by resampling that coordinate.

Measurability and square integrability are the hypotheses of the inequality as
Efron and Stein state it, and both are needed for the statement to say what they
say: for a non-measurable function the two sides are lower integrals of
different things, and without square integrability the mean inside the variance
is the junk value of a Bochner integral that does not converge. -/
def RWRS.External.EfronStein (V : Type*) : Prop :=
  ∀ ν : Measure ℝ, IsProbabilityMeasure ν → ∀ F : (V → ℝ) → ℝ,
    Measurable F → Integrable (fun ξ => F ξ ^ 2) (RWRS.iidLaw V ν) →
    ProbabilityTheory.evariance F (RWRS.iidLaw V ν)
      ≤ (∑' v : V, ∫⁻ ξ, ∫⁻ t, ENNReal.ofReal ((F ξ - F (RWRS.resample ξ v t)) ^ 2) ∂ν
          ∂(RWRS.iidLaw V ν)) / 2
-- FROZEN-STATEMENT-END
