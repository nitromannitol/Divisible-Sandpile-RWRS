/-
Cited input: the Efron--Stein inequality, quoted in the proof of
`prop:critical` (`rwrs.tex:694-699`) from Efron and Stein, *The jackknife
estimate of variance*.

Proved here for every countable vertex set (`efronStein`), by applying the
shared library's finite-product inequality to the partial integral over an
increasing exhaustion of the index set and passing to the limit with Fatou;
no hypothesis of any frozen statement carries it any longer.
-/
import RWRS.Setting
import Mathlib.Probability.Moments.Variance
import LatticeProb.Prob.EfronSteinCountable

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

/-- The Efron--Stein inequality for a countable i.i.d. field.
Cited in `rwrs.tex:694-699`; proved by the shared library. -/
theorem RWRS.External.efronStein (V : Type*) [Countable V] :
    RWRS.External.EfronStein V
-- FROZEN-STATEMENT-END
:= by
  classical
  intro ν hν F hFm hF2
  haveI := hν
  have hres : ∀ (ξ : V → ℝ) (v : V) (t : ℝ),
      RWRS.resample ξ v t = Function.update ξ v t := fun ξ v t => by
    funext w; by_cases h : w = v <;> simp [RWRS.resample, h]
  simp only [hres, RWRS.iidLaw] at hF2 ⊢
  exact LatticeProb.evariance_le_half_sum_resample ν F hFm hF2
