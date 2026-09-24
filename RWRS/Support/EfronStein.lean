/-
The Efron--Stein inequality of `rwrs.tex:694-699` is a theorem of the shared
library, not an input.  The library proves it over a countable index set by
applying the finite-product inequality to the partial integral over an
increasing exhaustion of the index set and passing to the limit with Fatou;
here it is only restated in the vocabulary of this repository, whose `resample`
is the library's `Function.update` and whose `iidLaw` is the library's
`Measure.infinitePi`.
-/
import RWRS.External.EfronStein
import RWRS.Support.Countable
import LatticeProb.Prob.EfronSteinCountable

open MeasureTheory
open scoped ENNReal

namespace RWRS.Support

variable {V : Type*}

/-- Resampling one coordinate is updating one coordinate. -/
theorem resample_eq_update [DecidableEq V] (ξ : V → ℝ) (v : V) (t : ℝ) :
    RWRS.resample ξ v t = Function.update ξ v t := by
  funext w
  by_cases h : w = v <;> simp [RWRS.resample, h]

/-- **The Efron--Stein inequality over a countable vertex set.**  This
discharges the external hypothesis `RWRS.External.EfronStein`. -/
theorem efronStein (V : Type*) [Countable V] : RWRS.External.EfronStein V := by
  classical
  intro ν hν F hFm hF2
  haveI := hν
  have hres : ∀ (ξ : V → ℝ) (v : V) (t : ℝ),
      RWRS.resample ξ v t = Function.update ξ v t := fun ξ v t =>
    resample_eq_update ξ v t
  simp only [hres, RWRS.iidLaw] at hF2 ⊢
  exact LatticeProb.evariance_le_half_sum_resample ν F hFm hF2

end RWRS.Support
