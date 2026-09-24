/-
Proposition 5.10 of `rwrs.tex`, frozen.  `rwrs.tex:950-954` (label
`prop:convexity-reduction`):

  "Let $G=(V,E)$ be an infinite, locally finite, connected graph, and let
   $(\xi(v))_{v\in V}$ be i.i.d. and independent of the walk with $\E[\xi]=0$,
   $\xi\not\equiv0$, and $\xi$ symmetric about $0$.  If for every i.i.d.
   scenery on $G$ with mean $0$, positive variance, and finite second moment,
   $\sup_\tau\E_o[S_\tau\mid\xi]=\infty$ a.s., then the same conclusion holds
   for $\xi$.  The same reduction holds with $\sup_\tau$ replaced by $\sup_n$."

`ξ ≢ 0` is that the law is not the point mass at `0`.  A finite second moment
together with mean zero is `evar ρ < ∞`.

The reduction ends by upgrading a probability at least one half of explosion to
an almost sure one through `prop:01-law`, whose proof quotes the existence of a
bounded nonnegative solution of `Δf = δ_b - δ_a`; that cited input enters here
as the explicit hypothesis `hVF`, exactly as it does in `prop:01-law` itself.
-/
import RWRS.Support.Convexity

open MeasureTheory
open scoped ENNReal

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

-- The reduction constructs its own mean-zero bounded scenery out of the
-- symmetry of the law, so the assumed vanishing of the extended mean is not
-- referred to.
set_option linter.unusedVariables false in
-- FROZEN-STATEMENT-BEGIN
theorem RWRS.Frozen.convexityReduction (hVF : RWRS.External.VoltageFunction G)
    [Infinite V] (hG : G.Connected)
    (ν : Measure ℝ) (hν : IsProbabilityMeasure ν) (hmean : RWRS.extMean ν = 0)
    (hnz : ν ≠ Measure.dirac 0) (hsym : RWRS.IsSymmetric ν) (o : V) :
    ((∀ ρ : Measure ℝ, IsProbabilityMeasure ρ → RWRS.extMean ρ = 0 → 0 < RWRS.evar ρ →
        RWRS.evar ρ < ⊤ → ∀ᵐ ξ ∂(RWRS.iidLaw V ρ), RWRS.supStopValue G ξ o = ⊤) →
      ∀ᵐ ξ ∂(RWRS.iidLaw V ν), RWRS.supStopValue G ξ o = ⊤) ∧
    ((∀ ρ : Measure ℝ, IsProbabilityMeasure ρ → RWRS.extMean ρ = 0 → 0 < RWRS.evar ρ →
        RWRS.evar ρ < ⊤ → ∀ᵐ ξ ∂(RWRS.iidLaw V ρ), RWRS.supMeanPayoff G ξ o = ⊤) →
      ∀ᵐ ξ ∂(RWRS.iidLaw V ν), RWRS.supMeanPayoff G ξ o = ⊤)
-- FROZEN-STATEMENT-END
:= by
  haveI := hν
  refine ⟨fun hhyp => ?_, fun hhyp => ?_⟩
  · exact RWRS.Support.convexity_reduction_aux ν hnz hsym
      (fun ξ => RWRS.supStopValue G ξ o)
      (fun ξ η => RWRS.Support.supStopValue_midpoint_le ξ η o)
      (RWRS.Support.measurableSet_supStopValue_top hG o)
      (RWRS.Support.measure_supStopValue_top_zero_or_one hVF hG ν o) hhyp
  · exact RWRS.Support.convexity_reduction_aux ν hnz hsym
      (fun ξ => RWRS.supMeanPayoff G ξ o)
      (fun ξ η => RWRS.Support.supMeanPayoff_midpoint_le ξ η o)
      (RWRS.Support.measurableSet_supMeanPayoff_top' hG o)
      (RWRS.Support.measure_supMeanPayoff_top_zero_or_one hVF hG ν o) hhyp
