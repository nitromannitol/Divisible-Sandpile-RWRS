/-
Proposition 5.2 of `rwrs.tex`, frozen.  `rwrs.tex:554-558` (label
`prop:supercritical`):

  "Let $G=(V,E)$ be an infinite, locally finite, connected graph, let
   $(X_n)_{n\geq0}$ be simple random walk on $G$, and let $(\xi(v))_{v\in V}$
   be i.i.d. and independent of the walk with $\E[\xi]\in(0,\infty]$.  If
   $A_n(x)\to\infty$ for some $x\in V$, then $\sup_n\E_x[S_n\mid\xi]=\infty$
   almost surely.  In particular, if the degree is bounded by $d$, then
   $A_n(x)\geq n/d\to\infty$, so the conclusion holds on every infinite
   bounded-degree graph."

`E[ξ]∈(0,∞]` is `0 < extMean ν` under the exclusion `hdet` of the
indeterminate case of `ssec:notation`.
-/
import RWRS.Support.Explosion

open MeasureTheory Filter Topology

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

-- The proof reaches the conclusion from the positivity of the extended mean,
-- which already excludes the indeterminate case, so the standing exclusion is
-- not referred to.
set_option linter.unusedVariables false in
-- FROZEN-STATEMENT-BEGIN
theorem RWRS.Frozen.supercritical [Infinite V] (hG : G.Connected)
    (ν : Measure ℝ) (hν : IsProbabilityMeasure ν) (hdet : RWRS.HasExtMean ν)
    (hmean : 0 < RWRS.extMean ν) :
    (∀ x : V, Tendsto (fun n : ℕ => RWRS.clock G n x) atTop atTop →
      ∀ᵐ ξ ∂(RWRS.iidLaw V ν), RWRS.supMeanPayoff G ξ x = ⊤) ∧
    (∀ d : ℕ, RWRS.BoundedDegree G d → ∀ x : V,
      (∀ n : ℕ, (n : ℝ) / d ≤ RWRS.clock G n x) ∧
        ∀ᵐ ξ ∂(RWRS.iidLaw V ν), RWRS.supMeanPayoff G ξ x = ⊤)
-- FROZEN-STATEMENT-END
:= by
  haveI := hν
  refine ⟨fun x hA => RWRS.Support.ae_supMeanPayoff_top hG x hA ν hmean, fun d hd x => ?_⟩
  exact ⟨fun n => RWRS.Support.clock_ge_of_boundedDegree hG hd n x,
    RWRS.Support.ae_supMeanPayoff_top hG x
      (RWRS.Support.tendsto_clock_of_boundedDegree hG hd x) ν hmean⟩
