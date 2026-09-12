/-
Proposition 5.11 of `rwrs.tex`, frozen.  `rwrs.tex:997-999` (label
`prop:short-clock`):

  "Let $G=(V,E)$ be infinite, locally finite, and connected.  If for some
   $o\in V$ the total inverse-degree time $\sum_{v\in V}g(o,v)$ is finite, and
   if $(\xi(v))_{v\in V}$ are i.i.d. and independent of the walk with
   $\E[\xi^+]<\infty$, then $\E[\sup_\tau\E_o[S_\tau\mid\xi]]<\infty$, where the
   supremum is over bounded stopping times."

The inner supremum is taken in `[0,∞]` and the outer expectation is its
`lintegral` against the i.i.d. law, so both finiteness assertions are that a
value in `[0,∞]` is not `⊤`.
-/
import RWRS.Support.ShortClock

open MeasureTheory
open scoped ENNReal

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

-- FROZEN-STATEMENT-BEGIN
theorem RWRS.Frozen.shortClock [Infinite V] (hG : G.Connected) (o : V)
    (hclock : (∑' v : V, RWRS.green G o v) ≠ ⊤)
    (ν : Measure ℝ) (hν : IsProbabilityMeasure ν) (hpos : RWRS.posPart ν ≠ ⊤) :
    (∫⁻ ξ, RWRS.supStopValue G ξ o ∂(RWRS.iidLaw V ν)) ≠ ⊤
-- FROZEN-STATEMENT-END
:= by
  refine ne_top_of_le_ne_top ?_
    (MeasureTheory.lintegral_mono fun ξ =>
      RWRS.Support.supStopValue_le_green hG ξ o)
  rw [RWRS.Support.lintegral_green_bound hG o ν hν]
  exact ENNReal.mul_ne_top hclock hpos
