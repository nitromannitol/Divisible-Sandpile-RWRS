/-
Proposition 5.16 of `rwrs.tex`, frozen.  `rwrs.tex:1155-1165` (label
`prop:subcritical`):

  "Let $G=(V,E)$ be an infinite, locally finite, connected graph with degree
   bounded by $d$ and satisfying the spectral dimension bound
   (eq:return-bound) for some $d_s>0$ and $A<\infty$.  Let $(\xi(v))_{v\in V}$
   be i.i.d. and independent of the walk with $\E[\xi]\in[-\infty,0)$ and
   $\E[(\xi^+)^p]<\infty$ for some $p>1+2/d_s$.  Then for every
   $q\in[1,(p-1)(d_s/2\wedge1))$, $\sup_{x\in V}\E_x[(\sup_n S_n)^q]<\infty$.
   In particular, if $(p-1)(d_s/2\wedge1)>1$---which holds whenever $d_s<2$
   (under the stated moment condition) or $d_s\geq2$ and $p>2$---then
   $\sup_\tau\E_x[S_\tau\mid\xi]<\infty$ almost surely."

The expectations are joint over the scenery and the walk.  `sup_n S_n` and the
supremum over `x` are taken in `[0,∞]`, so finiteness is the assertion that the
value is not `⊤`.  The final supremum over bounded stopping times is likewise
in `[0,∞]`.

The vertex set carries measurable singletons, as it does in `lem:dyadic` and
`lem:good-walk`, which this proposition is assembled from.  `sup_n S_n` reads
the scenery along the trajectory, `(ξ, X) ↦ ξ(X_j)`, and that functional on the
product of the two spaces is measurable exactly when the singletons of the
vertex set are; with a coarser structure the left-hand side is a supremum of
lower integrals of functions that need not be measurable.  `ssec:notation`
supplies the instance in substance, the vertex set of a connected locally finite
graph being countable with the discrete structure.

The proof of the proposition applies `lem:fuk-nagaev`, whose own proof cites the
von Bahr--Esseen inequality and the Fuk--Nagaev inequality from outside the
paper, so the proposition carries those two as explicit hypotheses.
-/
import RWRS.Support.SubFinal

open MeasureTheory
open scoped ENNReal

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

set_option linter.unusedVariables false in
-- FROZEN-STATEMENT-BEGIN
theorem RWRS.Frozen.subcritical [Infinite V] [MeasurableSpace V] [MeasurableSingletonClass V]
    (hVBE : RWRS.External.VonBahrEsseen) (hFN : RWRS.External.FukNagaevTail)
    (hG : G.Connected)
    (d : ℕ) (hd : RWRS.BoundedDegree G d) (d_s A : ℝ) (hds : 0 < d_s)
    (hspec : RWRS.SpectralDimensionBound G d_s A)
    (ν : Measure ℝ) (hν : IsProbabilityMeasure ν) (hdet : RWRS.HasExtMean ν)
    (hmean : RWRS.extMean ν < 0)
    (p : ℝ) (hp : 1 + 2 / d_s < p) (hmom : RWRS.posMoment ν p ≠ ⊤) :
    (∀ q : ℝ, 1 ≤ q → q < (p - 1) * min (d_s / 2) 1 →
      (⨆ x : V, ∫⁻ z, RWRS.supPayoff G z.1 z.2 ^ q ∂(RWRS.jointLaw G ν x)) ≠ ⊤) ∧
    (1 < (p - 1) * min (d_s / 2) 1 →
      ∀ x : V, ∀ᵐ ξ ∂(RWRS.iidLaw V ν), RWRS.supStopValue G ξ x ≠ ⊤)
-- FROZEN-STATEMENT-END
:= by
  haveI := hν
  haveI : Countable V := RWRS.Support.countable_of_connected hG
  haveI : DecidableEq V := Classical.decEq V
  exact ⟨fun q hq1 hq2 => RWRS.Support.lintegral_supPayoff_rpow_ne_top hG hVBE hFN d hd hds
      hspec ν hmean hp hmom hq1 hq2,
    fun hgt x => RWRS.Support.ae_supStopValue_ne_top hG hVBE hFN d hd hds hspec ν hmean hp
      hmom hgt x⟩
