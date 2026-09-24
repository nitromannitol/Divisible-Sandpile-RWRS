/-
Lemma 5.14 of `rwrs.tex`, frozen.  `rwrs.tex:1102-1111` (label `lem:dyadic`):

  "Let $G=(V,E)$ be an infinite, locally finite, connected graph with degree
   bounded by $d$, and let $(\xi(v))_{v\in V}$ be i.i.d. and independent of the
   walk with $\E[\xi]\in(-\infty,0)$ and $\E[|\xi|^p]<\infty$ for some $p\geq1$.
   For $k\geq0$ let
   $Y_k\coloneqq(\max_{2^k\leq n<2^{k+1}}W_n-\frac{|\E[\xi]|}{d}2^k)^+$.
   Then for every $q\geq1$ and every $x\in V$,
   $\E_x[(\sup_n S_n)^q]\leq\sum_{k\geq0}\E_x[Y_k^q]$."

Both expectations are joint over the scenery and the walk, as `ssec:notation`
fixes.  `sup_n S_n` is taken in `[0,∞]`, where it is at least `S_0 = 0`, and the
sum over `k` is an `[0,∞]`-sum, so the inequality carries no junk.  The mean of
`ξ` is the real number `m`, which the hypothesis `E[ξ]∈(-∞,0)` provides.

The vertex set carries measurable singletons.  `ssec:notation` fixes a
connected locally finite graph, whose vertex set is countable and carries the
discrete structure; the instance is what makes the scenery read along a
trajectory, `(ξ, X) ↦ ξ(X_k)`, a measurable function on the product of the two
spaces, and without it the right-hand side is a sum of lower integrals of
functions that need not be measurable, which is not what the paper's sum of
expectations means.
-/
import RWRS.Support.DyadicSup
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

open MeasureTheory
open scoped ENNReal

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

-- The proof uses neither the moment hypothesis nor the exponent `p` carrying
-- it, the block bound being pathwise, so those two binders of the statement are
-- not referred to.
set_option linter.unusedVariables false in
-- FROZEN-STATEMENT-BEGIN
theorem RWRS.Frozen.dyadic [Infinite V] [MeasurableSpace V] [MeasurableSingletonClass V]
    (hG : G.Connected)
    (d : ℕ) (hd : RWRS.BoundedDegree G d) (ν : Measure ℝ) (hν : IsProbabilityMeasure ν)
    (m : ℝ) (hm : RWRS.extMean ν = (m : EReal)) (hmneg : m < 0)
    (p : ℝ) (hp : 1 ≤ p) (hmom : RWRS.absMoment ν p ≠ ⊤)
    (q : ℝ) (hq : 1 ≤ q) (x : V) :
    (∫⁻ z, RWRS.supPayoff G z.1 z.2 ^ q ∂(RWRS.jointLaw G ν x))
      ≤ ∑' k : ℕ, ∫⁻ z, ENNReal.ofReal (RWRS.dyadicY G z.1 m d k z.2 ^ q)
          ∂(RWRS.jointLaw G ν x)
-- FROZEN-STATEMENT-END
:= by
  haveI := RWRS.Support.countable_of_connected hG
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le zero_lt_one hq
  have hpt : ∀ z : (V → ℝ) × (ℕ → V),
      RWRS.supPayoff G z.1 z.2 ^ q
        ≤ ∑' k : ℕ, ENNReal.ofReal (RWRS.dyadicY G z.1 m d k z.2 ^ q) := fun z =>
    RWRS.Support.supPayoff_rpow_le hG hd z.1 hmneg hq0 z.2
  calc (∫⁻ z, RWRS.supPayoff G z.1 z.2 ^ q ∂(RWRS.jointLaw G ν x))
      ≤ ∫⁻ z, ∑' k : ℕ, ENNReal.ofReal (RWRS.dyadicY G z.1 m d k z.2 ^ q)
          ∂(RWRS.jointLaw G ν x) := lintegral_mono hpt
    _ = ∑' k : ℕ, ∫⁻ z, ENNReal.ofReal (RWRS.dyadicY G z.1 m d k z.2 ^ q)
          ∂(RWRS.jointLaw G ν x) :=
        lintegral_tsum fun k =>
          (RWRS.Support.measurable_dyadicY_rpow m d k hq0.le).aemeasurable
