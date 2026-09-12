/-
Lemma 6.2 of `rwrs.tex`, frozen.  `rwrs.tex:1385-1398` (label
`lem:moment-sharpness`):

  "Let $G=(V,E)$ be an infinite, locally finite, connected graph.  Assume:
   (A1) (Upper heat kernel) $\sup_{x\in V}\P_x(X_n=x)/\deg(x)\leq An^{-\alpha}$
   for all $n\geq1$, for some $\alpha>0$ and $A<\infty$.
   (A2) (Local time lower bound) There exist $d_w\geq2$ and $a>0$ such that
   $\E_o[L_n(v)]/\deg(v)\geq an^{1-\alpha}$ for every $v\in B(o,n^{1/d_w})$ and
   all sufficiently large $n$.
   (A3) (Volume lower bound) $|B(o,r)|\geq c_{\mathrm{vol}}r^{d_f}$ for all
   $r\geq1$, for some $d_f>0$ and $c_{\mathrm{vol}}>0$.
   Let $(\sigma(v))_{v\in V}$ be i.i.d. with $\E[\sigma(v)]\in(-\infty,\infty]$.
   If $\E[(\sigma(v)^+)^{(d_f+d_w)/(d_w\alpha)}]=\infty$, then
   $\E[u_\infty(o;\sigma)]=\infty$."

The mean condition `E[σ]∈(-∞,∞]` excludes `-∞` and, with `hdet`, the
indeterminate case of `ssec:notation`.  The ball of real radius `n^{1/d_w}` is
the closed ball of integer radius `⌊n^{1/d_w}⌋`, which contains the same
vertices.  Both moments are `[0,∞]`-valued, so `= ∞` is a value.
-/
import RWRS.Support.SharpFinal
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

open MeasureTheory
open scoped ENNReal

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

-- The proof splits on whether the mean of the positive part is infinite.  In
-- the infinite case the constant rule already gives the conclusion; in the
-- finite case the strict lower bound on the extended mean forces the negative
-- part to be finite as well.  Either way the standing exclusion of the
-- indeterminate case is not referred to.
set_option linter.unusedVariables false in
-- FROZEN-STATEMENT-BEGIN
theorem RWRS.Frozen.momentSharpness [Infinite V] (hG : G.Connected) (o : V)
    (α A : ℝ) (hα : 0 < α)
    (hA1 : ∀ (x : V) (n : ℕ), 1 ≤ n → RWRS.heat G n x x / G.degree x ≤ A * (n : ℝ) ^ (-α))
    (d_w a : ℝ) (hdw : 2 ≤ d_w) (ha : 0 < a)
    (hA2 : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ v ∈ RWRS.closedBall G o ⌊(n : ℝ) ^ (1 / d_w)⌋₊,
      a * (n : ℝ) ^ (1 - α) ≤ RWRS.greenTime G n o v)
    (c_vol d_f : ℝ) (hdf : 0 < d_f) (hcv : 0 < c_vol)
    (hA3 : RWRS.VolumeGrowthLower G o c_vol d_f)
    (ν : Measure ℝ) (hν : IsProbabilityMeasure ν) (hdet : RWRS.HasExtMean ν)
    (hmean : (⊥ : EReal) < RWRS.extMean ν)
    (hmom : RWRS.posMoment ν ((d_f + d_w) / (d_w * α)) = ⊤) :
    (∫⁻ σ, RWRS.odometerLimit G σ o ∂(RWRS.iidLaw V ν)) = ⊤
-- FROZEN-STATEMENT-END
:= by
  haveI := hν
  exact RWRS.Support.momentSharpness_aux hG o hα hA1 hdw ha hA2 hdf hcv hA3 hmean hmom
