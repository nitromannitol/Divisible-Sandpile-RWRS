/-
Lemma 5.12 of `rwrs.tex`, frozen.  `rwrs.tex:1019-1034` (label
`lem:local-time`):

  "Let $G=(V,E)$ be an infinite, locally finite, connected graph on which the
   simple random walk $(X_n)_{n\geq0}$ satisfies the spectral dimension bound
   $\sup_{x\in V}\P_x(X_n=x)\leq An^{-d_s/2}$ for all $n\geq1$, for some
   $d_s>0$ and $A<\infty$.  Then for every $p\geq1$ and all $x\in V$ and
   $n\geq1$,
   $\sum_{v\in V}\E_x[L_n(v)^p]\leq C_p\cdot n^{1+(p-1)(1-d_s/2)}$ if $d_s<2$,
   $\leq C_p\cdot n(1+\log n)^{p-1}$ if $d_s=2$, and $\leq C_p\cdot n$ if
   $d_s>2$.  Here $C_p<\infty$ depends only on $p$, $d_s$, and $A$."

The constant depends only on `p`, `d_s` and `A`, so it is bound before the
graph, the vertex and the time.  The sum over `V` is taken in `[0,∞]`, so a
divergent sum is `⊤` and not a junk real.  Each expectation `E_x[L_n(v)^p]` is
a functional of the first `n` positions, so it is the finite-horizon walk
average `RWRS.walkExp`.
-/
import RWRS.Support.LocalTimeRegimes
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open scoped ENNReal

-- FROZEN-STATEMENT-BEGIN
theorem RWRS.Frozen.localTimeMoments (p d_s A : ℝ) (hp : 1 ≤ p) (hds : 0 < d_s) :
    ∃ Cp : ℝ, 0 < Cp ∧
      ∀ {V : Type} (G : SimpleGraph V) [G.LocallyFinite] [Infinite V], G.Connected →
        RWRS.SpectralDimensionBound G d_s A → ∀ (x : V) (n : ℕ), 1 ≤ n →
          (d_s < 2 →
            (∑' v : V, ENNReal.ofReal (RWRS.walkExp G n x
                (fun X => (RWRS.localTime n v X : ℝ) ^ p)))
              ≤ ENNReal.ofReal (Cp * (n : ℝ) ^ (1 + (p - 1) * (1 - d_s / 2)))) ∧
          (d_s = 2 →
            (∑' v : V, ENNReal.ofReal (RWRS.walkExp G n x
                (fun X => (RWRS.localTime n v X : ℝ) ^ p)))
              ≤ ENNReal.ofReal (Cp * (n : ℝ) * (1 + Real.log n) ^ (p - 1))) ∧
          (2 < d_s →
            (∑' v : V, ENNReal.ofReal (RWRS.walkExp G n x
                (fun X => (RWRS.localTime n v X : ℝ) ^ p)))
              ≤ ENNReal.ofReal (Cp * (n : ℝ)))
-- FROZEN-STATEMENT-END
:= RWRS.Support.localTimeMomentsAux p d_s A hp hds
