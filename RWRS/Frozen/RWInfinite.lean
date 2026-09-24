/-
Corollary 3.5 of `rwrs.tex`, frozen.  `rwrs.tex:473-478` (label
`cor:RW-infinite`):

  "For every configuration $\sigma$ and every $x\in V$,
   $u_\infty(x)=\sup_{\tau\ \mathrm{bounded}}\E_x[S_\tau\mid\sigma]$."

Both sides are read in `[0,∞]`: `u_∞(x)` is the supremum of the nondecreasing
sequence `u_n(x)`, and the right-hand side is the supremum over all `n` of the
values `E_x[S_τ]` of the stopping rules bounded by `n`, each pushed into
`[0,∞]` by `ENNReal.ofReal`.  The rule `τ = 0` has value `0`, so the negative
values that `ENNReal.ofReal` sends to `0` do not change the supremum.  `hG` is
the standing assumption of Section 3.
-/
import RWRS.Support.Representation

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

-- FROZEN-STATEMENT-BEGIN
theorem RWRS.Frozen.rwInfinite [Infinite V] (hG : G.Connected) (σ : V → ℝ) (x : V) :
    RWRS.odometerLimit G σ x = RWRS.supStopValue G (RWRS.excess σ) x
-- FROZEN-STATEMENT-END
:= by
  refine le_antisymm (iSup_le fun n => ?_) (iSup_le fun n => iSup_le fun a => iSup_le fun ha => ?_)
  · exact le_iSup_of_le n (le_iSup_of_le (RWRS.odometer G σ n x)
      (le_iSup_of_le (RWRS.Support.odometer_isLUB hG σ n x).2 le_rfl))
  · exact le_iSup_of_le n
      (ENNReal.ofReal_le_ofReal ((RWRS.Support.odometer_isLUB hG σ n x).1 a ha))
