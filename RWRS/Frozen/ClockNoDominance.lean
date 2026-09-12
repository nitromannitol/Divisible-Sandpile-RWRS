/-
Lemma 5.1 of `rwrs.tex`, frozen.  `rwrs.tex:531-538` (label
`lem:clock-no-dom`):

  "Let $G$ be infinite, locally finite, and connected, and fix $x\in V$.  If
   $A_n(x)\to\infty$, then $\frac{\sup_v g_n(x,v)}{A_n(x)}\to0$ and hence
   $\frac{\Sigma_n(x)}{A_n(x)^2}\to0$."

The supremum `sup_v g_n(x,v)` and the fluctuation scale `Σ_n(x)` are taken in
`[0,∞]`, so neither is a junk real; the quotients are `[0,∞]`-quotients, and
the hypothesis `A_n(x)→∞` makes the denominators eventually positive.
-/
import RWRS.External.HeatKernelVanishing
import RWRS.Support.ClockRatio

open Filter Topology

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

-- The proof below reaches the conclusion from the escape probability of the
-- walk and does not use the assumed vanishing of the return probability, so
-- that hypothesis of the statement is not referred to.
set_option linter.unusedVariables false in
-- FROZEN-STATEMENT-BEGIN
theorem RWRS.Frozen.clockNoDominance (hHKV : RWRS.External.HeatKernelVanishing G)
    [Infinite V] (hG : G.Connected) (x : V)
    (hA : Tendsto (fun n : ℕ => RWRS.clock G n x) atTop atTop) :
    Tendsto (fun n : ℕ => RWRS.supGreenTime G n x / ENNReal.ofReal (RWRS.clock G n x))
        atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => RWRS.fluct G n x / (ENNReal.ofReal (RWRS.clock G n x)) ^ 2)
        atTop (𝓝 0)
-- FROZEN-STATEMENT-END
:=
  ⟨RWRS.Support.tendsto_supGreenTime_div_clock hG x hA,
    RWRS.Support.tendsto_fluct_div_clock_sq hG x hA⟩
