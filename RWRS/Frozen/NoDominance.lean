/-
Lemma 5.4 of `rwrs.tex`, frozen.  `rwrs.tex:629-634` (label
`lem:no-dominance`):

  "Let $G=(V,E)$ be an infinite, locally finite, connected graph, and fix
   $o\in V$.  If $\Sigma_n(o)\to\infty$, then
   $\max_v g_n(o,v)^2/\Sigma_n(o)\to0$ as $n\to\infty$."

The maximum is the supremum of the nonnegative numbers `g_n(o,v)`, taken in
`[0,∞]`, and squaring commutes with it; the quotient is the `[0,∞]`-quotient.

The divergence `Σ_n(o) → ∞` is convergence to `⊤` in the order topology
of `[0,∞]`, written `Tendsto Σ atTop (𝓝 ⊤)`. It means that every finite
threshold is eventually exceeded.
-/
import RWRS.External.HeatKernelVanishing
import RWRS.Support.ClockRatio
import RWRS.Support.ShortClock

open Filter Topology

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

-- The proof below reaches the conclusion from the escape probability of the
-- walk and the first-visit comparison, and does not use the assumed vanishing
-- of the return probability, so that hypothesis of the statement is not
-- referred to.
set_option linter.unusedVariables false in
-- FROZEN-STATEMENT-BEGIN
theorem RWRS.Frozen.noDominance (hHKV : RWRS.External.HeatKernelVanishing G)
    [Infinite V] (hG : G.Connected) (o : V)
    (hSigma : Tendsto (fun n : ℕ => RWRS.fluct G n o) atTop (𝓝 ⊤)) :
    Tendsto (fun n : ℕ => RWRS.supGreenTime G n o ^ 2 / RWRS.fluct G n o) atTop (𝓝 0)
-- FROZEN-STATEMENT-END
:= by
  classical
  -- The divergence of the fluctuation scale, read on the real sum `Σ_n(o)`.
  have hS : Tendsto (fun n : ℕ => RWRS.Support.sumSq G n o) atTop atTop := by
    refine tendsto_atTop.2 fun M => ?_
    have h0 : (0 : ℝ) ≤ max M 0 := le_max_right _ _
    filter_upwards [ENNReal.tendsto_nhds_top_iff_nnreal.1 hSigma
      (Real.toNNReal (max M 0))] with n hn
    have hn' : ENNReal.ofReal (max M 0) < ENNReal.ofReal (RWRS.Support.sumSq G n o) := by
      rw [← RWRS.Support.fluct_eq_ofReal_sumSq]; exact hn
    exact ((le_max_left M 0).trans
      ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg h0).1 hn').le)
  -- The real form of the statement, proved in the support module.
  have hg := RWRS.Support.tendsto_greenTime_sq_div_sumSq hG o hS
  have hbound : ∀ᶠ n : ℕ in atTop,
      RWRS.supGreenTime G n o ^ 2 / RWRS.fluct G n o
        ≤ ENNReal.ofReal (RWRS.greenTime G n o o ^ 2 / RWRS.Support.sumSq G n o) := by
    filter_upwards [hS.eventually_gt_atTop 0] with n hn
    have hgn : 0 ≤ RWRS.greenTime G n o o := RWRS.Support.greenTime_nonneg n o o
    have hnum : RWRS.supGreenTime G n o ^ 2
        ≤ ENNReal.ofReal (RWRS.greenTime G n o o ^ 2) := by
      rw [ENNReal.ofReal_pow hgn]
      exact pow_le_pow_left' (RWRS.Support.supGreenTime_le hG n o) 2
    calc RWRS.supGreenTime G n o ^ 2 / RWRS.fluct G n o
        ≤ ENNReal.ofReal (RWRS.greenTime G n o o ^ 2) / RWRS.fluct G n o :=
          ENNReal.div_le_div_right hnum _
      _ = ENNReal.ofReal (RWRS.greenTime G n o o ^ 2)
            / ENNReal.ofReal (RWRS.Support.sumSq G n o) := by
          rw [RWRS.Support.fluct_eq_ofReal_sumSq]
      _ = ENNReal.ofReal (RWRS.greenTime G n o o ^ 2 / RWRS.Support.sumSq G n o) :=
          (ENNReal.ofReal_div_of_pos hn).symm
  have hlim : Tendsto
      (fun n : ℕ => ENNReal.ofReal (RWRS.greenTime G n o o ^ 2 / RWRS.Support.sumSq G n o))
      atTop (𝓝 0) := by
    have := (ENNReal.continuous_ofReal.tendsto 0).comp hg
    simpa [Function.comp_def] using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => zero_le) hbound
