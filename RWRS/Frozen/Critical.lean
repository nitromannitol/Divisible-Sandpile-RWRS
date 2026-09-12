/-
Proposition 5.6 of `rwrs.tex`, frozen.  `rwrs.tex:664-687` (label
`prop:critical`):

  "Let $G=(V,E)$ be an infinite, locally finite, connected graph, let
   $(X_n)_{n\geq0}$ be simple random walk on $G$, and let $(\xi(v))_{v\in V}$
   be i.i.d. and independent of the walk with $\E[\xi]=0$, $\var(\xi)>0$, and
   $\E[\xi^2]<\infty$.  Let $u_n(o)\coloneqq\sup_{\tau\leq n}\E_o[S_\tau\mid\xi]$.
   (a) (Variance bound) For every $o\in V$ and $n\geq1$,
   $\var(u_n(o))\leq\var(\xi)\Sigma_n(o)$.
   (b) (Explosion) If $\Sigma_n(o)\to\infty$, then there exist $c_1,c_2>0$
   depending only on $\xi$ such that
   $\P(u_n(o)\geq c_1\sqrt{\Sigma_n(o)})\geq c_2$, for all $n$ sufficiently
   large.  In particular, $\sup_n\E_o[S_n\mid\xi]=\infty$ almost surely."

`u_n(o)` is `RWRS.value G ξ n o`, the supremum over stopping times bounded by
`n`, which is the paper's definition.  The variance of a real random variable
is taken in `[0,∞]` as `evariance`, so `var(ξ)Σ_n(o)` is an `[0,∞]` product and
no junk real appears.  In (b) the constants depend only on the law of `ξ`, so
they are bound before the vertex `o`.  The square root is the power `1/2` in
`[0,∞]`.

The divergence `Σ_n(o) → ∞` is convergence to `⊤` in the order topology
of `[0,∞]`, written `Tendsto Σ atTop (𝓝 ⊤)`. It means that every finite
threshold is eventually exceeded.

The proof of (b) ends by upgrading a positive probability of explosion to an
almost sure one through `prop:01-law`, whose proof quotes the existence of a
bounded nonnegative solution of `Δf = δ_b - δ_a`; that cited input enters here
as the explicit hypothesis `hVF`, exactly as it does in `prop:01-law` itself.
-/
import RWRS.Support.Critical

open MeasureTheory Filter Topology
open scoped ENNReal

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

-- FROZEN-STATEMENT-BEGIN
theorem RWRS.Frozen.critical (hES : RWRS.External.EfronStein V)
    (hVF : RWRS.External.VoltageFunction G) [Infinite V] (hG : G.Connected)
    (ν : Measure ℝ) (hν : IsProbabilityMeasure ν) (hmean : RWRS.extMean ν = 0)
    (hvar : 0 < RWRS.evar ν) (hsq : RWRS.evar ν < ⊤) :
    (∀ (o : V) (n : ℕ), 1 ≤ n →
      ProbabilityTheory.evariance (fun ξ : V → ℝ => RWRS.value G ξ n o) (RWRS.iidLaw V ν)
        ≤ RWRS.evar ν * RWRS.fluct G n o) ∧
    (∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ o : V,
      Tendsto (fun n : ℕ => RWRS.fluct G n o) atTop (𝓝 ⊤) →
        (∃ N : ℕ, ∀ n : ℕ, N ≤ n →
          ENNReal.ofReal c₂ ≤ RWRS.iidLaw V ν
            {ξ : V → ℝ | ENNReal.ofReal c₁ * RWRS.fluct G n o ^ (2⁻¹ : ℝ)
              ≤ ENNReal.ofReal (RWRS.value G ξ n o)}) ∧
        ∀ᵐ ξ ∂(RWRS.iidLaw V ν), RWRS.supMeanPayoff G ξ o = ⊤)
-- FROZEN-STATEMENT-END
:= by
  constructor
  · intro o n _
    exact RWRS.Support.evariance_value_le hES hG hν hmean hsq n o
  · obtain ⟨c₁, c₂, hc₁, hc₂, hmain⟩ :=
      RWRS.Support.exists_critical_constants hES hG hν hmean hvar hsq
    exact ⟨c₁, c₂, hc₁, hc₂, fun o hSigma =>
      ⟨hmain o hSigma,
        RWRS.Support.ae_supMeanPayoff_top_critical hVF hG hν hmean hvar hsq o hSigma⟩⟩
