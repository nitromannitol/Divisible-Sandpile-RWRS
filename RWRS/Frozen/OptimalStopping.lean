/-
Theorem 1.1 of `rwrs.tex`, frozen.  `rwrs.tex:94-115` (label `thm:OS`):

  "Let $G=(V,E)$ be an infinite, locally finite, connected graph with degree
   bounded by $d$, let $(X_n)_{n\geq0}$ be simple random walk on $G$, let
   $(\xi(v))_{v\in V}$ be i.i.d. and independent of the walk, and
   $S_n\coloneqq\sum_{k=0}^{n-1}\xi(X_k)/\deg(X_k)$.
   (i) (Explosion) If $\E[\xi]\in(0,\infty]$, then $\sup_n\E_x[S_n\mid\xi]=\infty$
   almost surely for every $x\in V$.
   (ii) (Explosion) Suppose that $\E[\xi]=0$ and either $\var(\xi)\in(0,\infty)$,
   or $\xi\not\equiv0$ and symmetric.  Then $\sup_\tau\E_x[S_\tau\mid\xi]=\infty$
   almost surely for every $x\in V$, where the supremum is over bounded stopping
   times; if $G$ is not doubly transient, then $\sup_n\E_x[S_n\mid\xi]=\infty$
   almost surely for every $x\in V$.
   (iii) (Stabilization) Suppose $\E[\xi]\in[-\infty,0)$ and
   $\E[(\xi^+)^p]<\infty$ for some $p>3$.  Then $\E_x[(\sup_n S_n)^q]<\infty$
   for every $q\in[1,(p-1)/2)$ and every $x\in V$."

The extended mean of `ssec:notation` is `extMean ν`, an `EReal`; `hν` is the
paper's exclusion of the indeterminate case.  So `E[ξ]∈(0,∞]` is `0 < extMean ν`
and `E[ξ]∈[-∞,0)` is `extMean ν < 0`.  The two suprema live in `[0,∞]`, so
`= ∞` is a value.  In (iii) the expectation `E_x` is the joint one over the
scenery and the walk, as `ssec:notation` fixes, and `sup_n S_n` is taken in
`[0,∞]`; it is at least `S_0 = 0`, so nothing is lost.  The independence of the
walk and the scenery is the product structure of `jointLaw`.
-/
import RWRS.Setting
import RWRS.Support.OSParts
import RWRS.Support.OSSub
import RWRS.Frozen.ConvexityReduction
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

open MeasureTheory
open scoped ENNReal

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

set_option linter.unusedVariables false in
-- FROZEN-STATEMENT-BEGIN
theorem RWRS.Frozen.optimalStopping [Infinite V] [MeasurableSpace V]
    [MeasurableSingletonClass V]
    (hVBE : RWRS.External.VonBahrEsseen) (hFN : RWRS.External.FukNagaevTail)
    (hHK : RWRS.External.HeatKernelBoundedDegree G)
    (hVF : RWRS.External.VoltageFunction G) (hG : G.Connected)
    (d : ℕ) (hd : RWRS.BoundedDegree G d) (ν : Measure ℝ) (hν : IsProbabilityMeasure ν)
    (hdet : RWRS.HasExtMean ν) :
    (0 < RWRS.extMean ν →
      ∀ x : V, ∀ᵐ ξ ∂(RWRS.iidLaw V ν), RWRS.supMeanPayoff G ξ x = ⊤) ∧
    (RWRS.extMean ν = 0 →
      ((0 < RWRS.evar ν ∧ RWRS.evar ν < ⊤) ∨ (ν ≠ Measure.dirac 0 ∧ RWRS.IsSymmetric ν)) →
      (∀ x : V, ∀ᵐ ξ ∂(RWRS.iidLaw V ν), RWRS.supStopValue G ξ x = ⊤) ∧
      (¬ RWRS.DoublyTransient G →
        ∀ x : V, ∀ᵐ ξ ∂(RWRS.iidLaw V ν), RWRS.supMeanPayoff G ξ x = ⊤)) ∧
    (RWRS.extMean ν < 0 → ∀ p : ℝ, 3 < p → RWRS.posMoment ν p ≠ ⊤ →
      ∀ q : ℝ, 1 ≤ q → q < (p - 1) / 2 → ∀ x : V,
        (∫⁻ z, RWRS.supPayoff G z.1 z.2 ^ q ∂(RWRS.jointLaw G ν x)) ≠ ⊤)
-- FROZEN-STATEMENT-END
:= by
  classical
  haveI := hν
  haveI : Countable V := RWRS.Support.countable_of_connected hG
  have hES : RWRS.External.EfronStein V := RWRS.Support.efronStein V
  have hdeg : ∀ v : V, 0 < G.degree v := fun v => RWRS.Support.degree_pos hG v
  have hd0 : 0 < d := lt_of_lt_of_le (hdeg (Classical.arbitrary V)) (hd _)
  refine ⟨?_, ?_, ?_⟩
  · intro hmean x
    exact ((RWRS.Frozen.supercritical hG ν hν hdet hmean).2 d hd x).2
  · intro hmean hcase
    constructor
    · intro x
      rcases hcase with ⟨hvar, hsq⟩ | ⟨hnz, hsym⟩
      · exact RWRS.Support.explosion_of_mean_zero hES hVF hG d hd0 hd ν hν hmean hvar hsq x
      · obtain ⟨o, ho⟩ := RWRS.Support.exists_vertex_explosion hES hVF hG d hd0 hd
        have hconv := (RWRS.Frozen.convexityReduction hVF hG ν hν hmean hnz hsym o).1
          (fun ρ hρ h0 hv hs => ho ρ hρ h0 hv hs)
        filter_upwards [hconv] with ξ hξ
        exact RWRS.Support.supStopValue_top_everywhere hG hξ x
    · intro hndt x
      have hfl := RWRS.Support.tendsto_fluct_top_of_not_doublyTransient hG hdeg hndt x
      rcases hcase with ⟨hvar, hsq⟩ | ⟨hnz, hsym⟩
      · obtain ⟨c₁, c₂, _, _, hcrit⟩ := (RWRS.Frozen.critical hES hVF hG ν hν hmean hvar hsq).2
        exact (hcrit x hfl).2
      · refine (RWRS.Frozen.convexityReduction hVF hG ν hν hmean hnz hsym x).2
          (fun ρ hρ h0 hv hs => ?_)
        obtain ⟨c₁, c₂, _, _, hcrit⟩ := (RWRS.Frozen.critical hES hVF hG ρ hρ h0 hv hs).2
        exact (hcrit x hfl).2
  · intro hmean p hp hmom q hq1 hq2 x
    exact RWRS.Support.lintegral_supPayoff_rpow_ne_top_boundedDegree hVBE hFN hHK hG d hd
      ν hν hdet hmean p hp hmom q hq1 hq2 x
