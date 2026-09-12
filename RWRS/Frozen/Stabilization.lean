/-
Theorem 1.3 of `rwrs.tex`, frozen.  `rwrs.tex:131-142` (label `thm:stab`):

  "Let $G=(V,E)$ be an infinite, locally finite, connected graph with degree
   bounded by $d$, and let $(\sigma(v))_{v\in V}$ be i.i.d. random variables
   with $\E[\sigma(v)]=\mu\in[-\infty,1)$.
   (i) If $\E[(\sigma(v)^+)^p]<\infty$ for some $p>3$, then
   $\sup_{v\in V}\E[u_\infty(v)^q]<\infty$ for every $q\in[1,(p-1)/2)$; in
   particular $\P(\sigma\text{ stabilizes})=1$.
   (ii) If $|B(o,r)|\leq Cr^{d_f}$ for some $o\in V$, some $C>0$, some
   $d_f\geq1$, and all $r\geq1$, and if $\E[(\sigma(v)^+)^p]<\infty$ for some
   $p>d_f$, then $\P(\sigma\text{ stabilizes})=1$."

`u_∞(v)` is valued in `[0,∞]` and its `q`-th moment is the `lintegral` of its
`q`-th power, so the assertion of finiteness is that the value is not `⊤` and
no junk real intervenes.  The volume hypothesis compares the `encard` of the
closed ball, in `[0,∞]`, with `C r^{d_f}`.

The vertex set carries the discrete measurable structure, as `ssec:notation`
supplies it in substance and as `prop:subcritical`, `lem:dyadic` and
`lem:good-walk` already carry it.  The von Bahr--Esseen and Fuk--Nagaev
inequalities, which the proof of `lem:fuk-nagaev` quotes from outside the paper
and which part (i) reaches through `prop:subcritical`, enter as explicit
hypotheses.
-/
import RWRS.Support.SubStabPoly
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

open MeasureTheory
open scoped ENNReal

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

-- The convention excluding the indeterminate mean is carried but not referred
-- to: the mean being below one already forces the negative part to be finite or
-- the positive part to be, which is what the two parts use.
set_option linter.unusedVariables false in
-- FROZEN-STATEMENT-BEGIN
theorem RWRS.Frozen.stabilization [Infinite V] [MeasurableSpace V]
    [MeasurableSingletonClass V]
    (hHK : RWRS.External.HeatKernelBoundedDegree G) (hCV : RWRS.External.CarneVaropoulos G)
    (hVBE : RWRS.External.VonBahrEsseen) (hFNt : RWRS.External.FukNagaevTail)
    (hG : G.Connected)
    (d : ℕ) (hd : RWRS.BoundedDegree G d) (ν : Measure ℝ) (hν : IsProbabilityMeasure ν)
    (hdet : RWRS.HasExtMean ν) (hmean : RWRS.extMean ν < 1) :
    (∀ p : ℝ, 3 < p → RWRS.posMoment ν p ≠ ⊤ →
      (∀ q : ℝ, 1 ≤ q → q < (p - 1) / 2 →
        (⨆ v : V, ∫⁻ σ, RWRS.odometerLimit G σ v ^ q ∂(RWRS.iidLaw V ν)) ≠ ⊤) ∧
      RWRS.iidLaw V ν {σ : V → ℝ | RWRS.Stabilizes G σ} = 1) ∧
    (∀ (o : V) (C d_f : ℝ), 0 < C → 1 ≤ d_f → RWRS.VolumeGrowthUpper G o C d_f →
      ∀ p : ℝ, d_f < p → RWRS.posMoment ν p ≠ ⊤ →
        RWRS.iidLaw V ν {σ : V → ℝ | RWRS.Stabilizes G σ} = 1)
-- FROZEN-STATEMENT-END
:= by
  classical
  haveI := hν
  haveI : Countable V := RWRS.Support.countable_of_connected hG
  haveI : DecidableEq V := Classical.decEq V
  have hdeg : ∀ v : V, 1 ≤ G.degree v := fun v => RWRS.Support.degree_pos_of_connected hG v
  have hd1 : 1 ≤ d := le_trans (hdeg (Classical.arbitrary V)) (hd _)
  obtain ⟨A, hA0, hsp⟩ := hHK d hd1 hd
  exact ⟨fun p hp hmom =>
      ⟨fun q hq1 hq2 => RWRS.Support.lintegral_odometerLimit_rpow_ne_top hG hVBE hFNt d hd hsp
          ν hmean hp hmom hq1 hq2,
        RWRS.Support.measure_stabilizes_eq_one_part_one hG hVBE hFNt d hd hsp ν hmean hp hmom⟩,
    fun o C d_f hC hdf hH1 p hp hmom =>
      RWRS.Support.measure_stabilizes_eq_one_part_two hG hHK hCV d hd ν hmean o hC hdf hH1
        hp hmom⟩
