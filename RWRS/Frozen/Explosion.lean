/-
Theorem 1.2 of `rwrs.tex`, frozen.  `rwrs.tex:117-129` (label `thm:explosion`):

  "Let $G=(V,E)$ be an infinite, locally finite, connected graph with degree
   bounded by $d$, and let $(\sigma(v))_{v\in V}$ be i.i.d. random variables
   with $\E[\sigma(v)]=\mu$.
   (i) If $\mu\in(1,\infty]$, then $\P(\sigma\text{ stabilizes})=0$.
   (ii) If $\mu=1$ and either $\var(\sigma(v))\in(0,\infty)$, or
   $\sigma(v)\not\equiv1$ and $\sigma(v)-1$ is symmetric, then
   $\P(\sigma\text{ stabilizes})=0$."

`extMean ν` is the extended expectation of `ssec:notation` and `hdet` is the
paper's exclusion of the indeterminate case.  The symmetry of `σ(v)-1` is the
symmetry of the law of `σ` shifted by `1`.
-/
import RWRS.Setting
import RWRS.Support.OSShift
import RWRS.Frozen.ConvexityReduction
import RWRS.Frozen.Supercritical

open MeasureTheory

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

set_option linter.unusedVariables false in
-- FROZEN-STATEMENT-BEGIN
theorem RWRS.Frozen.explosion [Infinite V] [MeasurableSpace V]
    (hVF : RWRS.External.VoltageFunction G) (hG : G.Connected)
    (d : ℕ) (hd : RWRS.BoundedDegree G d) (ν : Measure ℝ) (hν : IsProbabilityMeasure ν)
    (hdet : RWRS.HasExtMean ν) :
    (1 < RWRS.extMean ν → RWRS.iidLaw V ν {σ : V → ℝ | RWRS.Stabilizes G σ} = 0) ∧
    (RWRS.extMean ν = 1 →
      ((0 < RWRS.evar ν ∧ RWRS.evar ν < ⊤) ∨
        (ν ≠ Measure.dirac 1 ∧ RWRS.IsSymmetric (ν.map (fun z => z - 1)))) →
      RWRS.iidLaw V ν {σ : V → ℝ | RWRS.Stabilizes G σ} = 0)
-- FROZEN-STATEMENT-END
:= by
  classical
  haveI := hν
  haveI : Countable V := RWRS.Support.countable_of_connected hG
  haveI : IsProbabilityMeasure (ν.map (fun z : ℝ => z - 1)) :=
    RWRS.Support.isProbabilityMeasure_map_sub_one
  have hES : RWRS.External.EfronStein V := RWRS.Support.efronStein V
  have hdeg : ∀ v : V, 0 < G.degree v := fun v => RWRS.Support.degree_pos hG v
  have hd0 : 0 < d := lt_of_lt_of_le (hdeg (Classical.arbitrary V)) (hd _)
  constructor
  · intro hmean
    refine RWRS.Support.measure_stabilizes_eq_zero hG ν (Classical.arbitrary V) ?_
    have hdet' : RWRS.HasExtMean (ν.map (fun z : ℝ => z - 1)) :=
      Or.inr (RWRS.Support.negPart_map_ne_top
        (RWRS.Support.negPart_ne_top_of_one_lt hdet hmean))
    have hpos := RWRS.Support.extMean_map_sub_one_pos hdet hmean
    have hmp := ((RWRS.Frozen.supercritical hG _ inferInstance hdet' hpos).2 d hd
      (Classical.arbitrary V)).2
    filter_upwards [hmp] with ξ hξ
    refine top_le_iff.1 ?_
    rw [← hξ]
    exact RWRS.Support.supMeanPayoff_le_supStopValue ξ _
  · intro hmean hcase
    refine RWRS.Support.measure_stabilizes_eq_zero hG ν (Classical.arbitrary V) ?_
    have hmean' : RWRS.extMean (ν.map (fun z : ℝ => z - 1)) = 0 :=
      RWRS.Support.extMean_map_sub_one_eq_zero hmean
    rcases hcase with ⟨hvar, hsq⟩ | ⟨hnz, hsym⟩
    · have hev := RWRS.Support.evar_map_sub_one hsq
      exact RWRS.Support.explosion_of_mean_zero hES hVF hG d hd0 hd _ inferInstance hmean'
        (by rw [hev]; exact hvar) (by rw [hev]; exact hsq) _
    · obtain ⟨o, ho⟩ := RWRS.Support.exists_vertex_explosion hES hVF hG d hd0 hd
      have hconv := (RWRS.Frozen.convexityReduction hVF hG _ inferInstance hmean'
        (RWRS.Support.map_sub_one_ne_dirac hnz) hsym o).1
        (fun ρ hρ h0 hv hs => ho ρ hρ h0 hv hs)
      filter_upwards [hconv] with ξ hξ
      exact RWRS.Support.supStopValue_top_everywhere hG hξ _
