/-
Theorem 6.8 of `rwrs.tex`, frozen.  `rwrs.tex:1575-1577` (label
`thm:transient-nonstab`):

  "For every $p\in(0,3)$, there exists a transient bounded-degree graph $G$
   such that for every $\mu<1$, there is an i.i.d. law bounded from below with
   $\E[\sigma]=\mu$ and $\E[|\sigma-\mu|^p]<\infty$ for which
   $u_\infty(o)=\infty$ almost surely.  In particular, the divisible sandpile
   does not stabilize."

The graph is infinite and connected, which the words "transient bounded-degree
graph" carry in this paper (`ssec:notation`).  Transience is `g(o,o) < ∞`,
"bounded from below" is an almost sure lower bound for the marginal, and
`u_∞(o) = ∞` is the `[0,∞]`-value `⊤`.
-/
import RWRS.Support.CombOdometer
import RWRS.Support.ProbHelpers
import RWRS.Support.Explosion
import RWRS.Support.Pareto
import RWRS.Frozen.CombEstimates
import RWRS.Frozen.TransientGoodPipes

open MeasureTheory Filter RWRS.Support
open scoped ENNReal

-- FROZEN-STATEMENT-BEGIN
theorem RWRS.Frozen.transientNonstabilization (p : ℝ) (hp0 : 0 < p) (hp3 : p < 3) :
    ∃ (V : Type) (G : SimpleGraph V) (hlf : G.LocallyFinite) (o : V) (d : ℕ),
      Infinite V ∧
        (haveI := hlf
        G.Connected ∧ RWRS.BoundedDegree G d ∧ ¬ RWRS.Recurrent G o ∧
          ∀ μ : ℝ, μ < 1 → ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧
            (∃ b : ℝ, ∀ᵐ z ∂ν, b ≤ z) ∧ RWRS.extMean ν = (μ : EReal) ∧
            RWRS.centeredMoment ν μ p ≠ ⊤ ∧
            RWRS.iidLaw V ν {σ : V → ℝ | RWRS.odometerLimit G σ o = ⊤} = 1 ∧
            RWRS.iidLaw V ν {σ : V → ℝ | RWRS.Stabilizes G σ} = 0)
-- FROZEN-STATEMENT-END
:= by
  classical
  obtain ⟨q, α, hpq, hq1, hq3, hα1, hα2, hα3⟩ := exists_params p hp3
  obtain ⟨B, hc⟩ := exists_combCond hα1 hα2
  have hB : 1 ≤ B := le_trans (by norm_num) hc.1
  have hL : ∀ j, 1 ≤ j → 1 ≤ RWRS.combLen B α j := fun j _ => one_le_combLen hc j
  haveI hinf : Infinite (pipeSites B (RWRS.combLen B α)) := pipeSites_infinite hB
  have hGconn : (pipeSub B (RWRS.combLen B α)).Connected := pipeSub_connected hL
  have hq0 : (0 : ℝ) < q := by linarith
  refine ⟨pipeSites B (RWRS.combLen B α), pipeSub B (RWRS.combLen B α),
    pipeSubLocallyFinite B (RWRS.combLen B α), pipeRootSub B (RWRS.combLen B α),
    2 * B + 3, hinf, hGconn, boundedDegree_pipeSub, not_recurrent_pipeSub hc, ?_⟩
  intro μ hμ
  set ν₀ : Measure ℝ := paretoLaw q with hν₀
  set m : ℝ := ∫ y, y ∂ν₀ with hm
  set c : ℝ := μ - m with hcdef
  set b : ℝ := 1 - c with hbdef
  have hmnn : (0 : ℝ) ≤ m := by
    rw [hm]
    refine integral_nonneg_of_ae ?_
    filter_upwards [ae_one_le_paretoLaw hq0] with y hy
    show (0 : ℝ) ≤ y
    linarith
  have hb : (0 : ℝ) ≤ b := by rw [hbdef, hcdef]; linarith
  obtain ⟨-, -, ⟨Ccomb, hCpos, -, hspike⟩, hgrow⟩ := RWRS.Frozen.combEstimates B α hc
  obtain ⟨hlow, hmean, hmom⟩ := shiftedParetoLaw_spec (q := q) (μ := μ) (p := p) hq1 hp0.le hpq
  refine ⟨shiftedParetoLaw q μ, inferInstance, ⟨1 + c, hlow⟩, hmean, hmom, ?_, ?_⟩
  all_goals
    (
    -- the law of the scenery is the image of the Pareto field
    have hΦm : Measurable (fun (Y : (List (Fin B) × ℕ) → ℝ)
        (v : pipeSites B (RWRS.combLen B α)) => Y (v : List (Fin B) × ℕ) + c) := by
      refine measurable_pi_lambda _ fun v => ?_
      have hco : Measurable (fun Y : (List (Fin B) × ℕ) → ℝ => Y (v : List (Fin B) × ℕ)) :=
        measurable_pi_apply _
      exact hco.add_const c
    have hm1 : Measurable (fun (ξ : pipeSites B (RWRS.combLen B α) → ℝ)
        (v : pipeSites B (RWRS.combLen B α)) => ξ v + c) := by
      refine measurable_pi_lambda _ fun v => ?_
      have hco : Measurable (fun ξ : pipeSites B (RWRS.combLen B α) → ℝ => ξ v) :=
        measurable_pi_apply _
      exact hco.add_const c
    have hm2 : Measurable (Set.restrict (pipeSites B (RWRS.combLen B α))
        (π := fun _ : List (Fin B) × ℕ => ℝ)) := by
      refine measurable_pi_lambda _ fun v => ?_
      exact measurable_pi_apply (v : List (Fin B) × ℕ)
    have hshift : shiftedParetoLaw q μ = ν₀.map (fun z => z + c) := rfl
    have hlaw : RWRS.iidLaw (pipeSites B (RWRS.combLen B α)) (shiftedParetoLaw q μ)
        = (RWRS.iidLaw (List (Fin B) × ℕ) ν₀).map
            (fun (Y : (List (Fin B) × ℕ) → ℝ) (v : pipeSites B (RWRS.combLen B α)) =>
              Y (v : List (Fin B) × ℕ) + c) := by
      rw [hshift, ← iidLaw_map (V := pipeSites B (RWRS.combLen B α)) ν₀
          (f := fun z : ℝ => z + c) (measurable_id.add_const c),
        ← iidLaw_restrict (pipeSites B (RWRS.combLen B α)) ν₀, Measure.map_map hm1 hm2]
      rfl
    have hae : ∀ᵐ Y ∂(RWRS.iidLaw (List (Fin B) × ℕ) ν₀),
        RWRS.odometerLimit (pipeSub B (RWRS.combLen B α))
          (fun v => Y (v : List (Fin B) × ℕ) + c) (pipeRootSub B (RWRS.combLen B α)) = ⊤ := by
      have hgood := RWRS.Frozen.transientGoodPipes B α q (2 + 2 * b * (Ccomb + 1)) hc hq1 hq3 hα3
        (by nlinarith) ν₀ inferInstance (isPareto_paretoLaw hq0)
      have hone := ae_all_mem (ι := List (Fin B) × ℕ) ν₀ measurableSet_Ici
        (by filter_upwards [ae_one_le_paretoLaw hq0] with y hy using hy)
      filter_upwards [hgood, hone] with Y hY1 hY2
      have hmain := odometerLimit_pipe_top hc b hb Ccomb hspike hgrow Y
        (fun u => le_trans zero_le_one (hY2 u)) hY1
      have hfun : (fun v : pipeSites B (RWRS.combLen B α) =>
          Y (v : List (Fin B) × ℕ) + c)
          = fun v : pipeSites B (RWRS.combLen B α) => Y (v : List (Fin B) × ℕ) - b + 1 := by
        funext v
        rw [hbdef]
        ring
      rw [hfun]
      exact hmain)
  · have hAm : MeasurableSet {σ : pipeSites B (RWRS.combLen B α) → ℝ |
        RWRS.odometerLimit (pipeSub B (RWRS.combLen B α)) σ
          (pipeRootSub B (RWRS.combLen B α)) = ⊤} :=
      (measurable_odometerLimit (G := pipeSub B (RWRS.combLen B α))
        (pipeRootSub B (RWRS.combLen B α))) (measurableSet_singleton ⊤)
    rw [hlaw, Measure.map_apply hΦm hAm]
    exact prob_eq_one_of_ae_mem (by filter_upwards [hae] with Y hY using hY)
  · rw [hlaw, Measure.map_apply hΦm (measurableSet_stabilizes hGconn)]
    refine measure_mono_null (fun Y hY => ?_) hae
    intro hcon
    exact hY (pipeRootSub B (RWRS.combLen B α)) hcon
