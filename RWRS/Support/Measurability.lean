/-
The odometer is a measurable function of the initial masses, and stabilization
is a measurable event.
-/
import RWRS.Support.Countable
import RWRS.Support.Green
import Mathlib.MeasureTheory.Constructions.Pi

open MeasureTheory
open scoped ENNReal

namespace RWRS.Support

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

theorem measurable_config (k : ℕ) (v : V) :
    Measurable fun σ : V → ℝ => config G σ k v := by
  induction k generalizing v with
  | zero => exact measurable_pi_apply v
  | succ k ih =>
      have hterm : ∀ w : V, Measurable fun σ : V → ℝ => emission G (config G σ k) w := by
        intro w
        exact (((ih w).sub measurable_const).max measurable_const).div_const _
      have : (fun σ : V → ℝ => config G σ (k + 1) v)
          = fun σ => min (config G σ k v) 1
            + ∑ w ∈ G.neighborFinset v, emission G (config G σ k) w := by
        funext σ
        rw [config_succ, topple]
      rw [this]
      exact ((ih v).min measurable_const).add
        (Finset.measurable_sum _ fun w _ => hterm w)

theorem measurable_odometer (n : ℕ) (v : V) :
    Measurable fun σ : V → ℝ => odometer G σ n v := by
  refine Finset.measurable_sum _ fun k _ => ?_
  exact (((measurable_config k v).sub measurable_const).max measurable_const).div_const _

theorem measurable_odometerLimit (v : V) :
    Measurable fun σ : V → ℝ => odometerLimit G σ v := by
  refine Measurable.iSup fun n => ?_
  exact (measurable_odometer n v).ennreal_ofReal

theorem measurableSet_stabilizes (hG : G.Connected) :
    MeasurableSet {σ : V → ℝ | Stabilizes G σ} := by
  haveI := countable_of_connected hG
  have : {σ : V → ℝ | Stabilizes G σ}
      = ⋂ v : V, {σ : V → ℝ | odometerLimit G σ v ≠ ⊤} := by
    ext σ
    simp [Stabilizes, Set.mem_iInter]
  rw [this]
  refine MeasurableSet.iInter fun v => ?_
  exact (measurable_odometerLimit v (measurableSet_singleton ⊤)).compl

theorem measurable_walkOp_iterate (k : ℕ) (x : V) :
    Measurable fun σ : V → ℝ => (walkOp G)^[k] (fun v => excess σ v / (G.degree v : ℝ)) x := by
  induction k generalizing x with
  | zero =>
      simp only [Function.iterate_zero_apply]
      exact ((measurable_pi_apply x).sub measurable_const).div_const _
  | succ k ih =>
      have : (fun σ : V → ℝ =>
            (walkOp G)^[k + 1] (fun v => excess σ v / (G.degree v : ℝ)) x)
          = fun σ => (∑ y ∈ G.neighborFinset x,
              (walkOp G)^[k] (fun v => excess σ v / (G.degree v : ℝ)) y)
                / (G.degree x : ℝ) := by
        funext σ
        rw [Function.iterate_succ_apply', walkOp]
      rw [this]
      exact (Finset.measurable_sum _ fun y _ => ih y).div_const _

theorem measurable_meanPayoff [Infinite V] (hG : G.Connected) (n : ℕ) (x : V) :
    Measurable fun σ : V → ℝ => meanPayoff G (excess σ) n x := by
  have : (fun σ : V → ℝ => meanPayoff G (excess σ) n x)
      = fun σ => ∑ k ∈ Finset.range n,
        (walkOp G)^[k] (fun v => excess σ v / (G.degree v : ℝ)) x := by
    funext σ
    exact walkExp_payoff_eq hG (excess σ) n x
  rw [this]
  exact Finset.measurable_sum _ fun k _ => measurable_walkOp_iterate k x

theorem measurableSet_supMeanPayoff_top [Infinite V] (hG : G.Connected) (o : V) :
    MeasurableSet {σ : V → ℝ | supMeanPayoff G (excess σ) o = ⊤} := by
  have hm : Measurable fun σ : V → ℝ => supMeanPayoff G (excess σ) o := by
    refine Measurable.iSup fun n => ?_
    exact (measurable_meanPayoff hG n o).ennreal_ofReal
  exact hm (measurableSet_singleton ⊤)

end RWRS.Support
