/-
The walk average of the local-time power sums of a discrete interval, for
`prop:subcritical`.

`eq:poly-moment` is a bound on `E_x[∑_v L_I(v)^p]` for a discrete interval `I`.
The bound itself is `sum_walkExp_localTimeOn_rpow_le`; what the chaining needs
is its `[0,∞]`-valued form, the lower integral against the law of the walk, and
that is what this file supplies.
-/
import RWRS.Support.GoodWalkTail
import RWRS.Support.SubVar
import RWRS.Support.SubMoment

namespace RWRS.Support

open MeasureTheory
open scoped ENNReal Classical

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]
variable [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]

omit [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] in
/-- The local time over `[a,b)` is settled by the positions up to `b`. -/
theorem dependsUpTo_localTimeOn (a b : ℕ) (v : V) (r : ℝ) :
    LatticeProb.Graph.DependsUpTo b
      (fun X : ℕ → V => ((localTimeOn a b v X : ℕ) : ℝ) ^ r) := by
  intro X Y hXY
  have hcard : localTimeOn a b v X = localTimeOn a b v Y := by
    unfold localTimeOn
    congr 1
    refine Finset.filter_congr fun k hk => ?_
    rw [hXY k (le_of_lt (Finset.mem_Ico.1 hk).2)]
  simp only [hcard]

theorem measurable_localTimeOn_rpow (a b : ℕ) (v : V) (r : ℝ) :
    Measurable (fun X : ℕ → V => ((localTimeOn a b v X : ℕ) : ℝ) ^ r) :=
  LatticeProb.Graph.measurable_of_dependsUpTo (dependsUpTo_localTimeOn a b v r)

omit [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] in
theorem localTimeOn_rpow_le_bound (a b : ℕ) (v : V) {r : ℝ} (hr : 0 ≤ r) (X : ℕ → V) :
    ‖((localTimeOn a b v X : ℕ) : ℝ) ^ r‖ ≤ ((b : ℝ) + 1) ^ r := by
  have hle : ((localTimeOn a b v X : ℕ) : ℝ) ≤ (b : ℝ) + 1 := by
    have h1 : localTimeOn a b v X ≤ RWRS.localTime b v X :=
      localTimeOn_le_localTime a b b le_rfl v X
    have h2 : RWRS.localTime b v X ≤ b := localTime_le b v X
    have : ((localTimeOn a b v X : ℕ) : ℝ) ≤ (b : ℝ) := by exact_mod_cast le_trans h1 h2
    linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) r)]
  exact Real.rpow_le_rpow (Nat.cast_nonneg _) hle hr

/-- **The walk average is the lower integral of the law**, for the local time of
a discrete interval. -/
theorem lintegral_localTimeOn_rpow [Infinite V] (hG : G.Connected)
    (a b : ℕ) (v : V) {r : ℝ} (hr : 0 ≤ r) (x : V) :
    ∫⁻ X, ENNReal.ofReal (((localTimeOn a b v X : ℕ) : ℝ) ^ r) ∂(RWRS.walkLaw G x)
      = ENNReal.ofReal
          (RWRS.walkExp G b x (fun X => ((localTimeOn a b v X : ℕ) : ℝ) ^ r)) := by
  classical
  have hdeg : ∀ w : V, 0 < G.degree w := fun w => degree_pos hG w
  have hmeas := measurable_localTimeOn_rpow (V := V) a b v r
  have hbdd : ∀ X : ℕ → V, ‖((localTimeOn a b v X : ℕ) : ℝ) ^ r‖ ≤ ((b : ℝ) + 1) ^ r :=
    fun X => localTimeOn_rpow_le_bound a b v hr X
  have hbridge : RWRS.walkExp G b x (fun X => ((localTimeOn a b v X : ℕ) : ℝ) ^ r)
      = ∫ X, ((localTimeOn a b v X : ℕ) : ℝ) ^ r ∂(RWRS.walkLaw G x) := by
    rw [walkExp_eq_lib, walkLaw_eq_lib]
    exact LatticeProb.Graph.walkExp_eq_integral hdeg b x _ hmeas _ hbdd
      (dependsUpTo_localTimeOn a b v r)
  haveI : IsProbabilityMeasure (RWRS.walkLaw G x) := by
    rw [walkLaw_eq_lib]; infer_instance
  have hint : Integrable (fun X : ℕ → V => ((localTimeOn a b v X : ℕ) : ℝ) ^ r)
      (RWRS.walkLaw G x) :=
    (memLp_top_of_bound hmeas.aestronglyMeasurable (((b : ℝ) + 1) ^ r)
      (Filter.Eventually.of_forall hbdd)).integrable (by norm_num)
  rw [hbridge, ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun X => Real.rpow_nonneg (Nat.cast_nonneg _) r)]

/-- **`eq:poly-moment` averaged over the walk.**  The `p`-th power sum of the
local times of a discrete interval, in `[0,∞]`, is at most the bound of
`lem:local-time` with the length of the interval in place of the horizon. -/
theorem lintegral_localTimeOnSum_le [Infinite V] (hG : G.Connected) {d_s A p : ℝ}
    (hds : 0 < d_s) (hsp : RWRS.SpectralDimensionBound G d_s A) (hp : 1 ≤ p)
    (x : V) {a b : ℕ} (hab : a < b) :
    (∫⁻ X, ∑' v : V, ENNReal.ofReal (((localTimeOn a b v X : ℕ) : ℝ) ^ p)
        ∂(RWRS.walkLaw G x))
      ≤ ENNReal.ofReal
          (p * momConst ⌈p⌉₊ * clockH A d_s (b - a) ^ (p - 1) * ((b - a : ℕ) : ℝ)) := by
  have hp0 : (0:ℝ) ≤ p := by linarith
  rw [lintegral_tsum fun v =>
    ((measurable_localTimeOn_rpow (V := V) a b v p).ennreal_ofReal).aemeasurable]
  have hpt : ∀ v : V,
      (∫⁻ X, ENNReal.ofReal (((localTimeOn a b v X : ℕ) : ℝ) ^ p) ∂(RWRS.walkLaw G x))
        = ENNReal.ofReal
            (RWRS.walkExp G b x (fun X => ((localTimeOn a b v X : ℕ) : ℝ) ^ p)) :=
    fun v => lintegral_localTimeOn_rpow hG a b v hp0 x
  rw [tsum_congr hpt]
  refine tsum_ofReal_le_of_sum_le
    (fun v => walkExp_nonneg fun X => Real.rpow_nonneg (Nat.cast_nonneg _) p) fun S => ?_
  exact sum_walkExp_localTimeOn_rpow_le hG hds hsp hp x hab S


end RWRS.Support
