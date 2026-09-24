/-
Part (a) of `lem:good-walk`: the walk visits no vertex too often.

On the complement of the good-walk event some vertex is visited more than
`N^{α+δ}` times, so the `r`-th power sum of the local times exceeds
`N^{r(α+δ)}`; Markov's inequality against the local-time moments of
`lem:local-time` then bounds the probability of that complement.
-/
import RWRS.Support.LocalTimeSum
import RWRS.Support.NestedLower
import RWRS.Support.DyadicSup

namespace RWRS.Support

open MeasureTheory
open scoped ENNReal Classical

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]
variable [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]

omit [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] in
/-- The local time before time `n` is settled by the positions up to `n`. -/
theorem dependsUpTo_localTime (n : ℕ) (v : V) (r : ℝ) :
    LatticeProb.Graph.DependsUpTo n
      (fun X : ℕ → V => ((RWRS.localTime n v X : ℕ) : ℝ) ^ r) := by
  intro X Y hXY
  have hcard : RWRS.localTime n v X = RWRS.localTime n v Y := by
    rw [RWRS.localTime, RWRS.localTime]
    congr 1
    refine Finset.filter_congr fun k hk => ?_
    rw [hXY k (le_of_lt (Finset.mem_range.1 hk))]
  simp only [hcard]

theorem measurable_localTime_rpow (n : ℕ) (v : V) (r : ℝ) :
    Measurable (fun X : ℕ → V => ((RWRS.localTime n v X : ℕ) : ℝ) ^ r) :=
  LatticeProb.Graph.measurable_of_dependsUpTo (dependsUpTo_localTime n v r)

omit [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] in
theorem localTime_le (n : ℕ) (v : V) (X : ℕ → V) : RWRS.localTime n v X ≤ n := by
  rw [RWRS.localTime]
  exact le_trans (Finset.card_filter_le _ _) (le_of_eq (Finset.card_range n))

omit [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] in
/-- The `r`-th power of the local time is bounded by the horizon. -/
theorem localTime_rpow_le_bound (n : ℕ) (v : V) {r : ℝ} (hr : 0 ≤ r) (X : ℕ → V) :
    ‖((RWRS.localTime n v X : ℕ) : ℝ) ^ r‖ ≤ ((n : ℝ) + 1) ^ r := by
  have hle : ((RWRS.localTime n v X : ℕ) : ℝ) ≤ (n : ℝ) + 1 := by
    have := localTime_le n v X
    have : ((RWRS.localTime n v X : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast this
    linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) r)]
  exact Real.rpow_le_rpow (Nat.cast_nonneg _) hle hr

/-- **The walk average is the lower integral of the law.** -/
theorem lintegral_localTime_rpow [Infinite V] (hG : G.Connected)
    (n : ℕ) (v : V) {r : ℝ} (hr : 0 ≤ r) (x : V) :
    ∫⁻ X, ENNReal.ofReal (((RWRS.localTime n v X : ℕ) : ℝ) ^ r) ∂(RWRS.walkLaw G x)
      = ENNReal.ofReal
          (RWRS.walkExp G n x (fun X => ((RWRS.localTime n v X : ℕ) : ℝ) ^ r)) := by
  classical
  have hdeg : ∀ w : V, 0 < G.degree w := fun w => degree_pos hG w
  have hmeas := measurable_localTime_rpow (V := V) n v r
  have hbdd : ∀ X : ℕ → V, ‖((RWRS.localTime n v X : ℕ) : ℝ) ^ r‖ ≤ ((n : ℝ) + 1) ^ r :=
    fun X => localTime_rpow_le_bound n v hr X
  have hbridge : RWRS.walkExp G n x (fun X => ((RWRS.localTime n v X : ℕ) : ℝ) ^ r)
      = ∫ X, ((RWRS.localTime n v X : ℕ) : ℝ) ^ r ∂(RWRS.walkLaw G x) := by
    rw [walkExp_eq_lib, walkLaw_eq_lib]
    exact LatticeProb.Graph.walkExp_eq_integral hdeg n x _ hmeas _ hbdd
      (dependsUpTo_localTime n v r)
  haveI : IsProbabilityMeasure (RWRS.walkLaw G x) := by
    rw [walkLaw_eq_lib]; infer_instance
  have hint : Integrable (fun X : ℕ → V => ((RWRS.localTime n v X : ℕ) : ℝ) ^ r)
      (RWRS.walkLaw G x) :=
    (memLp_top_of_bound hmeas.aestronglyMeasurable (((n : ℝ) + 1) ^ r)
      (Filter.Eventually.of_forall hbdd)).integrable (by norm_num)
  rw [hbridge, ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun X => Real.rpow_nonneg (Nat.cast_nonneg _) r)]

/-! ### Markov's inequality on the good-walk event -/

/-- The power sum of the local times along a trajectory. -/
noncomputable def localTimeSum (n : ℕ) (r : ℝ) (X : ℕ → V) : ℝ≥0∞ :=
  ∑' v : V, ENNReal.ofReal (((RWRS.localTime n v X : ℕ) : ℝ) ^ r)

theorem measurable_localTimeSum (n : ℕ) (r : ℝ) :
    Measurable (fun X : ℕ → V => localTimeSum n r X) := by
  refine Measurable.tsum fun v => ?_
  exact (measurable_localTime_rpow (V := V) n v r).ennreal_ofReal

omit [MeasurableSingletonClass V] [Countable V] in
theorem measurableSet_goodWalk (α δ : ℝ) (k : ℕ) [MeasurableSingletonClass V] [Countable V] :
    MeasurableSet (RWRS.goodWalk (V := V) α δ k) := by
  have hrw : RWRS.goodWalk (V := V) α δ k
      = ⋂ v : V, {X : ℕ → V |
          ((RWRS.localTime (2 ^ (k + 1)) v X : ℕ) : ℝ) ≤ (2 ^ (k + 1) : ℝ) ^ (α + δ)} := by
    ext X
    simp [RWRS.goodWalk]
  rw [hrw]
  refine MeasurableSet.iInter fun v => ?_
  have hm : Measurable (fun X : ℕ → V => ((RWRS.localTime (2 ^ (k + 1)) v X : ℕ) : ℝ)) := by
    have := measurable_localTime_rpow (V := V) (2 ^ (k + 1)) v 1
    simpa using this
  exact measurableSet_le hm measurable_const

omit [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] in
/-- Off the good-walk event the power sum of the local times is large. -/
theorem le_localTimeSum_of_notMem {α δ : ℝ} {k : ℕ} {r : ℝ} (hr : 0 ≤ r)
    {X : ℕ → V} (hX : X ∉ RWRS.goodWalk (V := V) α δ k) :
    ENNReal.ofReal (((2 : ℝ) ^ (k + 1)) ^ (r * (α + δ)))
      ≤ localTimeSum (2 ^ (k + 1)) r X := by
  rw [RWRS.goodWalk, Set.mem_setOf_eq] at hX
  push Not at hX
  obtain ⟨v, hv⟩ := hX
  refine le_trans ?_ (ENNReal.le_tsum v)
  refine ENNReal.ofReal_le_ofReal ?_
  have hbase : (0 : ℝ) ≤ (2 : ℝ) ^ (k + 1) := by positivity
  have hle : ((2 : ℝ) ^ (k + 1)) ^ (α + δ)
      ≤ ((RWRS.localTime (2 ^ (k + 1)) v X : ℕ) : ℝ) := le_of_lt hv
  have hpow := Real.rpow_le_rpow (Real.rpow_nonneg hbase (α + δ)) hle hr
  calc ((2 : ℝ) ^ (k + 1)) ^ (r * (α + δ))
      = (((2 : ℝ) ^ (k + 1)) ^ (α + δ)) ^ r := by
        rw [← Real.rpow_mul hbase]
        congr 1
        ring
    _ ≤ ((RWRS.localTime (2 ^ (k + 1)) v X : ℕ) : ℝ) ^ r := hpow

/-- **Markov's inequality for the good-walk event.** -/
theorem walkLaw_goodWalk_compl_le [Infinite V] (hG : G.Connected)
    {α δ r : ℝ} (hr : 0 ≤ r) (x : V) (k : ℕ) :
    RWRS.walkLaw G x (RWRS.goodWalk (V := V) α δ k)ᶜ
        * ENNReal.ofReal (((2 : ℝ) ^ (k + 1)) ^ (r * (α + δ)))
      ≤ ∑' v : V, ENNReal.ofReal (RWRS.walkExp G (2 ^ (k + 1)) x
          (fun X => ((RWRS.localTime (2 ^ (k + 1)) v X : ℕ) : ℝ) ^ r)) := by
  classical
  set ε : ℝ≥0∞ := ENNReal.ofReal (((2 : ℝ) ^ (k + 1)) ^ (r * (α + δ))) with hε
  have hsub : (RWRS.goodWalk (V := V) α δ k)ᶜ
      ⊆ {X : ℕ → V | ε ≤ localTimeSum (2 ^ (k + 1)) r X} :=
    fun X hX => le_localTimeSum_of_notMem hr hX
  have hmono : RWRS.walkLaw G x (RWRS.goodWalk (V := V) α δ k)ᶜ
      ≤ RWRS.walkLaw G x {X : ℕ → V | ε ≤ localTimeSum (2 ^ (k + 1)) r X} :=
    measure_mono hsub
  have hmarkov := MeasureTheory.mul_meas_ge_le_lintegral₀
    (μ := RWRS.walkLaw G x)
    (measurable_localTimeSum (V := V) (2 ^ (k + 1)) r).aemeasurable ε
  have hswap : ∫⁻ X, localTimeSum (2 ^ (k + 1)) r X ∂(RWRS.walkLaw G x)
      = ∑' v : V, ∫⁻ X, ENNReal.ofReal
          (((RWRS.localTime (2 ^ (k + 1)) v X : ℕ) : ℝ) ^ r) ∂(RWRS.walkLaw G x) := by
    simp only [localTimeSum]
    exact MeasureTheory.lintegral_tsum
      fun v => ((measurable_localTime_rpow (V := V) (2 ^ (k + 1)) v r).ennreal_ofReal).aemeasurable
  have hterm : ∀ v : V, ∫⁻ X, ENNReal.ofReal
        (((RWRS.localTime (2 ^ (k + 1)) v X : ℕ) : ℝ) ^ r) ∂(RWRS.walkLaw G x)
      = ENNReal.ofReal (RWRS.walkExp G (2 ^ (k + 1)) x
          (fun X => ((RWRS.localTime (2 ^ (k + 1)) v X : ℕ) : ℝ) ^ r)) :=
    fun v => lintegral_localTime_rpow hG (2 ^ (k + 1)) v hr x
  calc RWRS.walkLaw G x (RWRS.goodWalk (V := V) α δ k)ᶜ * ε
      ≤ RWRS.walkLaw G x {X : ℕ → V | ε ≤ localTimeSum (2 ^ (k + 1)) r X} * ε :=
        mul_le_mul_left hmono ε
    _ = ε * RWRS.walkLaw G x {X : ℕ → V | ε ≤ localTimeSum (2 ^ (k + 1)) r X} := by
        rw [mul_comm]
    _ ≤ ∫⁻ X, localTimeSum (2 ^ (k + 1)) r X ∂(RWRS.walkLaw G x) := hmarkov
    _ = _ := by rw [hswap, tsum_congr hterm]

/-- **Part (a) in its divided form.** -/
theorem walkLaw_goodWalk_compl_le_div [Infinite V] (hG : G.Connected)
    {α δ r : ℝ} (hr : 0 ≤ r) (x : V) (k : ℕ) {M : ℝ}
    (hbnd : ∑' v : V, ENNReal.ofReal (RWRS.walkExp G (2 ^ (k + 1)) x
        (fun X => ((RWRS.localTime (2 ^ (k + 1)) v X : ℕ) : ℝ) ^ r))
      ≤ ENNReal.ofReal M) :
    RWRS.walkLaw G x (RWRS.goodWalk (V := V) α δ k)ᶜ
      ≤ ENNReal.ofReal (M / ((2 : ℝ) ^ (k + 1)) ^ (r * (α + δ))) := by
  have hbase : (0 : ℝ) < (2 : ℝ) ^ (k + 1) := by positivity
  have hc : (0 : ℝ) < ((2 : ℝ) ^ (k + 1)) ^ (r * (α + δ)) := Real.rpow_pos_of_pos hbase _
  have hmain := le_trans (walkLaw_goodWalk_compl_le (α := α) (δ := δ) hG hr x k) hbnd
  rw [ENNReal.ofReal_div_of_pos hc]
  rw [ENNReal.le_div_iff_mul_le (Or.inl (by simp [ENNReal.ofReal_eq_zero]; linarith))
    (Or.inl ENNReal.ofReal_ne_top)]
  exact hmain

end RWRS.Support
