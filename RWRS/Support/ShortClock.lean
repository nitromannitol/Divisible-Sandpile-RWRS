/-
The stopping value is bounded by the Green function against the positive part of
the scenery, which is what makes the mean odometer finite when the total
inverse-degree time is finite.
-/
import RWRS.Support.KernelSum
import RWRS.Support.Representation
import RWRS.Support.HeatBasic
import RWRS.Scenery

open scoped ENNReal

namespace RWRS.Support

open scoped Classical

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite] [Infinite V]

theorem walkExp_payoff_le_green (hG : G.Connected) (ξ : V → ℝ) (n : ℕ) (x : V)
    {τ : (ℕ → V) → ℕ} (hle : ∀ X, τ X ≤ n) :
    walkExp G n x (fun X => payoff G ξ (τ X) X)
      ≤ ∑ v ∈ reach G x n, greenTime G n x v * max (ξ v) 0 := by
  have hmono : walkExp G n x (fun X => payoff G ξ (τ X) X)
      ≤ walkExp G n x (payoff G (fun v => max (ξ v) 0) n) := by
    refine walkExp_mono fun X => ?_
    have step1 : payoff G ξ (τ X) X ≤ payoff G (fun v => max (ξ v) 0) (τ X) X :=
      Finset.sum_le_sum fun k _ =>
        div_le_div_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _)
    have step2 : payoff G (fun v => max (ξ v) 0) (τ X) X
        ≤ payoff G (fun v => max (ξ v) 0) n X :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (fun k hk => Finset.mem_range.mpr
          (lt_of_lt_of_le (Finset.mem_range.mp hk) (hle X)))
        (fun k _ _ => div_nonneg (le_max_right _ _) (Nat.cast_nonneg _))
    exact step1.trans step2
  refine hmono.trans (le_of_eq ?_)
  rw [walkExp_payoff_eq hG]
  have hterm : ∀ k ∈ Finset.range n,
      (walkOp G)^[k] (fun v => max (ξ v) 0 / (G.degree v : ℝ)) x
        = ∑ v ∈ reach G x n, heat G k x v * (max (ξ v) 0 / (G.degree v : ℝ)) := by
    intro k hk
    rw [walkOp_iterate_eq_sum]
    refine Finset.sum_subset (reach_mono x (Nat.le_of_lt (Finset.mem_range.mp hk))) ?_
    intro v _ hv
    rw [heat_eq_zero_of_notMem_reach k x v hv, zero_mul]
  rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [greenTime, meanLocalTime, ← Finset.sum_mul]
  ring

theorem ofReal_greenTime_le_green (hG : G.Connected) (n : ℕ) (x v : V) :
    ENNReal.ofReal (greenTime G n x v) ≤ green G x v := by
  have hd : (0 : ℝ) < (G.degree v : ℝ) := Nat.cast_pos.mpr (degree_pos hG v)
  rw [greenTime, green, meanLocalTime, ENNReal.ofReal_div_of_pos hd,
    ENNReal.ofReal_natCast,
    ENNReal.ofReal_sum_of_nonneg (fun k _ => heat_nonneg k x v)]
  exact ENNReal.div_le_div_right (ENNReal.sum_le_tsum _) _

omit [Infinite V] in
theorem greenTime_nonneg (n : ℕ) (x v : V) : 0 ≤ greenTime G n x v :=
  div_nonneg (Finset.sum_nonneg fun k _ => heat_nonneg k x v) (Nat.cast_nonneg _)

theorem supStopValue_le_green (hG : G.Connected) (ξ : V → ℝ) (o : V) :
    supStopValue G ξ o ≤ ∑' v : V, green G o v * ENNReal.ofReal (max (ξ v) 0) := by
  refine iSup_le fun n => iSup_le fun a => iSup_le fun ha => ?_
  obtain ⟨τ, hτ, hle, rfl⟩ := ha
  refine le_trans (ENNReal.ofReal_le_ofReal (walkExp_payoff_le_green hG ξ n o hle)) ?_
  rw [ENNReal.ofReal_sum_of_nonneg
    (fun v _ => mul_nonneg (greenTime_nonneg n o v) (le_max_right _ _))]
  refine le_trans (Finset.sum_le_sum fun v _ => ?_) (ENNReal.sum_le_tsum _)
  rw [ENNReal.ofReal_mul (greenTime_nonneg n o v)]
  gcongr
  exact ofReal_greenTime_le_green hG n o v

omit [Infinite V] in
theorem lintegral_green_bound (hG : G.Connected) (o : V) (ν : MeasureTheory.Measure ℝ)
    (hν : MeasureTheory.IsProbabilityMeasure ν) :
    (∫⁻ ξ, ∑' v : V, green G o v * ENNReal.ofReal (max (ξ v) 0) ∂(iidLaw V ν))
      = (∑' v : V, green G o v) * posPart ν := by
  haveI := hν
  haveI := countable_of_connected hG
  have hmeas : ∀ v : V, Measurable fun ξ : V → ℝ => ENNReal.ofReal (max (ξ v) 0) :=
    fun v => ((measurable_pi_apply v).max measurable_const).ennreal_ofReal
  rw [MeasureTheory.lintegral_tsum fun v => ((hmeas v).const_mul _).aemeasurable]
  have hmarg : ∀ v : V,
      (∫⁻ ξ, ENNReal.ofReal (max (ξ v) 0) ∂(iidLaw V ν)) = posPart ν := by
    intro v
    have hmap : (iidLaw V ν).map (fun ξ : V → ℝ => ξ v) = ν :=
      MeasureTheory.Measure.infinitePi_map_eval _ v
    have hchange := MeasureTheory.lintegral_map (μ := iidLaw V ν)
      (f := fun z : ℝ => ENNReal.ofReal (max z 0)) (g := fun ξ : V → ℝ => ξ v)
      (measurable_id.max measurable_const).ennreal_ofReal (measurable_pi_apply v)
    rw [hmap] at hchange
    rw [← hchange, posPart]
    refine MeasureTheory.lintegral_congr fun z => ?_
    rcases le_total z 0 with h | h
    · rw [max_eq_right h, ENNReal.ofReal_zero, (ENNReal.ofReal_eq_zero).mpr h]
    · rw [max_eq_left h]
  have hstep : ∀ v : V,
      (∫⁻ ξ, green G o v * ENNReal.ofReal (max (ξ v) 0) ∂(iidLaw V ν))
        = green G o v * posPart ν := by
    intro v
    rw [MeasureTheory.lintegral_const_mul _ (hmeas v), hmarg v]
  rw [tsum_congr hstep, ENNReal.tsum_mul_right]

omit [Infinite V] in
theorem lintegral_green_bound' (hG : G.Connected) (o : V) (ν : MeasureTheory.Measure ℝ)
    (hν : MeasureTheory.IsProbabilityMeasure ν) (h : ℝ → ℝ≥0∞) (hh : Measurable h) :
    (∫⁻ σ, ∑' v : V, green G o v * h (σ v) ∂(iidLaw V ν))
      = (∑' v : V, green G o v) * ∫⁻ z, h z ∂ν := by
  haveI := hν
  haveI := countable_of_connected hG
  have hmeas : ∀ v : V, Measurable fun σ : V → ℝ => h (σ v) :=
    fun v => hh.comp (measurable_pi_apply v)
  rw [MeasureTheory.lintegral_tsum fun v => ((hmeas v).const_mul _).aemeasurable]
  have hmarg : ∀ v : V, (∫⁻ σ, h (σ v) ∂(iidLaw V ν)) = ∫⁻ z, h z ∂ν := by
    intro v
    have hmap : (iidLaw V ν).map (fun ξ : V → ℝ => ξ v) = ν :=
      MeasureTheory.Measure.infinitePi_map_eval _ v
    have hchange := MeasureTheory.lintegral_map (μ := iidLaw V ν) (f := h)
      (g := fun ξ : V → ℝ => ξ v) hh (measurable_pi_apply v)
    rw [hmap] at hchange
    rw [← hchange]
  have hstep : ∀ v : V, (∫⁻ σ, green G o v * h (σ v) ∂(iidLaw V ν))
      = green G o v * ∫⁻ z, h z ∂ν := by
    intro v
    rw [MeasureTheory.lintegral_const_mul _ (hmeas v), hmarg v]
  rw [tsum_congr hstep, ENNReal.tsum_mul_right]

/-- The mean payoff at a deterministic time is the finite-time Green function
against the scenery. -/
theorem meanPayoff_eq_green_sum (hG : G.Connected) (ξ : V → ℝ) (n : ℕ) (x : V) :
    meanPayoff G ξ n x = ∑ v ∈ reach G x n, greenTime G n x v * ξ v := by
  rw [meanPayoff, walkExp_payoff_eq hG]
  have hterm : ∀ k ∈ Finset.range n,
      (walkOp G)^[k] (fun v => ξ v / (G.degree v : ℝ)) x
        = ∑ v ∈ reach G x n, heat G k x v * (ξ v / (G.degree v : ℝ)) := by
    intro k hk
    rw [walkOp_iterate_eq_sum]
    refine Finset.sum_subset (reach_mono x (Nat.le_of_lt (Finset.mem_range.mp hk))) ?_
    intro v _ hv
    rw [heat_eq_zero_of_notMem_reach k x v hv, zero_mul]
  rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [greenTime, meanLocalTime, ← Finset.sum_mul]
  ring

/-- The clock is the total finite-time Green mass. -/
theorem clock_eq_green_sum (hG : G.Connected) (n : ℕ) (x : V) :
    clock G n x = ∑ v ∈ reach G x n, greenTime G n x v := by
  have h := meanPayoff_eq_green_sum hG (fun _ => (1 : ℝ)) n x
  rw [meanPayoff, walkExp_payoff_eq hG] at h
  simp only [mul_one] at h
  rw [clock, ← h]
  refine Finset.sum_congr rfl fun k _ => ?_
  rfl

end RWRS.Support
