/-
Part (b) of `lem:good-walk`: the `p`-th moment of the dyadic block variable.

`Y_k` is at most the total absolute centred scenery along the block, because the
drift it subtracts is nonnegative and every fluctuation in the block is at most
that total.  Convexity turns the `p`-th power of a sum of `N` terms into `N`
times the average of their `p`-th powers, and each term has mean the centred
`p`-th moment of the marginal, so the block moment is at most `N^p` times it.
-/
import RWRS.Support.GoodWalkTail
import RWRS.Support.WeakLaw
import Mathlib.Analysis.MeanInequalitiesPow

namespace RWRS.Support

open MeasureTheory
open scoped ENNReal Classical

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

/-- **The dyadic block variable is at most the absolute centred scenery along
the block.** -/
theorem dyadicY_le_sum [Infinite V] (hG : G.Connected) {d : ℕ}
    (_hd : RWRS.BoundedDegree G d) (ξ : V → ℝ) (m : ℝ) (k : ℕ) (X : ℕ → V) :
    RWRS.dyadicY G ξ m d k X
      ≤ ∑ j ∈ Finset.range (2 ^ (k + 1)), |ξ (X j) - m| := by
  classical
  have hsumnn : (0 : ℝ) ≤ ∑ j ∈ Finset.range (2 ^ (k + 1)), |ξ (X j) - m| :=
    Finset.sum_nonneg fun j _ => abs_nonneg _
  have hterm : ∀ n : ℕ, n ≤ 2 ^ (k + 1) →
      RWRS.fluctuation G ξ m n X ≤ ∑ j ∈ Finset.range (2 ^ (k + 1)), |ξ (X j) - m| := by
    intro n hn
    rw [fluctuation_eq_sum]
    have hstep : ∀ j ∈ Finset.range n,
        (ξ (X j) - m) / (G.degree (X j) : ℝ) ≤ |ξ (X j) - m| := by
      intro j _
      have hdeg : (1 : ℝ) ≤ (G.degree (X j) : ℝ) := by
        exact_mod_cast degree_pos hG (X j)
      calc (ξ (X j) - m) / (G.degree (X j) : ℝ)
          ≤ |ξ (X j) - m| / (G.degree (X j) : ℝ) :=
            div_le_div_of_nonneg_right (le_abs_self _) (by linarith)
        _ ≤ |ξ (X j) - m| := div_le_self (abs_nonneg _) hdeg
    calc ∑ j ∈ Finset.range n, (ξ (X j) - m) / (G.degree (X j) : ℝ)
        ≤ ∑ j ∈ Finset.range n, |ξ (X j) - m| := Finset.sum_le_sum hstep
      _ ≤ ∑ j ∈ Finset.range (2 ^ (k + 1)), |ξ (X j) - m| := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun j _ _ => abs_nonneg _
          exact fun j hj => Finset.mem_range.2
            (lt_of_lt_of_le (Finset.mem_range.1 hj) hn)
  have hsup : (⨆ n ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), RWRS.fluctuation G ξ m n X)
      ≤ ∑ j ∈ Finset.range (2 ^ (k + 1)), |ξ (X j) - m| := by
    rw [iSup_mem_finset_real _ (block_nonempty k) (block_compl k)]
    refine max_le ?_ hsumnn
    refine Finset.sup'_le _ _ fun n hn => ?_
    exact hterm n (le_of_lt (Finset.mem_Ico.1 hn).2)
  have hdnn : (0 : ℝ) ≤ |m| / d * 2 ^ k := by positivity
  rw [RWRS.dyadicY]
  refine max_le ?_ hsumnn
  linarith

/-- **Convexity of the `p`-th power.** -/
theorem sum_rpow_le {N : ℕ} (hN : 1 ≤ N) (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j) {p : ℝ}
    (hp : 1 ≤ p) :
    (∑ j ∈ Finset.range N, a j) ^ p
      ≤ (N : ℝ) ^ (p - 1) * ∑ j ∈ Finset.range N, (a j) ^ p := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  set S := ∑ j ∈ Finset.range N, a j with hS
  set T := ∑ j ∈ Finset.range N, (a j) ^ p with hT
  have hSnn : (0 : ℝ) ≤ S := Finset.sum_nonneg fun j _ => ha j
  have hw : ∀ j ∈ Finset.range N, (0 : ℝ) ≤ (N : ℝ)⁻¹ := fun j _ => by positivity
  have hw' : ∑ j ∈ Finset.range N, (N : ℝ)⁻¹ = 1 := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
  have hmean := Real.rpow_arith_mean_le_arith_mean_rpow (Finset.range N)
    (fun _ => (N : ℝ)⁻¹) a hw hw' (fun j _ => ha j) hp
  simp only [← Finset.mul_sum, ← hS, ← hT] at hmean
  have hrw : ((N : ℝ)⁻¹ * S) = S / (N : ℝ) := by field_simp
  rw [hrw, Real.div_rpow hSnn hNpos.le] at hmean
  have hNp : (0 : ℝ) < (N : ℝ) ^ p := Real.rpow_pos_of_pos hNpos p
  rw [div_le_iff₀ hNp] at hmean
  have h3 : ((N : ℝ)⁻¹ * T) * (N : ℝ) ^ p = (N : ℝ) ^ (p - 1) * T := by
    rw [Real.rpow_sub hNpos, Real.rpow_one]
    field_simp
  linarith [hmean, h3]

/-! ### The joint moment -/

section Joint

variable [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]

/-- The scenery read at a fixed time of the trajectory has the marginal law. -/
theorem lintegral_scenery_rpow [Infinite V] (_hG : G.Connected) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (m p : ℝ) (x : V) (j : ℕ) :
    ∫⁻ z : (V → ℝ) × (ℕ → V), ENNReal.ofReal (|z.1 (z.2 j) - m| ^ p)
        ∂(RWRS.jointLaw G ν x)
      = RWRS.centeredMoment ν m p := by
  classical
  haveI : IsProbabilityMeasure (RWRS.iidLaw V ν) := instIsProbabilityMeasureIid ν
  haveI : IsProbabilityMeasure (RWRS.walkLaw G x) := by
    rw [walkLaw_eq_lib]; infer_instance
  have hmeas : Measurable fun z : (V → ℝ) × (ℕ → V) =>
      ENNReal.ofReal (|z.1 (z.2 j) - m| ^ p) := by
    refine ENNReal.measurable_ofReal.comp ?_
    exact (((measurable_scenery_at (V := V) j).sub measurable_const).abs.pow_const p)
  rw [RWRS.jointLaw, MeasureTheory.lintegral_prod_symm _ hmeas.aemeasurable]
  have hinner : ∀ X : ℕ → V,
      ∫⁻ ξ : V → ℝ, ENNReal.ofReal (|ξ (X j) - m| ^ p) ∂(RWRS.iidLaw V ν)
        = RWRS.centeredMoment ν m p := by
    intro X
    have hmap := map_eval_iidLaw (V := V) ν (X j)
    have hg : Measurable fun y : ℝ => ENNReal.ofReal (|y - m| ^ p) :=
      ENNReal.measurable_ofReal.comp ((measurable_id.sub measurable_const).abs.pow_const p)
    have hchange : ∫⁻ ξ : V → ℝ, ENNReal.ofReal (|ξ (X j) - m| ^ p) ∂(RWRS.iidLaw V ν)
        = ∫⁻ y : ℝ, ENNReal.ofReal (|y - m| ^ p)
            ∂((RWRS.iidLaw V ν).map (fun ξ : V → ℝ => ξ (X j))) :=
      (MeasureTheory.lintegral_map hg (measurable_pi_apply (X j))).symm
    rw [hchange, hmap, RWRS.centeredMoment]
  rw [MeasureTheory.lintegral_congr hinner, MeasureTheory.lintegral_const,
    measure_univ, mul_one]

/-- **Part (b): the `p`-th moment of the dyadic block variable.** -/
theorem lintegral_dyadicY_rpow_le [Infinite V] (hG : G.Connected) {d : ℕ}
    (hd : RWRS.BoundedDegree G d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {m p : ℝ} (hp : 1 ≤ p) (x : V) (k : ℕ) :
    ∫⁻ z : (V → ℝ) × (ℕ → V), ENNReal.ofReal (RWRS.dyadicY G z.1 m d k z.2 ^ p)
        ∂(RWRS.jointLaw G ν x)
      ≤ ENNReal.ofReal (((2 : ℝ) ^ (k + 1)) ^ p) * RWRS.centeredMoment ν m p := by
  classical
  haveI : IsProbabilityMeasure (RWRS.iidLaw V ν) := instIsProbabilityMeasureIid ν
  set N : ℕ := 2 ^ (k + 1) with hN
  have hN1 : 1 ≤ N := Nat.one_le_two_pow
  have hNcast : ((N : ℕ) : ℝ) = (2 : ℝ) ^ (k + 1) := by rw [hN]; push_cast; ring
  have hNpos : (0 : ℝ) < ((N : ℕ) : ℝ) := by exact_mod_cast hN1
  -- the pathwise bound
  have hpt : ∀ z : (V → ℝ) × (ℕ → V),
      ENNReal.ofReal (RWRS.dyadicY G z.1 m d k z.2 ^ p)
        ≤ ENNReal.ofReal (((N : ℕ) : ℝ) ^ (p - 1))
            * ∑ j ∈ Finset.range N, ENNReal.ofReal (|z.1 (z.2 j) - m| ^ p) := by
    intro z
    have hYnn : (0 : ℝ) ≤ RWRS.dyadicY G z.1 m d k z.2 := le_max_right _ _
    have hle := dyadicY_le_sum hG hd z.1 m k z.2
    have hpow : RWRS.dyadicY G z.1 m d k z.2 ^ p
        ≤ (∑ j ∈ Finset.range N, |z.1 (z.2 j) - m|) ^ p :=
      Real.rpow_le_rpow hYnn hle (by linarith)
    have hconv := sum_rpow_le (N := N) hN1 (fun j => |z.1 (z.2 j) - m|)
      (fun j => abs_nonneg _) hp
    have hchain : RWRS.dyadicY G z.1 m d k z.2 ^ p
        ≤ ((N : ℕ) : ℝ) ^ (p - 1) * ∑ j ∈ Finset.range N, |z.1 (z.2 j) - m| ^ p :=
      le_trans hpow hconv
    refine le_trans (ENNReal.ofReal_le_ofReal hchain) (le_of_eq ?_)
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg hNpos.le _)]
    congr 1
    exact ENNReal.ofReal_sum_of_nonneg fun j _ => Real.rpow_nonneg (abs_nonneg _) p
  refine le_trans (MeasureTheory.lintegral_mono hpt) ?_
  rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hsum : ∫⁻ z : (V → ℝ) × (ℕ → V),
      (∑ j ∈ Finset.range N, ENNReal.ofReal (|z.1 (z.2 j) - m| ^ p))
        ∂(RWRS.jointLaw G ν x)
      = (N : ℝ≥0∞) * RWRS.centeredMoment ν m p := by
    rw [MeasureTheory.lintegral_finsetSum]
    · rw [Finset.sum_congr rfl fun j _ => lintegral_scenery_rpow (G := G) hG ν m p x j,
        Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    · intro j _
      refine ENNReal.measurable_ofReal.comp ?_
      exact (((measurable_scenery_at (V := V) j).sub measurable_const).abs.pow_const p)
  rw [hsum, ← mul_assoc]
  refine mul_le_mul_left (le_of_eq ?_) _
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Real.rpow_nonneg hNpos.le _), hNcast]
  congr 1
  rw [← hNcast]
  nth_rewrite 2 [show ((N : ℕ) : ℝ) = ((N : ℕ) : ℝ) ^ (1 : ℝ) from (Real.rpow_one _).symm]
  rw [← Real.rpow_add hNpos]
  congr 1
  ring

/-- The centred `p`-th moment is finite when the absolute one is. -/
theorem abs_sub_rpow_le {z m p : ℝ} (hp : 1 ≤ p) :
    |z - m| ^ p ≤ (2 : ℝ) ^ (p - 1) * (|z| ^ p + |m| ^ p) := by
  classical
  set a : ℕ → ℝ := fun j => if j = 0 then |z| else |m| with ha
  have hann : ∀ j, 0 ≤ a j := by
    intro j; rw [ha]; dsimp; split <;> positivity
  have hconv := sum_rpow_le (N := 2) (by norm_num) a hann hp
  have h1 : ∑ j ∈ Finset.range 2, a j = |z| + |m| := by
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    simp [ha]
  have h2 : ∑ j ∈ Finset.range 2, (a j) ^ p = |z| ^ p + |m| ^ p := by
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    simp [ha]
  rw [h1, h2] at hconv
  have h3 : |z - m| ≤ |z| + |m| := by
    calc |z - m| = |z + -m| := by ring_nf
      _ ≤ |z| + |-m| := abs_add_le _ _
      _ = |z| + |m| := by rw [abs_neg]
  have h4 : |z - m| ^ p ≤ (|z| + |m|) ^ p :=
    Real.rpow_le_rpow (abs_nonneg _) h3 (by linarith)
  have hcast : ((2 : ℕ) : ℝ) = (2 : ℝ) := by norm_num
  rw [hcast] at hconv
  linarith

theorem centeredMoment_ne_top (ν : Measure ℝ) [IsProbabilityMeasure ν] {m p : ℝ}
    (hp : 1 ≤ p) (hmom : RWRS.absMoment ν p ≠ ⊤) : RWRS.centeredMoment ν m p ≠ ⊤ := by
  have hpt : ∀ z : ℝ, ENNReal.ofReal (|z - m| ^ p)
      ≤ ENNReal.ofReal ((2 : ℝ) ^ (p - 1))
          * (ENNReal.ofReal (|z| ^ p) + ENNReal.ofReal (|m| ^ p)) := by
    intro z
    refine le_trans (ENNReal.ofReal_le_ofReal (abs_sub_rpow_le hp)) (le_of_eq ?_)
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _),
      ENNReal.ofReal_add (Real.rpow_nonneg (abs_nonneg _) _)
        (Real.rpow_nonneg (abs_nonneg _) _)]
  have hle : RWRS.centeredMoment ν m p
      ≤ ENNReal.ofReal ((2 : ℝ) ^ (p - 1))
          * (RWRS.absMoment ν p + ENNReal.ofReal (|m| ^ p)) := by
    rw [RWRS.centeredMoment]
    refine le_trans (MeasureTheory.lintegral_mono hpt) ?_
    rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine mul_le_mul_right (le_of_eq ?_) (ENNReal.ofReal ((2 : ℝ) ^ (p - 1)))
    rw [MeasureTheory.lintegral_add_right _ measurable_const,
      MeasureTheory.lintegral_const, measure_univ, mul_one, RWRS.absMoment]
  refine ne_top_of_le_ne_top ?_ hle
  refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_
  exact ENNReal.add_ne_top.2 ⟨hmom, ENNReal.ofReal_ne_top⟩

end Joint

end RWRS.Support
