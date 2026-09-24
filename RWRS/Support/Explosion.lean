/-
Explosion in the supercritical regime (`prop:supercritical`).

The mean payoff at a deterministic time splits into the drift `E[ξ] A_n(x)`
and the walk-averaged fluctuation `∑_v g_n(x,v)(ξ(v) - E[ξ])`.  The weak law of
`RWRS/Support/WeakLaw.lean` makes the second negligible against `A_n(x)`, so
once the drift diverges the payoff cannot stay below any fixed level, and the
event that it does has probability zero for every level.
-/
import RWRS.Support.WeakLaw

namespace RWRS.Support

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

/-- The drift and the fluctuation of the mean payoff. -/
theorem meanPayoff_eq_drift_add [Infinite V] (hG : G.Connected) (ξ : V → ℝ) (m : ℝ) (n : ℕ)
    (x : V) :
    meanPayoff G ξ n x
      = m * clock G n x + ∑ v ∈ reach G x n, greenTime G n x v * (ξ v - m) := by
  rw [meanPayoff_eq_green_sum hG, clock_eq_green_sum hG, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun v _ => by ring

/-- The payoff is monotone in the scenery. -/
theorem supMeanPayoff_mono [Infinite V] (hG : G.Connected) {ξ η : V → ℝ} (h : ∀ v, ξ v ≤ η v)
    (x : V) : supMeanPayoff G ξ x ≤ supMeanPayoff G η x := by
  refine iSup_le fun n => le_trans (ENNReal.ofReal_le_ofReal ?_)
    (le_iSup (fun k : ℕ => ENNReal.ofReal (meanPayoff G η k x)) n)
  rw [meanPayoff_eq_green_sum hG, meanPayoff_eq_green_sum hG]
  exact Finset.sum_le_sum fun v _ =>
    mul_le_mul_of_nonneg_left (h v) (greenTime_nonneg n x v)

/-- **Explosion at a finite positive mean.** -/
theorem ae_supMeanPayoff_top_of_mean [Infinite V] (hG : G.Connected) (x : V)
    (hA : Tendsto (fun n : ℕ => clock G n x) atTop atTop)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (m : ℝ) (hmpos : 0 < m)
    (hint : Integrable (fun z : ℝ => z) ν) (hmean : ∫ z, z ∂ν = m) :
    ∀ᵐ ξ ∂(iidLaw V ν), supMeanPayoff G ξ x = ⊤ := by
  classical
  have hintabs : Integrable (fun z => |z - m|) ν := (hint.sub (integrable_const m)).abs
  have hm0 : ∫ z, (z - m) ∂ν = 0 := by
    rw [integral_sub hint (integrable_const m), hmean, integral_const]
    simp
  have hweak := tendsto_measureReal_weighted (V := V) ν m hintabs hm0
    (fun n => reach G x n) (fun n v => greenTime G n x v) (fun n v => greenTime_nonneg n x v)
    (fun n => clock G n x) (fun n => clock_eq_green_sum hG n x) hA
    (tendsto_sumSq_div_clock_sq hG x hA) (ε := m / 2) (by linarith)
  set E : ℝ → Set (V → ℝ) := fun B => {ξ : V → ℝ | ∀ n : ℕ, meanPayoff G ξ n x ≤ B} with hE
  have hEzero : ∀ B : ℝ, iidLaw V ν (E B) = 0 := by
    intro B
    have hle : ∀ᶠ n in atTop, (iidLaw V ν).real (E B)
        ≤ (iidLaw V ν).real {ξ : V → ℝ | m / 2 * clock G n x
            ≤ |∑ v ∈ reach G x n, greenTime G n x v * (ξ v - m)|} := by
      filter_upwards [hA.eventually_gt_atTop (2 * B / m), hA.eventually_gt_atTop 0] with n hn hn0
      refine measureReal_mono ?_ (measure_ne_top _ _)
      intro ξ hξ
      have h1 : meanPayoff G ξ n x ≤ B := hξ n
      rw [meanPayoff_eq_drift_add hG ξ m n x] at h1
      rw [div_lt_iff₀ hmpos] at hn
      simp only [Set.mem_setOf_eq]
      refine le_trans ?_ (neg_le_abs _)
      nlinarith [h1, hn, hn0]
    have hle0 : (iidLaw V ν).real (E B) ≤ 0 := ge_of_tendsto hweak hle
    have h0 : (iidLaw V ν).real (E B) = 0 := le_antisymm hle0 measureReal_nonneg
    exact (measureReal_eq_zero_iff (measure_ne_top _ _)).mp h0
  rw [ae_iff]
  refine measure_mono_null ?_ (measure_iUnion_null fun k : ℕ => hEzero (k : ℝ))
  intro ξ hξ
  simp only [Set.mem_setOf_eq] at hξ
  have hlt : supMeanPayoff G ξ x ≠ ⊤ := hξ
  obtain ⟨k, hk⟩ := exists_nat_gt (supMeanPayoff G ξ x).toReal
  refine Set.mem_iUnion.2 ⟨k, fun n => ?_⟩
  have h1 : ENNReal.ofReal (meanPayoff G ξ n x) ≤ supMeanPayoff G ξ x :=
    le_iSup (fun n : ℕ => ENNReal.ofReal (meanPayoff G ξ n x)) n
  exact le_trans ((ENNReal.ofReal_le_iff_le_toReal hlt).mp h1) hk.le


/-! ### The extended mean -/

theorem enorm_real_eq (z : ℝ) : ‖z‖ₑ = ENNReal.ofReal z + ENNReal.ofReal (-z) := by
  rcases le_total 0 z with h | h
  · rw [ENNReal.ofReal_eq_zero.2 (neg_nonpos.2 h), add_zero, Real.enorm_eq_ofReal h]
  · rw [ENNReal.ofReal_eq_zero.2 h, zero_add, Real.enorm_eq_ofReal_abs, abs_of_nonpos h]

theorem negPart_ne_top {ν : Measure ℝ} (hmean : 0 < extMean ν) : negPart ν ≠ ⊤ := by
  intro hn
  rw [extMean, hn, EReal.coe_ennreal_top, EReal.sub_top] at hmean
  exact not_lt_bot hmean

theorem integrable_id_of_finite {ν : Measure ℝ} (hp : posPart ν ≠ ⊤) (hn : negPart ν ≠ ⊤) :
    Integrable (fun z : ℝ => z) ν := by
  refine ⟨aestronglyMeasurable_id, ?_⟩
  rw [HasFiniteIntegral, lintegral_congr (fun z => enorm_real_eq z),
    lintegral_add_left ENNReal.measurable_ofReal]
  exact ENNReal.add_lt_top.2 ⟨hp.lt_top, hn.lt_top⟩

theorem integral_id_eq {ν : Measure ℝ} (hint : Integrable (fun z : ℝ => z) ν) :
    ∫ z, z ∂ν = (posPart ν).toReal - (negPart ν).toReal :=
  integral_eq_lintegral_pos_part_sub_lintegral_neg_part hint

theorem toReal_lt_toReal_of_extMean {ν : Measure ℝ} (hp : posPart ν ≠ ⊤) (hn : negPart ν ≠ ⊤)
    (hmean : 0 < extMean ν) : (negPart ν).toReal < (posPart ν).toReal := by
  have hpe : ((posPart ν).toReal : EReal) = (posPart ν : EReal) := EReal.coe_ennreal_toReal hp
  have hne : ((negPart ν).toReal : EReal) = (negPart ν : EReal) := EReal.coe_ennreal_toReal hn
  rw [extMean, ← hpe, ← hne, ← EReal.coe_sub] at hmean
  have : (0 : ℝ) < (posPart ν).toReal - (negPart ν).toReal := by
    exact_mod_cast hmean
  linarith

/-! ### Truncation from above -/

theorem posPart_map_min (ν : Measure ℝ) (K : ℝ) :
    posPart (ν.map (fun z => min z K)) = ∫⁻ z, ENNReal.ofReal (min z K) ∂ν := by
  rw [posPart]
  exact lintegral_map (f := fun z : ℝ => ENNReal.ofReal z) (g := fun z : ℝ => min z K)
    ENNReal.measurable_ofReal (by fun_prop)

theorem negPart_map_min (ν : Measure ℝ) (K : ℝ) :
    negPart (ν.map (fun z => min z K)) = ∫⁻ z, ENNReal.ofReal (-(min z K)) ∂ν := by
  rw [negPart]
  exact lintegral_map (f := fun z : ℝ => ENNReal.ofReal (-z)) (g := fun z : ℝ => min z K)
    (by fun_prop) (by fun_prop)

theorem posPart_map_min_le (ν : Measure ℝ) [IsProbabilityMeasure ν] (K : ℝ) :
    posPart (ν.map (fun z => min z K)) ≤ ENNReal.ofReal K := by
  rw [posPart_map_min]
  calc ∫⁻ z, ENNReal.ofReal (min z K) ∂ν ≤ ∫⁻ _z, ENNReal.ofReal K ∂ν :=
        lintegral_mono fun z => ENNReal.ofReal_le_ofReal (min_le_right _ _)
    _ = ENNReal.ofReal K := by simp

theorem negPart_map_min_le (ν : Measure ℝ) {K : ℝ} (hK : 0 ≤ K) :
    negPart (ν.map (fun z => min z K)) ≤ negPart ν := by
  rw [negPart_map_min, negPart]
  refine lintegral_mono fun z => ?_
  rcases le_total z K with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h, ENNReal.ofReal_eq_zero.2 (by linarith)]
    simp

theorem iSup_lintegral_min (ν : Measure ℝ) :
    ⨆ K : ℕ, ∫⁻ z, ENNReal.ofReal (min z (K : ℝ)) ∂ν = posPart ν := by
  have hmeas : ∀ K : ℕ, Measurable fun z : ℝ => ENNReal.ofReal (min z (K : ℝ)) := by
    intro K; fun_prop
  have hmono : Monotone fun (K : ℕ) (z : ℝ) => ENNReal.ofReal (min z (K : ℝ)) := by
    intro a b hab z
    exact ENNReal.ofReal_le_ofReal (min_le_min le_rfl (by exact_mod_cast hab))
  have h := lintegral_iSup (μ := ν) hmeas hmono
  rw [← h, posPart]
  refine lintegral_congr fun z => le_antisymm (iSup_le fun K => ?_) ?_
  · exact ENNReal.ofReal_le_ofReal (min_le_left _ _)
  · refine le_iSup_of_le ⌈z⌉₊ ?_
    rcases le_total z 0 with h | h
    · rw [ENNReal.ofReal_eq_zero.2 h]; simp
    · rw [min_eq_left (Nat.le_ceil z)]

theorem exists_truncation (ν : Measure ℝ) [IsProbabilityMeasure ν] (hp : posPart ν = ⊤)
    (hn : negPart ν ≠ ⊤) :
    ∃ K : ℕ, posPart (ν.map (fun z => min z (K : ℝ))) ≠ ⊤ ∧
      negPart (ν.map (fun z => min z (K : ℝ))) ≠ ⊤ ∧
      (negPart (ν.map (fun z => min z (K : ℝ)))).toReal
        < (posPart (ν.map (fun z => min z (K : ℝ)))).toReal := by
  obtain ⟨K, hK⟩ : ∃ K : ℕ, negPart ν < ∫⁻ z, ENNReal.ofReal (min z (K : ℝ)) ∂ν := by
    by_contra hcon
    have hall : ∀ K : ℕ, ∫⁻ z, ENNReal.ofReal (min z (K : ℝ)) ∂ν ≤ negPart ν := by
      intro K
      exact not_lt.mp fun h => hcon ⟨K, h⟩
    have := iSup_le hall
    rw [iSup_lintegral_min ν, hp] at this
    exact hn (top_le_iff.mp this)
  have hKnn : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg _
  have hpfin : posPart (ν.map (fun z => min z (K : ℝ))) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (posPart_map_min_le ν (K : ℝ))
  have hnfin : negPart (ν.map (fun z => min z (K : ℝ))) ≠ ⊤ :=
    ne_top_of_le_ne_top hn (negPart_map_min_le ν hKnn)
  refine ⟨K, hpfin, hnfin, ?_⟩
  have h1 : negPart (ν.map (fun z => min z (K : ℝ)))
      < posPart (ν.map (fun z => min z (K : ℝ))) := by
    rw [posPart_map_min]
    exact lt_of_le_of_lt (negPart_map_min_le ν hKnn) hK
  exact ENNReal.toReal_lt_toReal hnfin hpfin |>.mpr h1

/-! ### The i.i.d. field of a pushed-forward marginal -/

theorem iidLaw_map (ν : Measure ℝ) [IsProbabilityMeasure ν] {f : ℝ → ℝ} (hf : Measurable f) :
    (iidLaw V ν).map (fun (ξ : V → ℝ) (v : V) => f (ξ v)) = iidLaw V (ν.map f) :=
  MeasureTheory.Measure.infinitePi_map_pi (μ := fun _ : V => ν) (f := fun _ : V => f)
    fun _ => hf

/-- **Explosion in the supercritical regime.** -/
theorem ae_supMeanPayoff_top [Infinite V] (hG : G.Connected) (x : V)
    (hA : Tendsto (fun n : ℕ => clock G n x) atTop atTop)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hmean : 0 < extMean ν) :
    ∀ᵐ ξ ∂(iidLaw V ν), supMeanPayoff G ξ x = ⊤ := by
  classical
  have hn := negPart_ne_top hmean
  by_cases hp : posPart ν = ⊤
  · -- truncate the marginal from above
    obtain ⟨K, hpK, hnK, hlt⟩ := exists_truncation ν hp hn
    set f : ℝ → ℝ := fun z => min z (K : ℝ) with hf
    have hfm : Measurable f := measurable_id.min measurable_const
    haveI : IsProbabilityMeasure (ν.map f) := Measure.isProbabilityMeasure_map hfm.aemeasurable
    have hintK : Integrable (fun z : ℝ => z) (ν.map f) := integrable_id_of_finite hpK hnK
    have hmK : ∫ z, z ∂(ν.map f) = (posPart (ν.map f)).toReal - (negPart (ν.map f)).toReal :=
      integral_id_eq hintK
    have hae := ae_supMeanPayoff_top_of_mean (V := V) hG x hA (ν.map f)
      ((posPart (ν.map f)).toReal - (negPart (ν.map f)).toReal) (by linarith) hintK hmK
    rw [ae_iff] at hae ⊢
    set Φ : (V → ℝ) → (V → ℝ) := fun ξ v => f (ξ v) with hΦ
    have hΦm : Measurable Φ := measurable_pi_lambda _ fun v => hfm.comp (measurable_pi_apply v)
    have hsub : {ξ : V → ℝ | ¬ supMeanPayoff G ξ x = ⊤}
        ⊆ Φ ⁻¹' {η : V → ℝ | ¬ supMeanPayoff G η x = ⊤} := by
      intro ξ hξ hcon
      refine hξ ?_
      refine top_le_iff.mp ?_
      rw [← hcon]
      exact supMeanPayoff_mono hG (fun v => min_le_left _ _) x
    refine measure_mono_null hsub ?_
    refine le_antisymm (le_trans (Measure.le_map_apply hΦm.aemeasurable _) ?_) (by simp)
    rw [hΦ, iidLaw_map ν hfm]
    exact le_of_eq hae
  · have hint : Integrable (fun z : ℝ => z) ν := integrable_id_of_finite hp hn
    have hmpos : 0 < (posPart ν).toReal - (negPart ν).toReal := by
      linarith [toReal_lt_toReal_of_extMean hp hn hmean]
    exact ae_supMeanPayoff_top_of_mean hG x hA ν _ hmpos hint (integral_id_eq hint)


/-! ### The clock on a graph of bounded degree -/

theorem walkOp_iterate_invDeg_ge [Infinite V] (hG : G.Connected) {d : ℕ}
    (hd : BoundedDegree G d) :
    ∀ (k : ℕ) (x : V), 1 / (d : ℝ) ≤ (walkOp G)^[k] (invDeg G) x := by
  intro k
  induction k with
  | zero =>
      intro x
      simp only [Function.iterate_zero_apply, invDeg]
      have h1 : (0 : ℝ) < (G.degree x : ℝ) := by exact_mod_cast degree_pos hG x
      have h2 : (G.degree x : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd x
      exact one_div_le_one_div_of_le h1 h2
  | succ k ih =>
      intro x
      rw [Function.iterate_succ_apply', walkOp]
      have hdx : (0 : ℝ) < (G.degree x : ℝ) := by exact_mod_cast degree_pos hG x
      rw [le_div_iff₀ hdx]
      calc 1 / (d : ℝ) * (G.degree x : ℝ) = ∑ _y ∈ G.neighborFinset x, 1 / (d : ℝ) := by
            rw [Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree, nsmul_eq_mul]
            ring
        _ ≤ ∑ y ∈ G.neighborFinset x, (walkOp G)^[k] (invDeg G) y :=
            Finset.sum_le_sum fun y _ => ih y

theorem clock_ge_of_boundedDegree [Infinite V] (hG : G.Connected) {d : ℕ}
    (hd : BoundedDegree G d) (n : ℕ) (x : V) : (n : ℝ) / d ≤ clock G n x := by
  rw [clock]
  calc (n : ℝ) / d = ∑ _k ∈ Finset.range n, 1 / (d : ℝ) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring
    _ ≤ ∑ k ∈ Finset.range n, (walkOp G)^[k] (invDeg G) x :=
        Finset.sum_le_sum fun k _ => walkOp_iterate_invDeg_ge hG hd k x

theorem boundedDegree_pos [Infinite V] (hG : G.Connected) {d : ℕ} (hd : BoundedDegree G d) :
    0 < d := by
  obtain ⟨x⟩ := (inferInstance : Nonempty V)
  exact lt_of_lt_of_le (degree_pos hG x) (hd x)

theorem tendsto_clock_of_boundedDegree [Infinite V] (hG : G.Connected) {d : ℕ}
    (hd : BoundedDegree G d) (x : V) :
    Tendsto (fun n : ℕ => clock G n x) atTop atTop := by
  refine tendsto_atTop_mono (fun n => clock_ge_of_boundedDegree hG hd n x) ?_
  have hd1 : (0 : ℝ) < d := by exact_mod_cast boundedDegree_pos hG hd
  exact Filter.Tendsto.atTop_div_const hd1 tendsto_natCast_atTop_atTop

end RWRS.Support
