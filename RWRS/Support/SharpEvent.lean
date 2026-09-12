/-
Steps 2 and 4 of `lem:moment-sharpness`, assembled at a fixed horizon.

At a site of the ball the finite-time Green function is large, so a mass above
`K t^α` at that site contributes more than the drift and the background can take
away, and the odometer at the root exceeds `t + 1`.  The good sites are governed
by independent masses, and the second-moment bound of `SharpCount` turns the
individual probabilities into a bound for the probability that some site of the
ball is good.
-/
import RWRS.Support.SharpBackground
import RWRS.Support.SharpBall
import RWRS.Support.SharpCount
import RWRS.Support.SharpGreen
import RWRS.Support.SharpIndep
import RWRS.Support.SpikeDecomp

namespace RWRS.Support

open MeasureTheory
open scoped ENNReal Classical

/-- **Step 2, the arithmetic.**  A spike at a site with a controlled background
and a controlled drift pushes the payoff above `2t`. -/
theorem spike_arith {c₀ K μ t g x b cl P Q : ℝ}
    (hc₀ : 0 < c₀) (ht : 1 ≤ t)
    (hP : 0 < P) (hQ : 1 ≤ Q) (hPQ : P * Q = t) (hPt : P ≤ t)
    (hg : c₀ * P ≤ g) (hx : K * Q ≤ x) (hb : -t ≤ b)
    (hcl0 : 0 ≤ cl) (hcl : cl ≤ 2 * t)
    (hK : c₀ * K = c₀ * |μ| + 2 * |μ| + 5) (hKμ : μ ≤ K) :
    2 * t ≤ g * (x - μ) + b + (μ - 1) * cl := by
  have habs0 : (0 : ℝ) ≤ |μ| := abs_nonneg μ
  have habs1 : μ ≤ |μ| := le_abs_self μ
  have habs2 : -μ ≤ |μ| := neg_le_abs μ
  have hKpos : 0 < K := by nlinarith
  have hKQ : K ≤ K * Q := by nlinarith
  have hxmu : 0 ≤ x - μ := by nlinarith
  have hc0P : 0 < c₀ * P := by positivity
  have h1 : c₀ * P * (K * Q - μ) ≤ g * (x - μ) := by nlinarith
  have h2 : c₀ * P * (K * Q - μ) = c₀ * K * t - c₀ * P * μ := by
    have hh : c₀ * P * (K * Q - μ) = c₀ * K * (P * Q) - c₀ * P * μ := by ring
    rw [hh, hPQ]
  have h3 : -(c₀ * t * |μ|) ≤ -(c₀ * P * μ) := by
    nlinarith [mul_le_mul_of_nonneg_left habs1 hc0P.le,
      mul_nonneg (mul_nonneg hc₀.le (sub_nonneg.2 hPt)) habs0]
  have hdrift : -((|μ| + 1) * (2 * t)) ≤ (μ - 1) * cl := by
    rcases le_or_gt 0 (μ - 1) with h | h
    · nlinarith
    · nlinarith
  nlinarith [h1, h2, h3, hdrift, hb, hK, ht]

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite] [Infinite V]
  {ν : Measure ℝ} [IsProbabilityMeasure ν]

/-- The good event at a site: a large mass there and a controlled background. -/
noncomputable def goodSite (G : SimpleGraph V) [G.LocallyFinite] (μ m t : ℝ) (n : ℕ)
    (o v : V) : Set (V → ℝ) :=
  {σ : V → ℝ | σ v ∈ {z : ℝ | m ≤ z}} ∩
    {σ : V → ℝ | (∑ u ∈ (reach G o n).erase v,
      RWRS.greenTime G n o u * (σ u - μ)) ∈ {y : ℝ | -t ≤ y}}

omit [Infinite V] in
theorem measurableSet_goodSite (μ m t : ℝ) (n : ℕ) (o v : V) :
    MeasurableSet (goodSite G μ m t n o v) := by
  refine MeasurableSet.inter ?_ ?_
  · exact (measurable_pi_apply v) (measurableSet_Ici (a := m))
  · exact (measurable_weighted_sum ((reach G o n).erase v)
      (fun u => RWRS.greenTime G n o u) (f := fun z => z - μ)
      (measurable_id.sub_const μ)) (measurableSet_Ici (a := -t))


/-- The background at a site is above `-t` with probability at least `3/4`. -/
theorem three_quarters_le_background (hG : G.Connected) (o : V) {μ : ℝ}
    (hint : Integrable (fun z => z - μ) ν) (hmean0 : ∫ z, (z - μ) ∂ν = 0)
    {M : ℝ} (hM : 0 ≤ M) (htail : ∫ z, |tailPart μ M z| ∂ν ≤ 1 / 32)
    {t : ℝ} (ht : 0 < t) (n : ℕ) (hn : (n : ℝ) ≤ 2 * t) (v : V)
    {H : ℝ} (hH : ∀ u : V, RWRS.greenTime G n o u ≤ H)
    (hHb : H * (2 * t) * (4 * M ^ 2) ≤ t ^ 2 / 128) :
    (3 : ℝ) / 4 ≤ (RWRS.iidLaw V ν {σ : V → ℝ | (∑ u ∈ (reach G o n).erase v,
      RWRS.greenTime G n o u * (σ u - μ)) ∈ {y : ℝ | -t ≤ y}}).toReal := by
  haveI : IsProbabilityMeasure (RWRS.iidLaw V ν) := instIsProbabilityMeasureIid ν
  set S : Finset V := (reach G o n).erase v with hS
  set w : V → ℝ := fun u => RWRS.greenTime G n o u with hw
  have hw0 : ∀ u, 0 ≤ w u := fun u => RWRS.Support.greenTime_nonneg n o u
  have hH0 : 0 ≤ H := le_trans (hw0 o) (hH o)
  have hWsum : ∑ u ∈ S, w u ≤ 2 * t :=
    le_trans (le_trans (sum_greenTime_le_clock hG n o S) (clock_le_horizon hG n o)) hn
  have hWsq : (∑ u ∈ S, w u ^ 2) * (4 * M ^ 2) ≤ t ^ 2 / 128 := by
    have hsq : ∑ u ∈ S, w u ^ 2 ≤ H * (2 * t) := by
      calc ∑ u ∈ S, w u ^ 2 ≤ ∑ u ∈ S, H * w u := by
            refine Finset.sum_le_sum fun u _ => ?_
            have := hH u
            nlinarith [hw0 u]
        _ = H * ∑ u ∈ S, w u := by rw [Finset.mul_sum]
        _ ≤ H * (2 * t) := mul_le_mul_of_nonneg_left hWsum hH0
    calc (∑ u ∈ S, w u ^ 2) * (4 * M ^ 2)
        ≤ (H * (2 * t)) * (4 * M ^ 2) := by
          refine mul_le_mul_of_nonneg_right hsq (by positivity)
      _ ≤ t ^ 2 / 128 := hHb
  have hbad := meas_background_small (ν := ν) hint hmean0 hM htail S w hw0 ht hWsum hWsq
  set E : Set (V → ℝ) := {σ : V → ℝ | ∑ u ∈ S, w u * (σ u - μ) < -t} with hE
  have hEmeas : MeasurableSet E := by
    exact (measurable_weighted_sum S w (f := fun z => z - μ)
      (measurable_id.sub_const μ)) measurableSet_Iio
  have hcompl : {σ : V → ℝ | (∑ u ∈ S, w u * (σ u - μ)) ∈ {y : ℝ | -t ≤ y}} = Eᶜ := by
    ext σ
    simp [hE, Set.mem_setOf_eq, not_lt]
  rw [hcompl, prob_compl_eq_one_sub hEmeas]
  have hle : RWRS.iidLaw V ν E ≤ ENNReal.ofReal (1 / 4) := hbad
  have hone : (1 : ℝ≥0∞) - ENNReal.ofReal (1 / 4) ≤ 1 - RWRS.iidLaw V ν E :=
    tsub_le_tsub_left hle 1
  have hval : (1 : ℝ≥0∞) - ENNReal.ofReal (1 / 4) = ENNReal.ofReal (3 / 4) := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp, ← ENNReal.ofReal_sub _ (by norm_num)]
    norm_num
  rw [hval] at hone
  have hfin : (1 : ℝ≥0∞) - RWRS.iidLaw V ν E ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) tsub_le_self
  have := ENNReal.toReal_mono hfin hone
  rwa [ENNReal.toReal_ofReal (by norm_num)] at this


/-- **The tail bound at a fixed horizon.**  If some site of the ball carries a
mass above `K t^α` while its background is above `-t`, then the odometer at the
root is above `t + 1`; the second-moment bound turns that into a lower bound for
the probability. -/
theorem meas_odometer_ge (hG : G.Connected) (o : V) {μ : ℝ}
    (hint : Integrable (fun z => z - μ) ν) (hmean0 : ∫ z, (z - μ) ∂ν = 0)
    {M : ℝ} (hM : 0 ≤ M) (htail : ∫ z, |tailPart μ M z| ∂ν ≤ 1 / 32)
    {c₀ K α : ℝ} (hc₀ : 0 < c₀) (hα : 0 < α)
    (hK : c₀ * K = c₀ * |μ| + 2 * |μ| + 5) (hKμ : μ ≤ K)
    {t R : ℕ} (ht : 1 ≤ t) (hRn : R ≤ 2 * t)
    (hball : ∀ v ∈ ballFinset G o R, c₀ * (t : ℝ) ^ (1 - α) ≤ RWRS.greenTime G (2 * t) o v)
    {H : ℝ} (hH : ∀ u : V, RWRS.greenTime G (2 * t) o u ≤ H)
    (hHb : H * (2 * (t : ℝ)) * (4 * M ^ 2) ≤ (t : ℝ) ^ 2 / 128) :
    ENNReal.ofReal (9 / 128 * min (((ballFinset G o R).card : ℝ)
        * (ν {z : ℝ | K * (t : ℝ) ^ α ≤ z}).toReal) 1)
      ≤ RWRS.iidLaw V ν {σ : V → ℝ | ((t : ℕ) : ℝ≥0∞) + 1 ≤ RWRS.odometerLimit G σ o} := by
  haveI : IsProbabilityMeasure (RWRS.iidLaw V ν) := instIsProbabilityMeasureIid ν
  set n : ℕ := 2 * t with hn
  set m : ℝ := K * (t : ℝ) ^ α with hm
  set s : Set ℝ := {z : ℝ | m ≤ z} with hsdef
  set p : ℝ := (ν s).toReal with hp
  set B : Finset V := ballFinset G o R with hB
  set A : V → Set (V → ℝ) := fun v => goodSite G μ m (t : ℝ) n o v with hA
  have htR : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  have htpos : (0 : ℝ) < (t : ℝ) := by linarith
  have hsmeas : MeasurableSet s := measurableSet_Ici (a := m)
  have hAmeas : ∀ v, MeasurableSet (A v) := fun v => measurableSet_goodSite μ m (t : ℝ) n o v
  have hp0 : 0 ≤ p := ENNReal.toReal_nonneg
  -- the background is good with probability at least three quarters
  have hbg : ∀ v : V, (3 : ℝ) / 4 ≤ (RWRS.iidLaw V ν
      {σ : V → ℝ | (∑ u ∈ (reach G o n).erase v,
        RWRS.greenTime G n o u * (σ u - μ)) ∈ {y : ℝ | -(t : ℝ) ≤ y}}).toReal := by
    intro v
    refine three_quarters_le_background hG o hint hmean0 hM htail htpos n ?_ v hH hHb
    rw [hn]; push_cast; linarith
  -- the two factors
  have hfac : ∀ v : V, RWRS.iidLaw V ν (A v)
      = ν s * RWRS.iidLaw V ν {σ : V → ℝ | (∑ u ∈ (reach G o n).erase v,
        RWRS.greenTime G n o u * (σ u - μ)) ∈ {y : ℝ | -(t : ℝ) ≤ y}} := by
    intro v
    exact meas_inter_coord_weighted (ν := ν) v ((reach G o n).erase v)
      (Finset.notMem_erase v _) (fun u => RWRS.greenTime G n o u) μ hsmeas
      (measurableSet_Ici (a := -(t : ℝ)))
  have hlow : ∀ v ∈ B, 3 / 4 * p ≤ (RWRS.iidLaw V ν (A v)).toReal := by
    intro v _
    rw [hfac v, ENNReal.toReal_mul]
    have h1 := hbg v
    have h2 : (0 : ℝ) ≤ (ν s).toReal := ENNReal.toReal_nonneg
    nlinarith [h1, h2]
  have hup : ∀ v ∈ B, (RWRS.iidLaw V ν (A v)).toReal ≤ p := by
    intro v _
    rw [hfac v, ENNReal.toReal_mul, hp]
    have h1 : (RWRS.iidLaw V ν {σ : V → ℝ | (∑ u ∈ (reach G o n).erase v,
        RWRS.greenTime G n o u * (σ u - μ)) ∈ {y : ℝ | -(t : ℝ) ≤ y}}).toReal ≤ 1 := by
      refine ENNReal.toReal_le_of_le_ofReal (by norm_num) ?_
      simpa using prob_le_one
    nlinarith [ENNReal.toReal_nonneg (a := ν s)]
  have hpair : ∀ v ∈ B, ∀ u ∈ B, v ≠ u →
      (RWRS.iidLaw V ν (A v ∩ A u)).toReal ≤ p * p := by
    intro v _ u _ hvu
    have hsub : A v ∩ A u ⊆ {σ : V → ℝ | σ v ∈ s} ∩ {σ : V → ℝ | σ u ∈ s} := by
      intro σ hσ
      exact ⟨hσ.1.1, hσ.2.1⟩
    have := measure_mono (μ := RWRS.iidLaw V ν) hsub
    rw [meas_inter_two_coord (ν := ν) hvu hsmeas] at this
    have h2 := ENNReal.toReal_mono (by simp [ENNReal.mul_ne_top, measure_ne_top]) this
    rw [ENNReal.toReal_mul] at h2
    exact h2
  have hmain := meas_biUnion_lower (P := RWRS.iidLaw V ν) B A hAmeas hp0 hlow hup hpair
  -- the union sits inside the tail event
  have hsub : (⋃ v ∈ B, A v) ⊆
      {σ : V → ℝ | ((t : ℕ) : ℝ≥0∞) + 1 ≤ RWRS.odometerLimit G σ o} := by
    intro σ hσ
    rw [Set.mem_iUnion₂] at hσ
    obtain ⟨v, hvB, hv⟩ := hσ
    have hvreach : v ∈ reach G o n :=
      reach_mono o hRn (ballFinset_subset_reach o R hvB)
    have hspike := spike_decomp hG σ μ n o hvreach
    have hP : (0 : ℝ) < (t : ℝ) ^ (1 - α) := Real.rpow_pos_of_pos htpos _
    have hQ : (1 : ℝ) ≤ (t : ℝ) ^ α := Real.one_le_rpow htR hα.le
    have hPQ : (t : ℝ) ^ (1 - α) * (t : ℝ) ^ α = (t : ℝ) := by
      rw [← Real.rpow_add htpos]; norm_num
    have hPt : (t : ℝ) ^ (1 - α) ≤ (t : ℝ) := by
      calc (t : ℝ) ^ (1 - α) ≤ (t : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le htR (by linarith)
        _ = (t : ℝ) := Real.rpow_one _
    have harith := spike_arith (c₀ := c₀) (K := K) (μ := μ) (t := (t : ℝ))
      (g := RWRS.greenTime G n o v) (x := σ v) (b := background G σ μ n o v)
      (cl := RWRS.clock G n o) (P := (t : ℝ) ^ (1 - α)) (Q := (t : ℝ) ^ α)
      hc₀ htR hP hQ hPQ hPt (hball v hvB) hv.1 hv.2
      (clock_nonneg hG n o)
      (by
        refine le_trans (clock_le_horizon hG n o) ?_
        rw [hn]; push_cast; linarith)
      hK hKμ
    have hge : ((t : ℕ) : ℝ≥0∞) + 1 ≤ ENNReal.ofReal
        (RWRS.greenTime G n o v * (σ v - μ) + background G σ μ n o v
          + (μ - 1) * RWRS.clock G n o) := by
      have hstep : ((t : ℕ) : ℝ≥0∞) + 1 = ENNReal.ofReal ((t : ℝ) + 1) := by
        rw [ENNReal.ofReal_add (by linarith) (by norm_num)]
        simp [ENNReal.ofReal_natCast]
      rw [hstep]
      refine ENNReal.ofReal_le_ofReal ?_
      linarith
    exact le_trans hge hspike
  have hmono : (RWRS.iidLaw V ν (⋃ v ∈ B, A v)).toReal
      ≤ (RWRS.iidLaw V ν {σ : V → ℝ | ((t : ℕ) : ℝ≥0∞) + 1
          ≤ RWRS.odometerLimit G σ o}).toReal :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)
  have hfinal : 9 / 128 * min ((B.card : ℝ) * p) 1
      ≤ (RWRS.iidLaw V ν {σ : V → ℝ | ((t : ℕ) : ℝ≥0∞) + 1
          ≤ RWRS.odometerLimit G σ o}).toReal := le_trans hmain hmono
  calc ENNReal.ofReal (9 / 128 * min ((B.card : ℝ) * p) 1)
      ≤ ENNReal.ofReal ((RWRS.iidLaw V ν {σ : V → ℝ | ((t : ℕ) : ℝ≥0∞) + 1
          ≤ RWRS.odometerLimit G σ o}).toReal) := ENNReal.ofReal_le_ofReal hfinal
    _ = RWRS.iidLaw V ν {σ : V → ℝ | ((t : ℕ) : ℝ≥0∞) + 1
          ≤ RWRS.odometerLimit G σ o} := ENNReal.ofReal_toReal (measure_ne_top _ _)

end RWRS.Support
