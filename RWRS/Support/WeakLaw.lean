/-
The weak law for a Green-weighted i.i.d. sum, under a first moment only.

`rwrs.tex:560-580` splits the fluctuation into a bounded truncation and a small
tail: the tail is controlled in `L^1` and by Markov's inequality, the
truncation is centred, independent and bounded, so Chebyshev's inequality
applies to it and the second moment of the weights enters.  The hypothesis that
no single weight carries a positive fraction of the total is used through
`∑_v w_v^2 / (∑_v w_v)^2 → 0`.
-/
import RWRS.Support.ClockRatio
import LatticeProb.Prob.Moments
import Mathlib.Probability.Independence.InfinitePi

namespace RWRS.Support

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

/-! ### The clamp -/

/-- `clamp m M z` is `z` moved into `[m - M, m + M]`. -/
noncomputable def clamp (m M z : ℝ) : ℝ := max (min z (m + M)) (m - M)

@[fun_prop]
theorem measurable_clamp (m M : ℝ) : Measurable (clamp m M) :=
  (measurable_id.min measurable_const).max measurable_const

theorem clamp_of_le_lower {m M z : ℝ} (hM : 0 ≤ M) (h : z ≤ m - M) : clamp m M z = m - M := by
  rw [clamp, min_eq_left (by linarith), max_eq_right h]

theorem clamp_of_upper_le {m M z : ℝ} (hM : 0 ≤ M) (h : m + M ≤ z) : clamp m M z = m + M := by
  rw [clamp, min_eq_right h, max_eq_left (by linarith)]

theorem clamp_of_mem {m M z : ℝ} (h1 : m - M ≤ z) (h2 : z ≤ m + M) : clamp m M z = z := by
  rw [clamp, min_eq_left h2, max_eq_left h1]

theorem abs_clamp_sub_le {m M : ℝ} (hM : 0 ≤ M) (z : ℝ) : |clamp m M z - m| ≤ M := by
  rcases le_total z (m - M) with h1 | h1
  · rw [clamp_of_le_lower hM h1]
    rw [show m - M - m = -M by ring, abs_neg, abs_of_nonneg hM]
  · rcases le_total z (m + M) with h2 | h2
    · rw [clamp_of_mem h1 h2, abs_le]; constructor <;> linarith
    · rw [clamp_of_upper_le hM h2, show m + M - m = M by ring, abs_of_nonneg hM]

theorem abs_sub_clamp_le {m M : ℝ} (hM : 0 ≤ M) (z : ℝ) : |z - clamp m M z| ≤ |z - m| := by
  rcases le_total z (m - M) with h1 | h1
  · rw [clamp_of_le_lower hM h1, abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    linarith
  · rcases le_total z (m + M) with h2 | h2
    · rw [clamp_of_mem h1 h2, sub_self, abs_zero]
      exact abs_nonneg _
    · rw [clamp_of_upper_le hM h2, abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      linarith

theorem sub_clamp_eq_zero {m M z : ℝ} (h : |z - m| ≤ M) : z - clamp m M z = 0 := by
  rw [abs_le] at h
  rw [clamp_of_mem (by linarith) (by linarith), sub_self]


/-! ### The coordinates of the i.i.d. field -/

variable {V : Type*}

theorem map_eval_iidLaw (ν : Measure ℝ) [IsProbabilityMeasure ν] (v : V) :
    (iidLaw V ν).map (fun ξ : V → ℝ => ξ v) = ν :=
  MeasureTheory.Measure.infinitePi_map_eval _ v

instance instIsProbabilityMeasureIid (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (iidLaw V ν) := by
  unfold iidLaw; infer_instance

theorem iIndepFun_coord (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    iIndepFun (fun (v : V) (ξ : V → ℝ) => ξ v) (iidLaw V ν) := by
  refine (iIndepFun_iff_map_fun_eq_infinitePi_map fun v => measurable_pi_apply v).2 ?_
  rw [show (fun (ξ : V → ℝ) (v : V) => ξ v) = id from rfl, Measure.map_id]
  simp only [map_eval_iidLaw]
  rfl

theorem integral_coord (ν : Measure ℝ) [IsProbabilityMeasure ν] (v : V) {f : ℝ → ℝ}
    (hf : AEStronglyMeasurable f ν) :
    ∫ ξ, f (ξ v) ∂(iidLaw V ν) = ∫ z, f z ∂ν := by
  conv_rhs => rw [← map_eval_iidLaw ν v]
  rw [integral_map (measurable_pi_apply v).aemeasurable
    (by rwa [map_eval_iidLaw ν v])]

theorem integrable_coord (ν : Measure ℝ) [IsProbabilityMeasure ν] (v : V) {f : ℝ → ℝ}
    (hf : Integrable f ν) : Integrable (fun ξ : V → ℝ => f (ξ v)) (iidLaw V ν) := by
  rw [show (fun ξ : V → ℝ => f (ξ v)) = f ∘ (fun ξ : V → ℝ => ξ v) from rfl]
  refine (integrable_map_measure ?_ (measurable_pi_apply v).aemeasurable).mp ?_
  · rw [map_eval_iidLaw ν v]; exact hf.aestronglyMeasurable
  · rw [map_eval_iidLaw ν v]; exact hf


theorem integrable_of_bounded {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {f : Ω → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ ω, |f ω| ≤ C) : Integrable f P :=
  Integrable.mono' (integrable_const C) hf.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hC ω)

/-! ### The tail, by Markov's inequality -/

theorem measureReal_tail_le (ν : Measure ℝ) [IsProbabilityMeasure ν] (m : ℝ)
    (hint : Integrable (fun z => |z - m|) ν) {M : ℝ} (hM : 0 ≤ M)
    (F : Finset V) (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) {t : ℝ} (ht : 0 < t) :
    (iidLaw V ν).real {ξ : V → ℝ | t ≤ |∑ v ∈ F, w v * (ξ v - clamp m M (ξ v))|}
      ≤ (∑ v ∈ F, w v) * (∫ z, |z - clamp m M z| ∂ν) / t := by
  classical
  set g : ℝ → ℝ := fun z => |z - clamp m M z| with hg
  have hgm : Measurable g := by fun_prop
  have hgnn : ∀ z, 0 ≤ g z := fun z => abs_nonneg _
  have hgle : ∀ z, g z ≤ |z - m| := fun z => abs_sub_clamp_le hM z
  have hgint : Integrable g ν := by
    refine Integrable.mono' hint hgm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hgnn z)]
    exact hgle z
  set W : (V → ℝ) → ℝ := fun ξ => |∑ v ∈ F, w v * (ξ v - clamp m M (ξ v))| with hW
  have hWm : Measurable W := by
    simp only [hW]
    fun_prop
  have hWle : ∀ ξ : V → ℝ, W ξ ≤ ∑ v ∈ F, w v * g (ξ v) := by
    intro ξ
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_of_eq (Finset.sum_congr rfl fun v _ => ?_))
    rw [abs_mul, abs_of_nonneg (hw v)]
  have hmajint : Integrable (fun ξ : V → ℝ => ∑ v ∈ F, w v * g (ξ v)) (iidLaw V ν) :=
    integrable_finsetSum _ fun v _ => ((integrable_coord ν v hgint).const_mul (w v))
  have hWint : Integrable W (iidLaw V ν) := by
    refine Integrable.mono' hmajint hWm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _)]
    exact hWle ξ
  have hmaj : ∫ ξ, W ξ ∂(iidLaw V ν) ≤ (∑ v ∈ F, w v) * ∫ z, g z ∂ν := by
    refine le_trans (integral_mono hWint hmajint hWle) (le_of_eq ?_)
    rw [integral_finsetSum _ fun v _ => ((integrable_coord ν v hgint).const_mul (w v)),
      Finset.sum_mul]
    exact Finset.sum_congr rfl fun v _ => by
      rw [integral_const_mul, integral_coord ν v hgint.aestronglyMeasurable]
  have hmark := mul_meas_ge_le_integral_of_nonneg (μ := iidLaw V ν) (f := W)
    (Filter.Eventually.of_forall fun ξ => abs_nonneg _) hWint t
  rw [le_div_iff₀ ht]
  calc (iidLaw V ν).real {ξ : V → ℝ | t ≤ W ξ} * t
      = t * (iidLaw V ν).real {ξ : V → ℝ | t ≤ W ξ} := by ring
    _ ≤ ∫ ξ, W ξ ∂(iidLaw V ν) := hmark
    _ ≤ (∑ v ∈ F, w v) * ∫ z, g z ∂ν := hmaj


/-! ### The truncation, by Chebyshev's inequality -/

theorem abs_integral_clamp_sub_le (ν : Measure ℝ) [IsProbabilityMeasure ν] (m : ℝ) {M : ℝ}
    (hM : 0 ≤ M) : |∫ z, (clamp m M z - m) ∂ν| ≤ M := by
  have hint : Integrable (fun z => clamp m M z - m) ν :=
    integrable_of_bounded ((measurable_clamp m M).sub measurable_const)
      (fun z => abs_clamp_sub_le hM z)
  calc |∫ z, (clamp m M z - m) ∂ν| ≤ ∫ z, |clamp m M z - m| ∂ν := abs_integral_le_integral_abs
    _ ≤ ∫ _z, M ∂ν := by
        refine integral_mono hint.abs (integrable_const M) fun z => abs_clamp_sub_le hM z
    _ = M := by simp

theorem abs_clamp_sub_sub_le {m M b : ℝ} (hM : 0 ≤ M) (hb : |b| ≤ M) (z : ℝ) :
    |clamp m M z - m - b| ≤ 2 * M := by
  have h1 : |clamp m M z - m| ≤ M := abs_clamp_sub_le hM z
  have h2 := abs_le.mp h1
  have h3 := abs_le.mp hb
  rw [abs_le]
  constructor <;> linarith

theorem measureReal_trunc_le (ν : Measure ℝ) [IsProbabilityMeasure ν] (m : ℝ)
    {M : ℝ} (hM : 0 ≤ M) (F : Finset V) (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) {t : ℝ} (ht : 0 < t) :
    (iidLaw V ν).real
        {ξ : V → ℝ | t ≤ |∑ v ∈ F, w v * (clamp m M (ξ v) - m - ∫ z, (clamp m M z - m) ∂ν)|}
      ≤ 4 * M ^ 2 * (∑ v ∈ F, w v ^ 2) / t ^ 2 := by
  classical
  set b : ℝ := ∫ z, (clamp m M z - m) ∂ν with hbdef
  have hb : |b| ≤ M := abs_integral_clamp_sub_le ν m hM
  set X : V → (V → ℝ) → ℝ := fun v ξ => w v * (clamp m M (ξ v) - m - b) with hX
  have hbound : ∀ (v : V) (ξ : V → ℝ), |X v ξ| ≤ w v * (2 * M) := by
    intro v ξ
    rw [hX, abs_mul, abs_of_nonneg (hw v)]
    exact mul_le_mul_of_nonneg_left (abs_clamp_sub_sub_le hM hb (ξ v)) (hw v)
  have hmeas : ∀ v, Measurable (X v) := by
    intro v
    simp only [hX]
    fun_prop
  have hindep : iIndepFun X (iidLaw V ν) := by
    have h := (iIndepFun_coord (V := V) ν).comp
      (fun v (z : ℝ) => w v * (clamp m M z - m - b))
      (fun v => ((measurable_clamp m M).sub measurable_const).sub measurable_const |>.const_mul _)
    exact h
  have h4 : ∀ v, Integrable (fun ξ : V → ℝ => X v ξ ^ 4) (iidLaw V ν) := by
    intro v
    refine integrable_of_bounded ((hmeas v).pow_const 4) (C := (w v * (2 * M)) ^ 4) fun ξ => ?_
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hbound v ξ) 4
  have hXint : ∀ v, Integrable (X v) (iidLaw V ν) := fun v =>
    integrable_of_bounded (hmeas v) (hbound v)
  have hmean : ∀ v, ∫ ξ, X v ξ ∂(iidLaw V ν) = 0 := by
    intro v
    have hc : Integrable (fun z => clamp m M z - m - b) ν :=
      integrable_of_bounded (((measurable_clamp m M).sub measurable_const).sub measurable_const)
        (C := 2 * M) fun z => abs_clamp_sub_sub_le hM hb z
    simp only [hX]
    rw [integral_const_mul, integral_coord ν v hc.aestronglyMeasurable]
    have hcm : Integrable (fun z => clamp m M z - m) ν :=
      integrable_of_bounded ((measurable_clamp m M).sub measurable_const)
        fun z => abs_clamp_sub_le hM z
    have hsplit : ∫ z, (clamp m M z - m - b) ∂ν
        = (∫ z, (clamp m M z - m) ∂ν) - ∫ _z, b ∂ν :=
      integral_sub hcm (integrable_const b)
    rw [hsplit, integral_const, ← hbdef]
    simp
  have hcheb := LatticeProb.measureReal_abs_sum_ge_le X hmeas hindep h4 hmean F ht
  refine le_trans hcheb ?_
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  calc ∑ v ∈ F, ∫ ξ, X v ξ ^ 2 ∂(iidLaw V ν)
      ≤ ∑ v ∈ F, 4 * M ^ 2 * w v ^ 2 := by
        refine Finset.sum_le_sum fun v _ => ?_
        have hsq : ∀ ξ : V → ℝ, X v ξ ^ 2 ≤ 4 * M ^ 2 * w v ^ 2 := by
          intro ξ
          have h1 := hbound v ξ
          have h2 : (0 : ℝ) ≤ |X v ξ| := abs_nonneg _
          nlinarith [sq_abs (X v ξ), hw v, hM]
        calc ∫ ξ, X v ξ ^ 2 ∂(iidLaw V ν) ≤ ∫ _ξ, 4 * M ^ 2 * w v ^ 2 ∂(iidLaw V ν) := by
              refine integral_mono ?_ (integrable_const _) hsq
              exact integrable_of_bounded ((hmeas v).pow_const 2) (C := (w v * (2 * M)) ^ 2)
                fun ξ => by
                  rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hbound v ξ) 2
          _ = 4 * M ^ 2 * w v ^ 2 := by simp
    _ = 4 * M ^ 2 * ∑ v ∈ F, w v ^ 2 := by rw [Finset.mul_sum]


/-! ### The weak law -/

theorem tendsto_integral_abs_sub_clamp (ν : Measure ℝ) [IsProbabilityMeasure ν] (m : ℝ)
    (hint : Integrable (fun z => |z - m|) ν) :
    Tendsto (fun M : ℕ => ∫ z, |z - clamp m (M : ℝ) z| ∂ν) atTop (𝓝 0) := by
  have hmeas : ∀ M : ℕ, AEStronglyMeasurable (fun z => |z - clamp m (M : ℝ) z|) ν := by
    intro M
    have : Measurable fun z : ℝ => |z - clamp m (M : ℝ) z| := by fun_prop
    exact this.aestronglyMeasurable
  have hbd : ∀ M : ℕ, ∀ᵐ z ∂ν, ‖|z - clamp m (M : ℝ) z|‖ ≤ |z - m| := by
    intro M
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_abs]
    exact abs_sub_clamp_le (by positivity) z
  have hlim : ∀ᵐ z ∂ν,
      Tendsto (fun M : ℕ => |z - clamp m (M : ℝ) z|) atTop (𝓝 0) := by
    filter_upwards with z
    have hev : ∀ᶠ M : ℕ in atTop, |z - clamp m (M : ℝ) z| = 0 := by
      filter_upwards [Filter.eventually_ge_atTop ⌈|z - m|⌉₊] with M hM
      have : |z - m| ≤ (M : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hM)
      rw [sub_clamp_eq_zero this, abs_zero]
    exact Tendsto.congr' (Filter.EventuallyEq.symm hev) tendsto_const_nhds
  have h := tendsto_integral_of_dominated_convergence (μ := ν) (bound := fun z => |z - m|)
    hmeas hint hbd hlim
  simpa using h

/-- **The weak law for a weighted i.i.d. sum.**  With a first moment only, the
weighted sum of the centred field is small compared with the total weight in
probability, as soon as the squares of the weights are negligible against the
square of their total. -/
theorem tendsto_measureReal_weighted {V : Type*} (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (m : ℝ) (hint : Integrable (fun z => |z - m|) ν) (hm : ∫ z, (z - m) ∂ν = 0)
    (S : ℕ → Finset V) (w : ℕ → V → ℝ) (hw : ∀ n v, 0 ≤ w n v)
    (A : ℕ → ℝ) (hA : ∀ n, A n = ∑ v ∈ S n, w n v)
    (hAtop : Tendsto A atTop atTop)
    (hSig : Tendsto (fun n => (∑ v ∈ S n, w n v ^ 2) / A n ^ 2) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => (iidLaw V ν).real
        {ξ : V → ℝ | ε * A n ≤ |∑ v ∈ S n, w n v * (ξ v - m)|}) atTop (𝓝 0) := by
  classical
  set e : ℕ → ℝ := fun M => ∫ z, |z - clamp m (M : ℝ) z| ∂ν with hedef
  have hetend := tendsto_integral_abs_sub_clamp ν m hint
  refine NormedAddGroup.tendsto_nhds_zero.2 fun η hη => ?_
  obtain ⟨M, hMe⟩ : ∃ M : ℕ, e M < min (ε / 3) (η * ε / 12) := by
    have hpos : (0 : ℝ) < min (ε / 3) (η * ε / 12) := lt_min (by positivity) (by positivity)
    exact (hetend.eventually (gt_mem_nhds hpos)).exists
  have hMe1 : e M < ε / 3 := lt_of_lt_of_le hMe (min_le_left _ _)
  have hMe2 : e M < η * ε / 12 := lt_of_lt_of_le hMe (min_le_right _ _)
  have hMnn : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg _
  set b : ℝ := ∫ z, (clamp m (M : ℝ) z - m) ∂ν with hbdef
  -- the bias is at most the tail
  have hcz : Integrable (fun z => clamp m (M : ℝ) z - z) ν := by
    refine Integrable.mono' hint (by fun_prop) (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_sub_comm]
    exact abs_sub_clamp_le hMnn z
  have hzm : Integrable (fun z => z - m) ν := by
    refine Integrable.mono' hint (by fun_prop) (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs]
  have hbeq : b = ∫ z, (clamp m (M : ℝ) z - z) ∂ν := by
    have hsum : ∫ z, ((clamp m (M : ℝ) z - z) + (z - m)) ∂ν
        = (∫ z, (clamp m (M : ℝ) z - z) ∂ν) + ∫ z, (z - m) ∂ν := integral_add hcz hzm
    rw [hm, add_zero] at hsum
    rw [hbdef, ← hsum]
    exact integral_congr_ae (Filter.Eventually.of_forall fun z => by ring)
  have hb : |b| ≤ e M := by
    rw [hbeq]
    refine le_trans abs_integral_le_integral_abs ?_
    refine le_of_eq (integral_congr_ae (Filter.Eventually.of_forall fun z => ?_))
    exact abs_sub_comm _ _
  -- the Chebyshev term tends to zero
  have hchev : Tendsto (fun n => 4 * (M : ℝ) ^ 2 * (∑ v ∈ S n, w n v ^ 2)
      / ((ε / 3) * A n) ^ 2) atTop (𝓝 0) := by
    have hcm := hSig.const_mul (36 * (M : ℝ) ^ 2 / ε ^ 2)
    rw [mul_zero] at hcm
    refine hcm.congr' ?_
    filter_upwards [hAtop.eventually_gt_atTop 0] with n hn
    field_simp
    ring
  filter_upwards [hchev.eventually (gt_mem_nhds (show (0 : ℝ) < η / 2 by linarith)),
    hAtop.eventually_gt_atTop 0] with n hcn hA0
  rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
  -- the event splits
  set T : (V → ℝ) → ℝ := fun ξ => ∑ v ∈ S n, w n v * (ξ v - clamp m (M : ℝ) (ξ v)) with hT
  set U : (V → ℝ) → ℝ := fun ξ => ∑ v ∈ S n, w n v * (clamp m (M : ℝ) (ξ v) - m - b) with hU
  have hdecomp : ∀ ξ : V → ℝ,
      (∑ v ∈ S n, w n v * (ξ v - m)) = U ξ + b * A n + T ξ := by
    intro ξ
    rw [hU, hT, hA n, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun v _ => by ring
  have hsub : {ξ : V → ℝ | ε * A n ≤ |∑ v ∈ S n, w n v * (ξ v - m)|}
      ⊆ {ξ : V → ℝ | (ε / 3) * A n ≤ |U ξ|} ∪ {ξ : V → ℝ | (ε / 3) * A n ≤ |T ξ|} := by
    intro ξ hξ
    by_contra hcon
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_le] at hcon
    obtain ⟨h1, h2⟩ := hcon
    have hbA : |b * A n| < (ε / 3) * A n := by
      rw [abs_mul, abs_of_nonneg hA0.le]
      exact mul_lt_mul_of_pos_right (lt_of_le_of_lt hb hMe1) hA0
    have : |∑ v ∈ S n, w n v * (ξ v - m)| < ε * A n := by
      rw [hdecomp ξ]
      calc |U ξ + b * A n + T ξ| ≤ |U ξ + b * A n| + |T ξ| := abs_add_le _ _
        _ ≤ |U ξ| + |b * A n| + |T ξ| := by linarith [abs_add_le (U ξ) (b * A n)]
        _ < (ε / 3) * A n + (ε / 3) * A n + (ε / 3) * A n := by linarith
        _ = ε * A n := by ring
    exact absurd hξ (not_le.mpr this)
  have hunion := measureReal_mono (μ := iidLaw V ν) hsub (measure_ne_top _ _)
  refine lt_of_le_of_lt (le_trans hunion (measureReal_union_le _ _)) ?_
  have ht3 : (0 : ℝ) < (ε / 3) * A n := by positivity
  have hUbd := measureReal_trunc_le (V := V) ν m hMnn (S n) (w n) (hw n) ht3
  have hTbd := measureReal_tail_le (V := V) ν m hint hMnn (S n) (w n) (hw n) ht3
  have hTfin : (∑ v ∈ S n, w n v) * e M / ((ε / 3) * A n) = 3 * e M / ε := by
    rw [← hA n]
    field_simp
  rw [hTfin] at hTbd
  have h1 : (iidLaw V ν).real {ξ : V → ℝ | (ε / 3) * A n ≤ |U ξ|} < η / 2 :=
    lt_of_le_of_lt hUbd hcn
  have h2 : (iidLaw V ν).real {ξ : V → ℝ | (ε / 3) * A n ≤ |T ξ|} < η / 4 := by
    refine lt_of_le_of_lt hTbd ?_
    rw [div_lt_iff₀ hε] at *
    nlinarith [hMe2, hε, hη]
  linarith

end RWRS.Support
