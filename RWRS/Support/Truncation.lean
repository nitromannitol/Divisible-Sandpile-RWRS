/-
The marginal of the scenery in the critical regime, and its truncation.

`prop:critical` assumes `E[ξ]=0` and `E[ξ²]<∞`.  The first is recorded here as
the vanishing of the extended mean, which forces both of its halves to be
finite and the Bochner integral to vanish; the second is recorded as
finiteness of the extended variance, which is the second moment.

The proof truncates the marginal at a level `M` and splits it into the centred
truncation and the centred remainder.  As `M` grows the truncation keeps all of
the variance and the remainder keeps none of the second moment, which is what
lets `M` be chosen once, before the vertex and the horizon.
-/
import RWRS.Support.WeakLaw
import RWRS.Support.Explosion
import RWRS.Support.PositivePart

namespace RWRS.Support

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

/-! ### The marginal: mean zero and a finite second moment -/

section Marginal

variable {ν : Measure ℝ}

theorem posPart_ne_top_of_extMean_zero (h : extMean ν = 0) : posPart ν ≠ ⊤ := by
  intro hp
  rw [extMean, hp, EReal.coe_ennreal_top] at h
  rcases eq_or_ne (negPart ν) ⊤ with hn | hn
  · rw [hn, EReal.coe_ennreal_top] at h; simp at h
  · rw [EReal.top_sub (by simpa using hn)] at h; simp at h

theorem negPart_ne_top_of_extMean_zero (h : extMean ν = 0) : negPart ν ≠ ⊤ := by
  intro hn
  rw [extMean, hn, EReal.coe_ennreal_top] at h
  rcases eq_or_ne (posPart ν) ⊤ with hp | hp
  · rw [hp, EReal.coe_ennreal_top] at h; simp at h
  · rw [EReal.sub_top] at h; simp at h

theorem integrable_id_of_extMean_zero (h : extMean ν = 0) :
    Integrable (fun z : ℝ => z) ν :=
  integrable_id_of_finite (posPart_ne_top_of_extMean_zero h) (negPart_ne_top_of_extMean_zero h)

theorem integral_id_zero (h : extMean ν = 0) : ∫ z, z ∂ν = 0 := by
  have hp := posPart_ne_top_of_extMean_zero h
  have hn := negPart_ne_top_of_extMean_zero h
  rw [integral_id_eq (integrable_id_of_finite hp hn)]
  have hpe : ((posPart ν).toReal : EReal) = (posPart ν : EReal) := EReal.coe_ennreal_toReal hp
  have hne : ((negPart ν).toReal : EReal) = (negPart ν : EReal) := EReal.coe_ennreal_toReal hn
  rw [extMean, ← hpe, ← hne, ← EReal.coe_sub] at h
  exact_mod_cast h

theorem evar_eq_lintegral (h : extMean ν = 0) :
    evar ν = ∫⁻ z, ENNReal.ofReal (z ^ 2) ∂ν := by
  rw [evar, ProbabilityTheory.evariance_eq_lintegral_ofReal]
  have hz : ∫ z, id z ∂ν = 0 := integral_id_zero h
  simp only [id_eq] at hz ⊢
  rw [hz]
  simp

theorem integrable_sq_of_evar (h : extMean ν = 0) (hsq : evar ν < ⊤) :
    Integrable (fun z : ℝ => z ^ 2) ν := by
  refine ⟨(measurable_id.pow_const 2).aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral]
  have he : ∀ z : ℝ, ‖z ^ 2‖ₑ = ENNReal.ofReal (z ^ 2) :=
    fun z => Real.enorm_of_nonneg (sq_nonneg z)
  rw [lintegral_congr he, ← evar_eq_lintegral h]
  exact hsq

theorem evar_eq_ofReal (h : extMean ν = 0) (hsq : evar ν < ⊤) :
    evar ν = ENNReal.ofReal (∫ z, z ^ 2 ∂ν) := by
  rw [evar_eq_lintegral h,
    ofReal_integral_eq_lintegral_ofReal (integrable_sq_of_evar h hsq)
      (Filter.Eventually.of_forall fun z => sq_nonneg z)]

theorem integral_sq_pos (h : extMean ν = 0) (hsq : evar ν < ⊤) (hvar : 0 < evar ν) :
    0 < ∫ z, z ^ 2 ∂ν := by
  by_contra hle
  rw [not_lt] at hle
  rw [evar_eq_ofReal h hsq, ENNReal.ofReal_eq_zero.2 hle] at hvar
  exact lt_irrefl 0 hvar

end Marginal

/-! ### The truncated marginal -/

open scoped Classical in
/-- The marginal truncated at level `M`. -/
noncomputable def trunc (M z : ℝ) : ℝ := if |z| ≤ M then z else 0

open scoped Classical in
theorem measurable_trunc (M : ℝ) : Measurable (trunc M) := by
  unfold trunc
  exact Measurable.ite (measurableSet_le (by fun_prop) measurable_const) measurable_id
    measurable_const

theorem abs_trunc_le {M : ℝ} (hM : 0 ≤ M) (z : ℝ) : |trunc M z| ≤ M := by
  classical
  unfold trunc
  split
  · assumption
  · simpa using hM

theorem abs_trunc_le_abs (M z : ℝ) : |trunc M z| ≤ |z| := by
  classical
  unfold trunc
  split
  · exact le_rfl
  · simp

theorem sub_trunc_sq (M z : ℝ) : (z - trunc M z) ^ 2 = z ^ 2 - trunc M z ^ 2 := by
  classical
  unfold trunc
  split
  · ring
  · ring

theorem trunc_sq_le (M z : ℝ) : trunc M z ^ 2 ≤ z ^ 2 := by
  have h := sq_nonneg (z - trunc M z)
  rw [sub_trunc_sq] at h
  linarith

theorem tendsto_trunc (z : ℝ) : Tendsto (fun k : ℕ => trunc (k : ℝ) z) atTop (𝓝 z) := by
  classical
  refine tendsto_const_nhds.congr' ?_
  obtain ⟨k₀, hk₀⟩ := exists_nat_ge |z|
  filter_upwards [eventually_ge_atTop k₀] with k hk
  have hz : |z| ≤ (k : ℝ) := le_trans hk₀ (by exact_mod_cast hk)
  rw [trunc, if_pos hz]

section TruncMoments

variable {ν : Measure ℝ} [IsProbabilityMeasure ν]

theorem integrable_trunc {M : ℝ} (hM : 0 ≤ M) : Integrable (trunc M) ν :=
  integrable_of_bounded (measurable_trunc M) (abs_trunc_le hM)

theorem integrable_trunc_sq {M : ℝ} (hM : 0 ≤ M) :
    Integrable (fun z => trunc M z ^ 2) ν := by
  refine integrable_of_bounded ((measurable_trunc M).pow_const 2) (C := M ^ 2) fun z => ?_
  rw [abs_pow, sq_abs]
  nlinarith [abs_trunc_le hM z, abs_nonneg (trunc M z), sq_abs (trunc M z)]

omit [IsProbabilityMeasure ν] in
theorem tendsto_integral_trunc (hint : Integrable (fun z : ℝ => z) ν) :
    Tendsto (fun k : ℕ => ∫ z, trunc (k : ℝ) z ∂ν) atTop (𝓝 (∫ z, z ∂ν)) := by
  refine tendsto_integral_of_dominated_convergence (fun z => |z|)
    (fun _ => (measurable_trunc _).aestronglyMeasurable) hint.abs (fun _ => ?_)
    (Filter.Eventually.of_forall fun z => tendsto_trunc z)
  filter_upwards with z
  rw [Real.norm_eq_abs]
  exact abs_trunc_le_abs _ z

omit [IsProbabilityMeasure ν] in
theorem tendsto_integral_trunc_sq (hint : Integrable (fun z : ℝ => z ^ 2) ν) :
    Tendsto (fun k : ℕ => ∫ z, trunc (k : ℝ) z ^ 2 ∂ν) atTop (𝓝 (∫ z, z ^ 2 ∂ν)) := by
  refine tendsto_integral_of_dominated_convergence (fun z => z ^ 2)
    (fun _ => ((measurable_trunc _).pow_const 2).aestronglyMeasurable) hint (fun _ => ?_)
    (Filter.Eventually.of_forall fun z => (tendsto_trunc z).pow 2)
  filter_upwards with z
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact trunc_sq_le _ z

end TruncMoments

/-! ### The two centred pieces of the truncation -/

/-- The mean of the truncated marginal. -/
noncomputable def tMean (ν : Measure ℝ) (M : ℝ) : ℝ := ∫ z, trunc M z ∂ν

/-- The second moment of the truncated marginal. -/
noncomputable def tSq (ν : Measure ℝ) (M : ℝ) : ℝ := ∫ z, trunc M z ^ 2 ∂ν

/-- The variance of the truncated marginal, the paper's `s_M^2`. -/
noncomputable def tVar (ν : Measure ℝ) (M : ℝ) : ℝ := tSq ν M - tMean ν M ^ 2

/-- The second moment carried by the tail, the paper's `δ_M^2`. -/
noncomputable def tTail (ν : Measure ℝ) (M : ℝ) : ℝ := (∫ z, z ^ 2 ∂ν) - tSq ν M

/-- The centred truncation `\hat ζ` of `prop:critical`. -/
noncomputable def hhat (ν : Measure ℝ) (M z : ℝ) : ℝ := trunc M z - tMean ν M

/-- The centred remainder, so that `hhat + krem` is the identity. -/
noncomputable def krem (ν : Measure ℝ) (M z : ℝ) : ℝ := z - trunc M z + tMean ν M

section TruncPieces

variable {ν : Measure ℝ} [IsProbabilityMeasure ν]

omit [IsProbabilityMeasure ν] in
theorem hhat_add_krem (M z : ℝ) : hhat ν M z + krem ν M z = z := by
  rw [hhat, krem]; ring

omit [IsProbabilityMeasure ν] in
theorem measurable_hhat (M : ℝ) : Measurable (hhat ν M) :=
  (measurable_trunc M).sub_const _

omit [IsProbabilityMeasure ν] in
theorem measurable_krem (M : ℝ) : Measurable (krem ν M) :=
  (measurable_id.sub (measurable_trunc M)).add_const _

theorem abs_tMean_le {M : ℝ} (hM : 0 ≤ M) : |tMean ν M| ≤ M := by
  rw [tMean]
  calc |∫ z, trunc M z ∂ν| ≤ ∫ z, |trunc M z| ∂ν := abs_integral_le_integral_abs
    _ ≤ ∫ _z, M ∂ν := integral_mono (integrable_trunc hM).abs (integrable_const M)
        (abs_trunc_le hM)
    _ = M := by simp


theorem abs_hhat_le {M : ℝ} (hM : 0 ≤ M) (z : ℝ) : |hhat ν M z| ≤ 2 * M := by
  have h1 := abs_trunc_le hM z
  have h2 := abs_tMean_le (ν := ν) hM
  have h3 : |trunc M z - tMean ν M| ≤ |trunc M z| + |tMean ν M| := by
    simpa [sub_eq_add_neg] using abs_add_le (trunc M z) (-(tMean ν M))
  show |trunc M z - tMean ν M| ≤ 2 * M
  linarith

theorem integrable_hhat {M : ℝ} (hM : 0 ≤ M) : Integrable (hhat ν M) ν :=
  integrable_of_bounded (measurable_hhat M) (abs_hhat_le hM)

theorem integrable_hhat_sq {M : ℝ} (hM : 0 ≤ M) :
    Integrable (fun z => hhat ν M z ^ 2) ν := by
  refine integrable_of_bounded ((measurable_hhat M).pow_const 2) (C := (2 * M) ^ 2) fun z => ?_
  rw [abs_pow, sq_abs]
  nlinarith [abs_hhat_le (ν := ν) hM z, abs_nonneg (hhat ν M z), sq_abs (hhat ν M z), hM]

theorem memLp_trunc {M : ℝ} (hM : 0 ≤ M) : MemLp (trunc M) 2 ν :=
  (memLp_two_iff_integrable_sq (measurable_trunc M).aestronglyMeasurable).2
    (integrable_trunc_sq hM)

theorem integral_hhat {M : ℝ} (hM : 0 ≤ M) : ∫ z, hhat ν M z ∂ν = 0 := by
  show ∫ z, (trunc M z - tMean ν M) ∂ν = 0
  rw [integral_sub (integrable_trunc hM) (integrable_const _), integral_const]
  simp [tMean]

theorem integral_hhat_sq {M : ℝ} (hM : 0 ≤ M) :
    ∫ z, hhat ν M z ^ 2 ∂ν = tVar ν M := by
  have h1 : variance (trunc M) ν = ∫ z, (trunc M z - ∫ w, trunc M w ∂ν) ^ 2 ∂ν :=
    variance_eq_integral (memLp_trunc hM).aemeasurable
  have h2 : variance (trunc M) ν = (∫ z, trunc M z ^ 2 ∂ν) - (∫ z, trunc M z ∂ν) ^ 2 :=
    variance_eq_sub (memLp_trunc hM)
  show ∫ z, (trunc M z - tMean ν M) ^ 2 ∂ν = tVar ν M
  rw [tVar, tSq, tMean, ← h1, h2]

theorem tVar_nonneg {M : ℝ} (hM : 0 ≤ M) : 0 ≤ tVar ν M := by
  rw [← integral_hhat_sq hM]
  exact integral_nonneg fun z => sq_nonneg _

theorem integrable_krem {M : ℝ} (hM : 0 ≤ M) (hint : Integrable (fun z : ℝ => z) ν) :
    Integrable (krem ν M) ν :=
  (hint.sub (integrable_trunc hM)).add (integrable_const _)

theorem integral_krem {M : ℝ} (hM : 0 ≤ M) (hint : Integrable (fun z : ℝ => z) ν)
    (h0 : ∫ z, z ∂ν = 0) : ∫ z, krem ν M z ∂ν = 0 := by
  show ∫ z, ((z - trunc M z) + tMean ν M) ∂ν = 0
  rw [integral_add (f := fun z : ℝ => z - trunc M z) (g := fun _ : ℝ => tMean ν M)
      (hint.sub (integrable_trunc hM)) (integrable_const _),
    integral_sub hint (integrable_trunc hM), integral_const, h0]
  simp [tMean]

omit [IsProbabilityMeasure ν] in
theorem integrable_sub_trunc_sq {M : ℝ} (_hM : 0 ≤ M)
    (hint2 : Integrable (fun z : ℝ => z ^ 2) ν) :
    Integrable (fun z : ℝ => (z - trunc M z) ^ 2) ν := by
  refine Integrable.mono' hint2
    (((measurable_id.sub (measurable_trunc M)).pow_const 2).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), sub_trunc_sq]
  nlinarith [sq_nonneg (trunc M z)]

theorem integral_sub_trunc_sq {M : ℝ} (hM : 0 ≤ M)
    (hint2 : Integrable (fun z : ℝ => z ^ 2) ν) :
    ∫ z, (z - trunc M z) ^ 2 ∂ν = tTail ν M := by
  rw [integral_congr_ae (Filter.Eventually.of_forall fun z => sub_trunc_sq M z),
    integral_sub hint2 (integrable_trunc_sq hM), tTail, tSq]

theorem tTail_nonneg {M : ℝ} (hM : 0 ≤ M) (hint2 : Integrable (fun z : ℝ => z ^ 2) ν) :
    0 ≤ tTail ν M := by
  rw [← integral_sub_trunc_sq hM hint2]
  exact integral_nonneg fun z => sq_nonneg _

omit [IsProbabilityMeasure ν] in
theorem memLp_sub_trunc {M : ℝ} (hM : 0 ≤ M) (hint2 : Integrable (fun z : ℝ => z ^ 2) ν) :
    MemLp (fun z : ℝ => z - trunc M z) 2 ν :=
  (memLp_two_iff_integrable_sq
    (measurable_id.sub (measurable_trunc M)).aestronglyMeasurable).2
    (integrable_sub_trunc_sq hM hint2)

theorem memLp_krem {M : ℝ} (hM : 0 ≤ M) (hint2 : Integrable (fun z : ℝ => z ^ 2) ν) :
    MemLp (krem ν M) 2 ν := by
  have h := (memLp_sub_trunc hM hint2).add (memLp_const (tMean ν M) (μ := ν) (p := 2))
  have he : ((fun z : ℝ => z - trunc M z) + fun _ : ℝ => tMean ν M) = krem ν M := by
    funext z; rw [krem]; rfl
  rwa [he] at h

theorem integrable_krem_sq {M : ℝ} (hM : 0 ≤ M) (hint2 : Integrable (fun z : ℝ => z ^ 2) ν) :
    Integrable (fun z => krem ν M z ^ 2) ν := (memLp_krem hM hint2).integrable_sq

theorem integral_krem_sq_le {M : ℝ} (hM : 0 ≤ M) (hint : Integrable (fun z : ℝ => z) ν)
    (hint2 : Integrable (fun z : ℝ => z ^ 2) ν) (h0 : ∫ z, z ∂ν = 0) :
    ∫ z, krem ν M z ^ 2 ∂ν ≤ tTail ν M := by
  have hgmem := memLp_sub_trunc (ν := ν) hM hint2
  have hga : ∫ z, (z - trunc M z) ∂ν = -tMean ν M := by
    rw [integral_sub hint (integrable_trunc hM), h0]
    simp [tMean]
  have hkr : ∀ z : ℝ, krem ν M z = (z - trunc M z) - ∫ w, (w - trunc M w) ∂ν := by
    intro z
    rw [hga]
    show z - trunc M z + tMean ν M = (z - trunc M z) - -tMean ν M
    ring
  have hpt : ∀ z : ℝ, krem ν M z ^ 2 = ((z - trunc M z) - ∫ w, (w - trunc M w) ∂ν) ^ 2 :=
    fun z => by rw [hkr z]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
    ← variance_eq_integral hgmem.aemeasurable, variance_eq_sub hgmem]
  have hsq : ∫ x : ℝ, ((fun z : ℝ => z - trunc M z) ^ 2) x ∂ν = tTail ν M := by
    rw [← integral_sub_trunc_sq hM hint2]
    exact integral_congr_ae (Filter.Eventually.of_forall fun z => rfl)
  rw [hsq]
  nlinarith [sq_nonneg (∫ z, (z - trunc M z) ∂ν)]


/-! ### The choice of the truncation level -/

omit [IsProbabilityMeasure ν] in
theorem tendsto_tSq (hint2 : Integrable (fun z : ℝ => z ^ 2) ν) :
    Tendsto (fun k : ℕ => tSq ν (k : ℝ)) atTop (𝓝 (∫ z, z ^ 2 ∂ν)) :=
  tendsto_integral_trunc_sq hint2

omit [IsProbabilityMeasure ν] in
theorem tendsto_tMean (hint : Integrable (fun z : ℝ => z) ν) (h0 : ∫ z, z ∂ν = 0) :
    Tendsto (fun k : ℕ => tMean ν (k : ℝ)) atTop (𝓝 0) := by
  have h := tendsto_integral_trunc (ν := ν) hint
  rw [h0] at h
  exact h

omit [IsProbabilityMeasure ν] in
theorem tendsto_tVar (hint : Integrable (fun z : ℝ => z) ν)
    (hint2 : Integrable (fun z : ℝ => z ^ 2) ν) (h0 : ∫ z, z ∂ν = 0) :
    Tendsto (fun k : ℕ => tVar ν (k : ℝ)) atTop (𝓝 (∫ z, z ^ 2 ∂ν)) := by
  have h := (tendsto_tSq (ν := ν) hint2).sub ((tendsto_tMean hint h0).pow 2)
  simpa [tVar] using h

omit [IsProbabilityMeasure ν] in
theorem tendsto_tTail (hint2 : Integrable (fun z : ℝ => z ^ 2) ν) :
    Tendsto (fun k : ℕ => tTail ν (k : ℝ)) atTop (𝓝 0) := by
  have h := tendsto_const_nhds (x := ∫ z, z ^ 2 ∂ν) (f := atTop (α := ℕ))
  simpa [tTail] using h.sub (tendsto_tSq (ν := ν) hint2)

/-- The truncation level of `prop:critical`: the truncated marginal keeps a
positive variance and the tail keeps so little of the second moment that the
positive-part constant still dominates it.  The level depends only on the law
of the scenery. -/
theorem exists_good_trunc (h0 : extMean ν = 0) (hsq : evar ν < ⊤) (hvar : 0 < evar ν) :
    ∃ M : ℝ, 0 < M ∧ 0 < tVar ν M ∧
      Real.sqrt (tTail ν M) < cStar * Real.sqrt (tVar ν M) := by
  have hint : Integrable (fun z : ℝ => z) ν := integrable_id_of_extMean_zero h0
  have hint2 : Integrable (fun z : ℝ => z ^ 2) ν := integrable_sq_of_evar h0 hsq
  have hz : ∫ z, z ∂ν = 0 := integral_id_zero h0
  have hm2 : 0 < ∫ z, z ^ 2 ∂ν := integral_sq_pos h0 hsq hvar
  have hsqrt : 0 < Real.sqrt (∫ z, z ^ 2 ∂ν) := Real.sqrt_pos.2 hm2
  set ε : ℝ := cStar * Real.sqrt (∫ z, z ^ 2 ∂ν) / 2 with hε
  have hεpos : 0 < ε := by
    rw [hε]; exact div_pos (mul_pos cStar_pos hsqrt) two_pos
  have hA : Tendsto (fun k : ℕ => Real.sqrt (tVar ν (k : ℝ))) atTop
      (𝓝 (Real.sqrt (∫ z, z ^ 2 ∂ν))) :=
    (Real.continuous_sqrt.tendsto _).comp (tendsto_tVar hint hint2 hz)
  have hB : Tendsto (fun k : ℕ => Real.sqrt (tTail ν (k : ℝ))) atTop (𝓝 0) := by
    have h : Tendsto (fun k : ℕ => Real.sqrt (tTail ν (k : ℝ))) atTop (𝓝 (Real.sqrt 0)) :=
      (Real.continuous_sqrt.tendsto 0).comp (tendsto_tTail (ν := ν) hint2)
    rwa [Real.sqrt_zero] at h
  obtain ⟨k, hk1, hkA, hkB⟩ : ∃ k : ℕ, 1 ≤ k ∧
      Real.sqrt (∫ z, z ^ 2 ∂ν) / 2 < Real.sqrt (tVar ν (k : ℝ)) ∧
      Real.sqrt (tTail ν (k : ℝ)) < ε := by
    have h1 := hA.eventually (eventually_gt_nhds (by linarith : Real.sqrt (∫ z, z ^ 2 ∂ν) / 2
      < Real.sqrt (∫ z, z ^ 2 ∂ν)))
    have h2 := hB.eventually (gt_mem_nhds hεpos)
    exact ((eventually_ge_atTop 1).and (h1.and h2)).exists.imp
      fun k hk => ⟨hk.1, hk.2.1, hk.2.2⟩
  refine ⟨(k : ℝ), by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hk1, ?_, ?_⟩
  · have hnn : 0 ≤ tVar ν (k : ℝ) := tVar_nonneg (by positivity)
    rcases eq_or_lt_of_le hnn with heq | hlt
    · rw [← heq] at hkA; simp at hkA; linarith
    · exact hlt
  · calc Real.sqrt (tTail ν (k : ℝ)) < ε := hkB
      _ = cStar * (Real.sqrt (∫ z, z ^ 2 ∂ν) / 2) := by rw [hε]; ring
      _ < cStar * Real.sqrt (tVar ν (k : ℝ)) := by
          exact mul_lt_mul_of_pos_left hkA cStar_pos

end TruncPieces

end RWRS.Support
