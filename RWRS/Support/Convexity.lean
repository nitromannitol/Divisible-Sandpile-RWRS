/-
The convexity reduction for symmetric sceneries (`prop:convexity-reduction`).

Both optimal stopping suprema are suprema of linear functionals of the
scenery, one for each bounded stopping rule, so both are convex in the
scenery.  A symmetric scenery is the midpoint of itself and of the copy
obtained by reflecting its large values, which has the same law, and their
common midpoint is the bounded truncation.  Convexity therefore transfers
explosion from the truncation to the scenery, on an event of probability at
least one half, and the zero-one law finishes.
-/
import RWRS.Support.Dyadic

namespace RWRS.Support

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

/-! ### The two suprema are convex in the scenery -/

theorem payoff_midpoint (ξ η : V → ℝ) (n : ℕ) (X : ℕ → V) :
    payoff G (fun v => (ξ v + η v) / 2) n X = (payoff G ξ n X + payoff G η n X) / 2 := by
  rw [payoff, payoff, payoff, ← Finset.sum_add_distrib, Finset.sum_div]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem walkExp_midpoint (n : ℕ) (x : V) (F F' : (ℕ → V) → ℝ) :
    walkExp G n x (fun X => (F X + F' X) / 2)
      = (walkExp G n x F + walkExp G n x F') / 2 := by
  have h : (fun X : ℕ → V => (F X + F' X) / 2)
      = fun X => (1 / 2 : ℝ) * (F X + F' X) := by funext X; ring
  rw [h, walkExp_const_mul, walkExp_add]
  ring

theorem ofReal_midpoint_le (a b : ℝ) :
    ENNReal.ofReal ((a + b) / 2) ≤ (ENNReal.ofReal a + ENNReal.ofReal b) / 2 := by
  rw [ENNReal.ofReal_div_of_pos two_pos]
  have h2 : ENNReal.ofReal (2 : ℝ) = 2 := by simp
  rw [h2]
  exact ENNReal.div_le_div_right ENNReal.ofReal_add_le 2

theorem supStopValue_midpoint_le [Infinite V] (ξ η : V → ℝ) (o : V) :
    supStopValue G (fun v => (ξ v + η v) / 2) o
      ≤ (supStopValue G ξ o + supStopValue G η o) / 2 := by
  refine iSup_le fun n => iSup_le fun a => iSup_le fun ha => ?_
  obtain ⟨τ, hτ, hle, rfl⟩ := ha
  have hval : walkExp G n o (fun X => payoff G (fun v => (ξ v + η v) / 2) (τ X) X)
      = (walkExp G n o (fun X => payoff G ξ (τ X) X)
        + walkExp G n o (fun X => payoff G η (τ X) X)) / 2 := by
    rw [← walkExp_midpoint]
    exact walkExp_congr fun X _ => payoff_midpoint ξ η (τ X) X
  rw [hval]
  refine le_trans (ofReal_midpoint_le _ _) (ENNReal.div_le_div_right (add_le_add ?_ ?_) 2)
  · exact le_iSup_of_le n (le_iSup_of_le _ (le_iSup_of_le ⟨τ, hτ, hle, rfl⟩ le_rfl))
  · exact le_iSup_of_le n (le_iSup_of_le _ (le_iSup_of_le ⟨τ, hτ, hle, rfl⟩ le_rfl))

theorem supMeanPayoff_midpoint_le [Infinite V] (ξ η : V → ℝ) (o : V) :
    supMeanPayoff G (fun v => (ξ v + η v) / 2) o
      ≤ (supMeanPayoff G ξ o + supMeanPayoff G η o) / 2 := by
  refine iSup_le fun n => ?_
  have hval : meanPayoff G (fun v => (ξ v + η v) / 2) n o
      = (meanPayoff G ξ n o + meanPayoff G η n o) / 2 := by
    rw [meanPayoff, meanPayoff, meanPayoff, ← walkExp_midpoint]
    exact walkExp_congr fun X _ => payoff_midpoint ξ η n X
  rw [hval]
  refine le_trans (ofReal_midpoint_le _ _) (ENNReal.div_le_div_right (add_le_add ?_ ?_) 2)
  · exact le_iSup (fun k : ℕ => ENNReal.ofReal (meanPayoff G ξ k o)) n
  · exact le_iSup (fun k : ℕ => ENNReal.ofReal (meanPayoff G η k o)) n

/-! ### The zero-one law for the value over bounded stopping rules -/

theorem supStopValue_eq_odometerLimit [Infinite V] (hG : G.Connected) (ξ : V → ℝ) (x : V) :
    supStopValue G ξ x = odometerLimit G (fun u => ξ u + 1) x := by
  have h := RWRS.Frozen.rwInfinite hG (fun u => ξ u + 1) x
  rw [excess_add_one] at h
  exact h.symm

theorem measurableSet_supStopValue_top [Infinite V] (hG : G.Connected) (o : V) :
    MeasurableSet {ξ : V → ℝ | supStopValue G ξ o = ⊤} := by
  have heq : {ξ : V → ℝ | supStopValue G ξ o = ⊤}
      = (fun ξ : V → ℝ => (fun u => ξ u + 1)) ⁻¹'
        {σ : V → ℝ | odometerLimit G σ o = ⊤} := by
    ext ξ
    simp only [Set.mem_preimage, Set.mem_setOf_eq, supStopValue_eq_odometerLimit hG]
  rw [heq]
  exact measurable_shift ((measurable_odometerLimit o) (measurableSet_singleton ⊤))

theorem supStopValue_perm_iff [Infinite V] (hVF : RWRS.External.VoltageFunction G)
    (hG : G.Connected) (σ : V → ℝ) (π : Equiv.Perm V) (hfin : {i : V | π i ≠ i}.Finite)
    (o : V) :
    supStopValue G (excess fun v => σ (π v)) o = ⊤ ↔ supStopValue G (excess σ) o = ⊤ := by
  obtain ⟨C, hC0, hle⟩ := perm_sup_le hVF hG σ π hfin
  obtain ⟨C', hC0', hle'⟩ := perm_sup_le hVF hG (fun v => σ (π v)) π.symm
    (perm_symm_finite hfin)
  have hback : (fun w => σ (π (π.symm w))) = σ := funext fun v => by simp
  constructor
  · intro h
    have h1 := (hle o).1
    rw [h, top_le_iff] at h1
    rcases ENNReal.add_eq_top.mp h1 with h2 | h2
    · exact h2
    · exact absurd h2 ENNReal.ofReal_ne_top
  · intro h
    have h1 := (hle' o).1
    rw [hback] at h1
    rw [h, top_le_iff] at h1
    rcases ENNReal.add_eq_top.mp h1 with h2 | h2
    · exact h2
    · exact absurd h2 ENNReal.ofReal_ne_top

theorem measure_supStopValue_top_zero_or_one [Infinite V]
    (hVF : RWRS.External.VoltageFunction G) (hG : G.Connected)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (o : V) :
    iidLaw V ν {ξ : V → ℝ | supStopValue G ξ o = ⊤} = 0 ∨
      iidLaw V ν {ξ : V → ℝ | supStopValue G ξ o = ⊤} = 1 := by
  classical
  refine LatticeProb.measure_zero_or_one_of_exchangeable ν
    (measurableSet_supStopValue_top hG o) fun π hπ => ?_
  ext ξ
  simp only [Set.mem_preimage, Set.mem_setOf_eq]
  have h := supStopValue_perm_iff hVF hG (fun u => ξ u + 1) π hπ o
  rw [excess_add_one (fun v => ξ (π v)), excess_add_one ξ] at h
  exact h

/-! ### The reflected copy of a symmetric marginal -/

open scoped Classical in
/-- The scenery with its large values reflected. -/
noncomputable def flipAt (M z : ℝ) : ℝ := if |z| ≤ M then z else -z

open scoped Classical in
theorem measurable_flipAt (M : ℝ) : Measurable (flipAt M) := by
  unfold flipAt
  exact Measurable.ite (measurableSet_le (by fun_prop) measurable_const) measurable_id
    measurable_neg

theorem trunc_eq_midpoint (M z : ℝ) : trunc M z = (z + flipAt M z) / 2 := by
  classical
  unfold trunc flipAt
  split
  · ring
  · ring

theorem flipAt_neg (M z : ℝ) : flipAt M (-z) = -flipAt M z := by
  classical
  unfold flipAt
  rw [abs_neg]
  split
  · rfl
  · ring

theorem trunc_neg (M z : ℝ) : trunc M (-z) = -trunc M z := by
  classical
  unfold trunc
  rw [abs_neg]
  split
  · rfl
  · ring

theorem map_flipAt (ν : Measure ℝ) (hsym : IsSymmetric ν) (M : ℝ) :
    ν.map (flipAt M) = ν := by
  classical
  refine Measure.ext fun A hA => ?_
  rw [Measure.map_apply (measurable_flipAt M) hA]
  set S : Set ℝ := {z : ℝ | |z| ≤ M} with hSdef
  have hSm : MeasurableSet S := measurableSet_le (by fun_prop) measurable_const
  have hSneg : ∀ z : ℝ, (-z ∈ S) ↔ (z ∈ S) := by
    intro z; simp [hSdef, abs_neg]
  have hpre : flipAt M ⁻¹' A
      = (A ∩ S) ∪ ((fun z : ℝ => -z) ⁻¹' (A ∩ Sᶜ)) := by
    ext z
    by_cases h : |z| ≤ M
    · have hz : z ∈ S := h
      simp only [Set.mem_preimage, Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff,
        flipAt, if_pos h]
      constructor
      · intro hz'; exact Or.inl ⟨hz', hz⟩
      · rintro (⟨hz', _⟩ | ⟨_, hns⟩)
        · exact hz'
        · exact absurd ((hSneg z).2 hz) hns
    · have hz : z ∉ S := h
      simp only [Set.mem_preimage, Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff,
        flipAt, if_neg h]
      constructor
      · intro hz'; exact Or.inr ⟨hz', fun hc => hz ((hSneg z).1 hc)⟩
      · rintro (⟨_, hs⟩ | ⟨hz', _⟩)
        · exact absurd hs hz
        · exact hz'
  have hdisj : Disjoint (A ∩ S) ((fun z : ℝ => -z) ⁻¹' (A ∩ Sᶜ)) := by
    refine Set.disjoint_left.2 fun z hz hz' => ?_
    exact hz'.2 ((hSneg z).2 hz.2)
  have hmeas2 : MeasurableSet ((fun z : ℝ => -z) ⁻¹' (A ∩ Sᶜ)) :=
    measurable_neg (hA.inter hSm.compl)
  rw [hpre, measure_union hdisj hmeas2]
  have hflipmeas : ν ((fun z : ℝ => -z) ⁻¹' (A ∩ Sᶜ)) = ν (A ∩ Sᶜ) := by
    rw [← Measure.map_apply measurable_neg (hA.inter hSm.compl), hsym]
  rw [hflipmeas, ← Set.sdiff_eq]
  exact measure_inter_add_sdiff A hSm

/-! ### The bounded truncation of a symmetric marginal -/

theorem lintegral_of_symmetric {ρ : Measure ℝ} (hsym : IsSymmetric ρ) {f : ℝ → ℝ≥0∞}
    (hf : Measurable f) : ∫⁻ z, f z ∂ρ = ∫⁻ z, f (-z) ∂ρ := by
  conv_lhs => rw [← hsym]
  rw [lintegral_map hf measurable_neg]

theorem posPart_eq_negPart_of_symmetric {ρ : Measure ℝ} (hsym : IsSymmetric ρ) :
    posPart ρ = negPart ρ := by
  rw [posPart, negPart, lintegral_of_symmetric hsym ENNReal.measurable_ofReal]

theorem extMean_eq_zero_of_symmetric {ρ : Measure ℝ} (hsym : IsSymmetric ρ)
    (hfin : posPart ρ ≠ ⊤) : extMean ρ = 0 := by
  have hpn := posPart_eq_negPart_of_symmetric hsym
  have hcoe : ((posPart ρ).toReal : EReal) = (posPart ρ : EReal) :=
    EReal.coe_ennreal_toReal hfin
  rw [extMean, ← hpn, ← hcoe, ← EReal.coe_sub]
  norm_num

theorem isSymmetric_map_trunc (ν : Measure ℝ) (hsym : IsSymmetric ν) (M : ℝ) :
    IsSymmetric (ν.map (trunc M)) := by
  rw [IsSymmetric, Measure.map_map measurable_neg (measurable_trunc M)]
  have h : (fun z : ℝ => -z) ∘ (trunc M) = (trunc M) ∘ (fun z : ℝ => -z) := by
    funext z
    simp only [Function.comp_apply]
    rw [trunc_neg]
  rw [h, ← Measure.map_map (measurable_trunc M) measurable_neg, hsym]

theorem ae_abs_le_map_trunc (ν : Measure ℝ) [IsProbabilityMeasure ν] {M : ℝ} (hM : 0 ≤ M) :
    ∀ᵐ z ∂(ν.map (trunc M)), |z| ≤ M := by
  rw [ae_map_iff (measurable_trunc M).aemeasurable
    (measurableSet_le (by fun_prop) measurable_const)]
  exact Filter.Eventually.of_forall fun z => abs_trunc_le hM z

theorem posPart_map_trunc_ne_top (ν : Measure ℝ) [IsProbabilityMeasure ν] {M : ℝ}
    (hM : 0 ≤ M) : posPart (ν.map (trunc M)) ≠ ⊤ := by
  refine ne_top_of_le_ne_top (b := ENNReal.ofReal M) ENNReal.ofReal_ne_top ?_
  rw [posPart]
  calc ∫⁻ z, ENNReal.ofReal z ∂(ν.map (trunc M))
      ≤ ∫⁻ _z, ENNReal.ofReal M ∂(ν.map (trunc M)) := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_abs_le_map_trunc ν hM] with z hz
        exact ENNReal.ofReal_le_ofReal (le_trans (le_abs_self z) hz)
    _ ≤ ENNReal.ofReal M := by
        haveI : IsProbabilityMeasure (ν.map (trunc M)) :=
          Measure.isProbabilityMeasure_map (measurable_trunc M).aemeasurable
        rw [lintegral_const, measure_univ, mul_one]

theorem evar_map_trunc_lt_top (ν : Measure ℝ) [IsProbabilityMeasure ν] {M : ℝ}
    (hM : 0 ≤ M) : evar (ν.map (trunc M)) < ⊤ := by
  haveI : IsProbabilityMeasure (ν.map (trunc M)) :=
    Measure.isProbabilityMeasure_map (measurable_trunc M).aemeasurable
  refine ProbabilityTheory.evariance_lt_top (μ := ν.map (trunc M)) (X := id) ?_
  refine (memLp_two_iff_integrable_sq aestronglyMeasurable_id).2 ?_
  refine Integrable.mono' (integrable_const (M ^ 2))
    ((measurable_id.pow_const 2).aestronglyMeasurable) ?_
  filter_upwards [ae_abs_le_map_trunc ν hM] with z hz
  rw [Real.norm_eq_abs]
  simp only [id_eq]
  rw [abs_pow, sq_abs]
  nlinarith [abs_nonneg z, sq_abs z]

theorem eq_dirac_of_ae_zero (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h : ν {z : ℝ | z ≠ 0} = 0) : ν = Measure.dirac 0 := by
  refine Measure.ext fun A hA => ?_
  have hcompl : MeasurableSet ({(0 : ℝ)} : Set ℝ) := measurableSet_singleton 0
  have hzero : ν (A \ {0}) = 0 := by
    refine measure_mono_null (fun z hz => ?_) h
    exact fun hc => hz.2 (by rw [hc]; exact rfl)
  have hsplit : ν (A ∩ {0}) + ν (A \ {0}) = ν A := measure_inter_add_sdiff A hcompl
  rw [hzero, add_zero] at hsplit
  rw [← hsplit, Measure.dirac_apply' 0 hA]
  by_cases h0 : (0 : ℝ) ∈ A
  · have hAi : A ∩ ({0} : Set ℝ) = {0} := by
      ext z; constructor
      · exact fun hz => hz.2
      · intro hz; rw [Set.mem_singleton_iff] at hz; exact ⟨by rw [hz]; exact h0, hz⟩
    have hone : ν ({(0 : ℝ)} : Set ℝ) = 1 := by
      have := measure_add_measure_compl (μ := ν) hcompl
      have hc : ν ({(0 : ℝ)} : Set ℝ)ᶜ = 0 := by
        refine measure_mono_null (fun z hz => ?_) h
        exact fun hc => hz (by rw [hc]; exact rfl)
      rw [hc, add_zero, measure_univ] at this
      exact this
    rw [hAi, hone, Set.indicator_of_mem h0]
    rfl
  · have hAi : A ∩ ({0} : Set ℝ) = ∅ := by
      ext z; constructor
      · rintro ⟨hz, hz0⟩
        rw [Set.mem_singleton_iff] at hz0
        exact absurd (by rw [← hz0]; exact hz) h0
      · exact fun hz => absurd hz (Set.notMem_empty z)
    rw [hAi, measure_empty, Set.indicator_of_notMem h0]

theorem exists_trunc_level (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hnz : ν ≠ Measure.dirac 0) :
    ∃ M : ℝ, 0 < M ∧ 0 < ν {z : ℝ | trunc M z ≠ 0} := by
  classical
  have hpos : ν {z : ℝ | z ≠ 0} ≠ 0 := fun h => hnz (eq_dirac_of_ae_zero ν h)
  by_contra hcon
  rw [not_exists] at hcon
  replace hcon : ∀ M : ℝ, 0 < M → ν {z : ℝ | trunc M z ≠ 0} ≤ 0 := by
    intro M hM
    have := hcon M
    rw [not_and, not_lt] at this
    exact this hM
  refine hpos ?_
  have hsub : {z : ℝ | z ≠ 0} ⊆ ⋃ k : ℕ, {z : ℝ | trunc ((k : ℝ) + 1) z ≠ 0} := by
    intro z hz
    obtain ⟨k, hk⟩ := exists_nat_ge |z|
    refine Set.mem_iUnion.2 ⟨k, ?_⟩
    have hle : |z| ≤ (k : ℝ) + 1 := by linarith
    simp only [Set.mem_setOf_eq, trunc, if_pos hle]
    exact hz
  refine measure_mono_null hsub ?_
  refine measure_iUnion_null fun k => ?_
  exact le_antisymm (hcon ((k : ℝ) + 1) (by positivity)) bot_le

theorem measure_map_trunc_ne_zero (ν : Measure ℝ) [IsProbabilityMeasure ν] {M : ℝ}
    (hpos : 0 < ν {z : ℝ | trunc M z ≠ 0}) :
    0 < (ν.map (trunc M)) {z : ℝ | z ≠ 0} := by
  have hms : MeasurableSet {z : ℝ | z ≠ 0} := (measurableSet_singleton (0 : ℝ)).compl
  rw [Measure.map_apply (measurable_trunc M) hms]
  exact hpos

theorem evar_map_trunc_pos (ν : Measure ℝ) [IsProbabilityMeasure ν] (hsym : IsSymmetric ν)
    {M : ℝ} (hM : 0 ≤ M) (hpos : 0 < ν {z : ℝ | trunc M z ≠ 0}) :
    0 < evar (ν.map (trunc M)) := by
  haveI : IsProbabilityMeasure (ν.map (trunc M)) :=
    Measure.isProbabilityMeasure_map (measurable_trunc M).aemeasurable
  have hmean : extMean (ν.map (trunc M)) = 0 :=
    extMean_eq_zero_of_symmetric (isSymmetric_map_trunc ν hsym M)
      (posPart_map_trunc_ne_top ν hM)
  have hzero : ∫ z, z ∂(ν.map (trunc M)) = 0 := integral_id_zero hmean
  rcases eq_zero_or_pos (evar (ν.map (trunc M))) with h | h
  · exfalso
    have hae := (ProbabilityTheory.evariance_eq_zero_iff (μ := ν.map (trunc M))
      (X := id) aemeasurable_id).1 h
    simp only [id_eq] at hae
    rw [hzero] at hae
    have hnull : (ν.map (trunc M)) {z : ℝ | z ≠ 0} = 0 := by
      refine measure_mono_null (fun z hz => ?_) (ae_iff.1 hae)
      exact fun hc => hz (by simpa using hc)
    have hcontra := measure_map_trunc_ne_zero ν (M := M) hpos
    rw [hnull] at hcontra
    exact lt_irrefl _ hcontra
  · exact h

/-! ### The reduction -/

theorem measurable_truncMap (M : ℝ) :
    Measurable fun ξ : V → ℝ => (fun v => trunc M (ξ v)) :=
  measurable_pi_lambda _ fun v => (measurable_trunc M).comp (measurable_pi_apply v)

theorem measurable_flipMap (M : ℝ) :
    Measurable fun ξ : V → ℝ => (fun v => flipAt M (ξ v)) :=
  measurable_pi_lambda _ fun v => (measurable_flipAt M).comp (measurable_pi_apply v)

/-- The reduction of `prop:convexity-reduction`, for either of the two
convex functionals of the scenery. -/
theorem convexity_reduction_aux (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hnz : ν ≠ Measure.dirac 0) (hsym : IsSymmetric ν)
    (F : (V → ℝ) → ℝ≥0∞)
    (hmid : ∀ ξ η : V → ℝ, F (fun v => (ξ v + η v) / 2) ≤ (F ξ + F η) / 2)
    (hmeasA : MeasurableSet {ξ : V → ℝ | F ξ = ⊤})
    (hzo : iidLaw V ν {ξ : V → ℝ | F ξ = ⊤} = 0 ∨
      iidLaw V ν {ξ : V → ℝ | F ξ = ⊤} = 1)
    (hhyp : ∀ ρ : Measure ℝ, IsProbabilityMeasure ρ → extMean ρ = 0 → 0 < evar ρ →
      evar ρ < ⊤ → ∀ᵐ ξ ∂(iidLaw V ρ), F ξ = ⊤) :
    ∀ᵐ ξ ∂(iidLaw V ν), F ξ = ⊤ := by
  classical
  obtain ⟨M, hM, hMpos⟩ := exists_trunc_level ν hnz
  set ρ : Measure ℝ := ν.map (trunc M) with hρ
  haveI : IsProbabilityMeasure ρ :=
    Measure.isProbabilityMeasure_map (measurable_trunc M).aemeasurable
  have hmeanρ : extMean ρ = 0 :=
    extMean_eq_zero_of_symmetric (isSymmetric_map_trunc ν hsym M)
      (posPart_map_trunc_ne_top ν hM.le)
  have hvarρ : 0 < evar ρ := evar_map_trunc_pos ν hsym hM.le hMpos
  have hsqρ : evar ρ < ⊤ := evar_map_trunc_lt_top ν hM.le
  have h1 := hhyp ρ inferInstance hmeanρ hvarρ hsqρ
  rw [hρ, ← iidLaw_map ν (measurable_trunc M)] at h1
  rw [ae_map_iff (measurable_truncMap M).aemeasurable hmeasA] at h1
  -- convexity transfers explosion to the scenery or to its reflection
  have h2 : ∀ᵐ ξ ∂(iidLaw V ν),
      ξ ∈ {ξ : V → ℝ | F ξ = ⊤} ∪
        (fun ξ : V → ℝ => (fun v => flipAt M (ξ v))) ⁻¹' {ξ : V → ℝ | F ξ = ⊤} := by
    filter_upwards [h1] with ξ hξ
    have heq : (fun v => trunc M (ξ v))
        = fun v => (ξ v + (fun v => flipAt M (ξ v)) v) / 2 := by
      funext v; exact trunc_eq_midpoint M (ξ v)
    rw [heq] at hξ
    have hle := hmid ξ (fun v => flipAt M (ξ v))
    rw [hξ, top_le_iff] at hle
    have hadd : F ξ + F (fun v => flipAt M (ξ v)) = ⊤ := by
      rcases (ENNReal.div_eq_top).1 hle with ⟨_, h0⟩ | ⟨htop, _⟩
      · exact absurd h0 two_ne_zero
      · exact htop
    rcases ENNReal.add_eq_top.1 hadd with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hmap : (iidLaw V ν).map (fun ξ : V → ℝ => (fun v => flipAt M (ξ v))) = iidLaw V ν := by
    rw [iidLaw_map ν (measurable_flipAt M), map_flipAt ν hsym M]
  have hflipmeas : iidLaw V ν
      ((fun ξ : V → ℝ => (fun v => flipAt M (ξ v))) ⁻¹' {ξ : V → ℝ | F ξ = ⊤})
      = iidLaw V ν {ξ : V → ℝ | F ξ = ⊤} := by
    rw [← Measure.map_apply (measurable_flipMap M) hmeasA, hmap]
  have hAm : MeasurableSet ({ξ : V → ℝ | F ξ = ⊤} ∪
      (fun ξ : V → ℝ => (fun v => flipAt M (ξ v))) ⁻¹' {ξ : V → ℝ | F ξ = ⊤}) :=
    hmeasA.union (measurable_flipMap M hmeasA)
  have hfull : iidLaw V ν ({ξ : V → ℝ | F ξ = ⊤} ∪
      (fun ξ : V → ℝ => (fun v => flipAt M (ξ v))) ⁻¹' {ξ : V → ℝ | F ξ = ⊤}) = 1 := by
    have h0 : iidLaw V ν ({ξ : V → ℝ | F ξ = ⊤} ∪
        (fun ξ : V → ℝ => (fun v => flipAt M (ξ v))) ⁻¹' {ξ : V → ℝ | F ξ = ⊤})ᶜ = 0 :=
      ae_iff.1 h2
    have hsum := measure_add_measure_compl (μ := iidLaw V ν) hAm
    rw [h0, add_zero, measure_univ] at hsum
    exact hsum
  have hne : iidLaw V ν {ξ : V → ℝ | F ξ = ⊤} ≠ 0 := by
    intro h0
    have hle := measure_union_le (μ := iidLaw V ν) {ξ : V → ℝ | F ξ = ⊤}
      ((fun ξ : V → ℝ => (fun v => flipAt M (ξ v))) ⁻¹' {ξ : V → ℝ | F ξ = ⊤})
    rw [hfull, h0, hflipmeas, h0, add_zero] at hle
    simp at hle
  have hone : iidLaw V ν {ξ : V → ℝ | F ξ = ⊤} = 1 := hzo.resolve_left hne
  rw [ae_iff]
  have hcompl : {ξ : V → ℝ | ¬ F ξ = ⊤} = {ξ : V → ℝ | F ξ = ⊤}ᶜ := rfl
  rw [hcompl, measure_compl hmeasA (measure_ne_top _ _), hone]
  simp

end RWRS.Support
