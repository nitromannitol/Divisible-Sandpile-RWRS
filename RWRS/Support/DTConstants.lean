import RWRS.Support.DTTrapFamily
import RWRS.Support.Truncation

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace RWRS.Support

variable {V : Type*} [MeasurableSpace V] [MeasurableSingletonClass V]

omit [MeasurableSpace V] [MeasurableSingletonClass V] in
/-- **Choice of the trap threshold.**  For a probability law `ν` on `ℝ` and a
block-size bound `M` there is `ε > 0` with every trap block of size at most
`M + 1` firing with probability at most `1/2`; equivalently the complement
of every such trap event has probability at least `1/2`. -/
theorem exists_eps_trapEvent_le {ν : Measure ℝ} [IsProbabilityMeasure ν] (M : ℕ) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ C : Finset V, C.Nonempty → C.card ≤ M + 1 →
        RWRS.iidLaw V ν (trapEvent C ε) ≤ 1/2 := by
  classical
  have hmono : Monotone (fun n : ℕ => Set.Ioi (-(n : ℝ))) := by
    intro a b hab
    exact Set.Ioi_subset_Ioi (by
      have hc : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
      have h2 : (-(b : ℝ)) ≤ -(a : ℝ) := by exact_mod_cast neg_le_neg hc
      exact h2)
  have h1 : Filter.Tendsto (fun n : ℕ => ν (Set.Ioi (-(n : ℝ)))) Filter.atTop
      (nhds (ν (⋃ n : ℕ, Set.Ioi (-(n : ℝ))))) :=
    tendsto_measure_iUnion_atTop (μ := ν) hmono
  have hu : (⋃ n : ℕ, Set.Ioi (-(n : ℝ))) = Set.univ := by
    ext x
    simp
    obtain ⟨n, hn⟩ := exists_nat_gt (-x)
    exact ⟨n, by
      have h2 : (-x : ℝ) < (n : ℝ) := by exact_mod_cast hn
      linarith⟩
  rw [hu, measure_univ] at h1
  have hgt : ∀ᶠ n : ℕ in Filter.atTop, (1 / 2 : ℝ≥0∞) < ν (Set.Ioi (-(n : ℝ))) :=
    h1.eventually (lt_mem_nhds (by norm_num))
  obtain ⟨N, hN⟩ := mem_atTop_sets.mp hgt
  refine ⟨((N + 1) : ℝ), (by exact_mod_cast Nat.succ_pos N), ?_⟩
  intro C hCne hC
  have hIic : ν (Set.Iic (-((N + 1) : ℝ))) ≤ 1 / 2 := by
    have h := measure_add_measure_compl (μ := ν)
      (measurableSet_Iic (a := -((N + 1) : ℝ)))
    have heq : (Set.Iic (-((N + 1) : ℝ)))ᶜ = Set.Ioi (-((N + 1) : ℝ)) := by
      ext x
      simp
    rw [heq] at h
    rw [measure_univ] at h
    have hN' : (1 / 2 : ℝ≥0∞) < ν (Set.Ioi (-((N + 1) : ℝ))) := by
      simpa using hN (N + 1) (by omega)
    have hsub : ν (Set.Iic (-((N + 1) : ℝ))) = 1 - ν (Set.Ioi (-((N + 1) : ℝ))) := by
      rw [← h]
      simp
    rw [hsub]
    have h6 : (1 : ℝ≥0∞) - 1/2 = 1/2 := by
      have h4 : (2 : ℝ≥0∞) * 2⁻¹ = 1 := ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
      have h5 : (1/2 : ℝ≥0∞) = 2⁻¹ := by norm_num
      rw [h5, ← h4, two_mul]
      simp
    rw [← h6]
    exact tsub_le_tsub_left hN'.le _
  have hmeas := measure_trapEvent ν C ((N + 1) : ℝ)
  rw [hmeas]
  have hp : ν (Set.Iic (-((N + 1) : ℝ))) ≤ 1 / 2 := hIic
  have hple : ν (Set.Iic (-((N + 1) : ℝ))) ≤ 1 := le_trans hp (by norm_num)
  have hcard1 : 1 ≤ C.card := by
    have := Finset.card_pos.mpr hCne
    omega
  have hstep : ν (Set.Iic (-((N + 1) : ℝ))) ^ C.card ≤ ν (Set.Iic (-((N + 1) : ℝ))) := by
    have h1 : ν (Set.Iic (-((N + 1) : ℝ))) ^ C.card ≤ ν (Set.Iic (-((N + 1) : ℝ))) ^ 1 :=
      pow_le_pow_right_of_le_one' hple hcard1
    simpa using h1
  exact le_trans hstep hp

variable {ν : Measure ℝ}

/-- **Positive mass below some `-ε` level.** -/
theorem exists_eps_pos_mass [IsProbabilityMeasure ν]
    (h0 : RWRS.extMean ν = 0) (hvar : 0 < RWRS.evar ν) :
    ∃ ε : ℝ, 0 < ε ∧ 0 < ν (Set.Iic (-ε)) := by
  by_contra hcon
  push Not at hcon
  have hmono : Monotone (fun n : ℕ => Set.Iic (-((n + 1 : ℕ) : ℝ)⁻¹)) := by
    intro a b hab
    exact (Set.Iic_subset_Iic).mpr (by
      have hle : ((a + 1 : ℕ) : ℝ) ≤ ((b + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.add_le_add_right hab 1
      have ha : (0 : ℝ) < ((a + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos a
      exact neg_le_neg (inv_anti₀ ha hle))
  have hunion : (⋃ n : ℕ, Set.Iic (-((n + 1 : ℕ) : ℝ)⁻¹)) = {z : ℝ | z < 0} := by
    ext z
    simp only [Set.mem_iUnion, Set.mem_Iic, Set.mem_setOf_eq]
    constructor
    · rintro ⟨n, hn⟩
      have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ)⁻¹ := by positivity
      linarith
    · intro hz
      have hnz : (0 : ℝ) < -z := by linarith
      obtain ⟨n, hn⟩ := exists_nat_gt (1 / (-z))
      have h1 : (1 : ℝ) / (-z) < (n : ℝ) := by exact_mod_cast hn
      have hn0 : 0 < n := by
        exact_mod_cast lt_of_le_of_lt (le_of_lt (by positivity : (0 : ℝ) < 1 / (-z))) h1
      have hkey : ((n : ℝ)⁻¹) < -z := by
        have h2 : ((n : ℝ)⁻¹) < ((1 : ℝ) / (-z))⁻¹ :=
          inv_strictAnti₀ (by positivity) h1
        rwa [one_div, inv_inv] at h2
      refine ⟨n - 1, ?_⟩
      have hcast : ((n - 1 + 1 : ℕ) : ℝ) = (n : ℝ) := by
        exact_mod_cast Nat.succ_pred_eq_of_pos hn0
      rw [hcast]
      linarith
  have hzero : ν {z : ℝ | z < 0} = 0 := by
    have h1 := tendsto_measure_iUnion_atTop (μ := ν) hmono
    rw [hunion] at h1
    simp only [Function.comp_def] at h1
    have hval : ∀ n : ℕ, ν (Set.Iic (-((n + 1 : ℕ) : ℝ)⁻¹)) = 0 := fun n =>
      le_antisymm (hcon (((n + 1 : ℕ) : ℝ)⁻¹) (by positivity)) zero_le
    rw [funext hval] at h1
    exact tendsto_nhds_unique h1 tendsto_const_nhds
  -- so the marginal is nonnegative a.e., and centred, hence zero a.e.
  have hae : ∀ᵐ z ∂ν, 0 ≤ z := by
    have hsub : {z : ℝ | ¬ 0 ≤ z} ⊆ {z : ℝ | z < 0} := fun z hz => Std.not_le.mp hz
    have hnull := measure_mono_null hsub hzero
    have h8 : ∀ᵐ z ∂ν, z ∉ {z : ℝ | ¬ 0 ≤ z} :=
      measure_eq_zero_iff_ae_notMem.mp hnull
    exact h8.mono fun z hz => not_not.1 (fun hc => hz hc)
  have hint' : Integrable (fun z : ℝ => z) ν := integrable_id_of_extMean_zero h0
  have hmax : (fun z : ℝ => max z 0) =ᵐ[ν] (fun z : ℝ => z) := by
    filter_upwards [hae] with z hz
    simp only [max_eq_left hz]
  have hint : Integrable (fun z : ℝ => max z 0) ν :=
    (integrable_congr hmax).mpr hint'
  have hinteg : ∫ z, max z 0 ∂ν = 0 := by
    have h6 := integral_congr_ae hmax
    rw [integral_id_zero h0] at h6
    exact h6
  have hae0 : (fun z : ℝ => max z 0) =ᵐ[ν] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun z => le_max_iff.2 (Or.inr le_rfl)) hint).mp hinteg
  have haez : (fun z : ℝ => z) =ᵐ[ν] 0 := hmax.symm.trans hae0
  -- hence the variance is zero: contradiction
  have hvar0 : RWRS.evar ν = 0 := by
    rw [evar_eq_lintegral h0]
    have hae2 : (fun z : ℝ => ENNReal.ofReal (z ^ 2)) =ᵐ[ν] 0 := by
      filter_upwards [haez] with z hz
      rw [hz]
      simp
    have hlint : ∫⁻ z, ENNReal.ofReal (z ^ 2) ∂ν = 0 := by
      rw [lintegral_congr_ae hae2]
      simp
    rw [hlint]
  exact absurd hvar0 (by
    intro h
    rw [h] at hvar
    exact lt_irrefl 0 hvar)

end RWRS.Support
