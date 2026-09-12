/-
Step 2 of `prop:doubly-transient-really-general`: on a doubly transient graph an
infinite annealed value forces an almost surely infinite value.

The paper truncates the value at a level `K`, bounds the variance of the
truncation by `var(ξ)∑_v g(o,v)^2` through Efron--Stein, and derives a
contradiction from Fatou's lemma with a zero-one law.  The same two ingredients
give the conclusion directly and with no appeal to the zero-one law: the
truncations `f_K` have means tending to infinity and a variance bounded uniformly
in `K`, so Chebyshev's inequality puts `f_K` above half its mean with probability
tending to one, and `f_K ≤ u_∞`; hence `u_∞` exceeds every level with
probability one, and the intersection over the integer levels is the event that
it is infinite.
-/
import RWRS.Support.Convexity
import RWRS.Support.EfronStein

namespace RWRS.Support

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite] {ν : Measure ℝ}

/-! ### The value as a monotone limit -/

/-- The value at horizon `n` is the odometer after `n` rounds of the scenery
shifted by one. -/
theorem value_eq_odometer [Infinite V] (hG : G.Connected) (ξ : V → ℝ) (n : ℕ) (x : V) :
    value G ξ n x = odometer G (fun u => ξ u + 1) n x := by
  have h := value_eq hG (fun u => ξ u + 1) n x
  rw [excess_add_one] at h
  exact h

/-- The value at horizon `n` is nondecreasing in `n`. -/
theorem value_mono_horizon [Infinite V] (hG : G.Connected) (ξ : V → ℝ) (x : V) :
    Monotone fun n : ℕ => value G ξ n x := by
  refine monotone_nat_of_le_succ fun n => ?_
  simp only [value_eq_odometer hG]
  exact odometer_mono _ n x

/-- `u_∞(x)` is the supremum of the values at the finite horizons. -/
theorem supStopValue_eq_iSup_value [Infinite V] (hG : G.Connected) (ξ : V → ℝ) (x : V) :
    supStopValue G ξ x = ⨆ n : ℕ, ENNReal.ofReal (value G ξ n x) := by
  rw [supStopValue_eq_odometerLimit hG, RWRS.odometerLimit]
  exact iSup_congr fun n => congrArg ENNReal.ofReal (value_eq_odometer hG ξ n x).symm

/-! ### The Green energy -/

/-- `∑_v g(o,v)^2`, the quantity double transience asks to be finite. -/
noncomputable def greenSq (G : SimpleGraph V) [G.LocallyFinite] (o : V) : ℝ≥0∞ :=
  ∑' v : V, green G o v ^ 2

theorem fluct_le_greenSq [Infinite V] (hG : G.Connected) (n : ℕ) (o : V) :
    fluct G n o ≤ greenSq G o := by
  refine ENNReal.tsum_le_tsum fun v => ?_
  have h1 : ENNReal.ofReal (greenTime G n o v ^ 2)
      = ENNReal.ofReal (greenTime G n o v) ^ 2 := by
    rw [pow_two, pow_two, ENNReal.ofReal_mul (greenTime_nonneg n o v)]
  rw [h1]
  exact pow_le_pow_left' (ofReal_greenTime_le_green hG n o v) 2

/-! ### The value at a finite horizon -/

theorem measurable_supStopValue [Infinite V] (hG : G.Connected) (o : V) :
    Measurable fun ξ : V → ℝ => supStopValue G ξ o := by
  have hfun : (fun ξ : V → ℝ => supStopValue G ξ o)
      = (fun σ : V → ℝ => odometerLimit G σ o) ∘ (fun ξ : V → ℝ => fun u => ξ u + 1) :=
    funext fun ξ => supStopValue_eq_odometerLimit hG ξ o
  rw [hfun]
  exact (measurable_odometerLimit o).comp measurable_shift


theorem ofReal_value_le_supStopValue [Infinite V] (hG : G.Connected) (ξ : V → ℝ) (n : ℕ)
    (x : V) : ENNReal.ofReal (value G ξ n x) ≤ supStopValue G ξ x := by
  rw [supStopValue_eq_iSup_value hG]
  exact le_iSup (fun k : ℕ => ENNReal.ofReal (value G ξ k x)) n

theorem integrable_value [Infinite V] (hG : G.Connected) (hν : IsProbabilityMeasure ν)
    (h0 : extMean ν = 0) (hsq : evar ν < ⊤) (n : ℕ) (o : V) :
    Integrable (fun ξ : V → ℝ => value G ξ n o) (iidLaw V ν) := by
  haveI : Countable V := countable_of_connected hG
  exact (memLp_value (efronStein V) hG hν h0 hsq n o).integrable one_le_two

theorem lintegral_ofReal_value [Infinite V] (hG : G.Connected) (hν : IsProbabilityMeasure ν)
    (h0 : extMean ν = 0) (hsq : evar ν < ⊤) (n : ℕ) (o : V) :
    (∫⁻ ξ, ENNReal.ofReal (value G ξ n o) ∂(iidLaw V ν))
      = ENNReal.ofReal (∫ ξ, value G ξ n o ∂(iidLaw V ν)) :=
  (MeasureTheory.ofReal_integral_eq_lintegral_ofReal (integrable_value hG hν h0 hsq n o)
    (Filter.Eventually.of_forall fun ξ => value_nonneg hG ξ n o)).symm

/-- The annealed values at the finite horizons increase to the annealed value. -/
theorem iSup_lintegral_ofReal_value [Infinite V] (hG : G.Connected) (o : V) :
    (⨆ n : ℕ, ∫⁻ ξ, ENNReal.ofReal (value G ξ n o) ∂(iidLaw V ν))
      = ∫⁻ ξ, supStopValue G ξ o ∂(iidLaw V ν) := by
  have hmeas : ∀ n : ℕ, Measurable fun ξ : V → ℝ => ENNReal.ofReal (value G ξ n o) :=
    fun n => (measurable_value hG n o).ennreal_ofReal
  have hmono : Monotone fun (n : ℕ) (ξ : V → ℝ) => ENNReal.ofReal (value G ξ n o) :=
    fun a b hab ξ => ENNReal.ofReal_le_ofReal (value_mono_horizon hG ξ o hab)
  rw [← MeasureTheory.lintegral_iSup hmeas hmono]
  exact lintegral_congr fun ξ => (supStopValue_eq_iSup_value hG ξ o).symm

/-- **An infinite annealed value forces the finite-horizon means to diverge.** -/
theorem tendsto_integral_value_atTop [Infinite V] (hG : G.Connected)
    (hν : IsProbabilityMeasure ν) (h0 : extMean ν = 0) (hsq : evar ν < ⊤) (o : V)
    (hann : (∫⁻ ξ, supStopValue G ξ o ∂(iidLaw V ν)) = ⊤) :
    Tendsto (fun n : ℕ => ∫ ξ, value G ξ n o ∂(iidLaw V ν)) atTop atTop := by
  have hmono : Monotone fun n : ℕ =>
      ∫⁻ ξ, ENNReal.ofReal (value G ξ n o) ∂(iidLaw V ν) :=
    fun a b hab => lintegral_mono fun ξ => ENNReal.ofReal_le_ofReal (value_mono_horizon hG ξ o hab)
  have hsup : (⨆ n : ℕ, ∫⁻ ξ, ENNReal.ofReal (value G ξ n o) ∂(iidLaw V ν)) = ⊤ := by
    rw [iSup_lintegral_ofReal_value hG o]; exact hann
  have htop : Tendsto
      (fun n : ℕ => ∫⁻ ξ, ENNReal.ofReal (value G ξ n o) ∂(iidLaw V ν)) atTop (nhds ⊤) := by
    rw [← hsup]; exact tendsto_atTop_iSup hmono
  refine tendsto_atTop.2 fun C => ?_
  have hC : (0 : ℝ) ≤ max C 0 := le_max_right _ _
  filter_upwards [ENNReal.tendsto_nhds_top_iff_nnreal.1 htop (Real.toNNReal (max C 0))] with n hn
  have hn' : ENNReal.ofReal (max C 0)
      < ENNReal.ofReal (∫ ξ, value G ξ n o ∂(iidLaw V ν)) := by
    rw [← lintegral_ofReal_value hG hν h0 hsq n o]; exact hn
  exact ((le_max_left C 0).trans ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hC).1 hn').le)

/-! ### The variance bound of Step 2 -/

/-- **The variance of the value at any horizon is bounded by the Green energy.**
Efron--Stein against the one-site sensitivity gives `var(ξ)Σ_n(o)`, and the
finite-horizon Green weights are below the full ones. -/
theorem variance_value_le_greenSq [Infinite V] (hG : G.Connected)
    (hν : IsProbabilityMeasure ν) (h0 : extMean ν = 0) (hsq : evar ν < ⊤)
    (o : V) (hgs : greenSq G o ≠ ⊤) (n : ℕ) :
    variance (fun ξ : V → ℝ => value G ξ n o) (iidLaw V ν)
      ≤ (evar ν * greenSq G o).toReal := by
  haveI : Countable V := countable_of_connected hG
  have h := evariance_value_le (efronStein V) hG hν h0 hsq n o
  rw [ProbabilityTheory.variance]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top hsq.ne hgs)
    (h.trans (mul_le_mul' le_rfl (fluct_le_greenSq hG n o)))

/-! ### Chebyshev at the finite horizons -/

/-- **The value exceeds every level almost surely.**  The mean of the value at
horizon `n` diverges while its variance stays below the Green energy, so
Chebyshev's inequality puts the value above any fixed level with probability
arbitrarily close to one, and the level set has full measure. -/
theorem measure_ge_level_eq_one [Infinite V] (hG : G.Connected)
    (hν : IsProbabilityMeasure ν) (h0 : extMean ν = 0) (hsq : evar ν < ⊤) (o : V)
    (hgs : greenSq G o ≠ ⊤)
    (hann : (∫⁻ ξ, supStopValue G ξ o ∂(iidLaw V ν)) = ⊤) (T : ℝ) :
    iidLaw V ν {ξ : V → ℝ | ENNReal.ofReal T ≤ supStopValue G ξ o} = 1 := by
  haveI := hν
  haveI : Countable V := countable_of_connected hG
  set μ : Measure (V → ℝ) := iidLaw V ν with hμ
  set m : ℕ → ℝ := fun n => ∫ ξ, value G ξ n o ∂μ with hm
  set V₀ : ℝ := (evar ν * greenSq G o).toReal with hV0
  have hV0nn : 0 ≤ V₀ := ENNReal.toReal_nonneg
  have hmtop : Tendsto m atTop atTop := tendsto_integral_value_atTop hG hν h0 hsq o hann
  set A : Set (V → ℝ) := {ξ : V → ℝ | ENNReal.ofReal T ≤ supStopValue G ξ o} with hA
  have hAm : MeasurableSet A :=
    measurableSet_le measurable_const (measurable_supStopValue hG o)
  have hcompl : ∀ n : ℕ, 0 < m n → 2 * T ≤ m n →
      μ Aᶜ ≤ ENNReal.ofReal (V₀ / (m n / 2) ^ 2) := by
    intro n hpos hT
    have hsub : Aᶜ ⊆ {ξ : V → ℝ | m n / 2 ≤ |value G ξ n o - m n|} := by
      intro ξ hξ
      simp only [hA, Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hξ
      have h1 : ENNReal.ofReal (value G ξ n o) < ENNReal.ofReal T :=
        lt_of_le_of_lt (ofReal_value_le_supStopValue hG ξ n o) hξ
      have h2 : value G ξ n o < T := by
        rcases lt_or_ge (value G ξ n o) T with h | h
        · exact h
        · exact absurd (ENNReal.ofReal_le_ofReal h) (not_le.2 h1)
      simp only [Set.mem_setOf_eq]
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
      linarith
    refine (measure_mono hsub).trans ?_
    have hmemLp : MemLp (fun ξ : V → ℝ => value G ξ n o) 2 μ :=
      memLp_value (efronStein V) hG hν h0 hsq n o
    have hcheb := ProbabilityTheory.meas_ge_le_variance_div_sq (μ := μ) hmemLp
      (c := m n / 2) (by linarith)
    refine hcheb.trans (ENNReal.ofReal_le_ofReal ?_)
    have hvar := variance_value_le_greenSq hG hν h0 hsq o hgs n
    have hsqpos : (0 : ℝ) < (m n / 2) ^ 2 := by positivity
    exact div_le_div_of_nonneg_right hvar hsqpos.le
  have hzero : μ Aᶜ = 0 := by
    have hdiv : Tendsto (fun n : ℕ => V₀ / (m n / 2) ^ 2) atTop (nhds 0) := by
      have h1 : Tendsto (fun n : ℕ => m n / 2) atTop atTop :=
        hmtop.atTop_div_const two_pos
      have h2 : Tendsto (fun n : ℕ => (m n / 2) ^ 2) atTop atTop := by
        simpa [pow_two] using h1.atTop_mul_atTop₀ h1
      exact h2.const_div_atTop V₀
    have htend : Tendsto (fun n : ℕ => ENNReal.ofReal (V₀ / (m n / 2) ^ 2)) atTop (nhds 0) := by
      have h3 := (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp hdiv
      rw [Function.comp_def] at h3
      simpa using h3
    refine le_antisymm (ge_of_tendsto htend ?_) (by simp)
    filter_upwards [hmtop.eventually_ge_atTop (max (2 * T) 1)] with n hn
    exact hcompl n (lt_of_lt_of_le zero_lt_one (le_trans (le_max_right _ _) hn))
      (le_trans (le_max_left _ _) hn)
  rwa [← prob_compl_eq_zero_iff hAm]

/-- **Step 2 of `prop:doubly-transient-really-general`.** -/
theorem ae_supStopValue_top_of_lintegral_top [Infinite V] (hG : G.Connected)
    (hν : IsProbabilityMeasure ν) (h0 : extMean ν = 0) (hsq : evar ν < ⊤) (o : V)
    (hgs : greenSq G o ≠ ⊤)
    (hann : (∫⁻ ξ, supStopValue G ξ o ∂(iidLaw V ν)) = ⊤) :
    ∀ᵐ ξ ∂(iidLaw V ν), supStopValue G ξ o = ⊤ := by
  haveI := hν
  set μ : Measure (V → ℝ) := iidLaw V ν with hμ
  have hAm : ∀ k : ℕ, MeasurableSet {ξ : V → ℝ | ENNReal.ofReal (k : ℝ) ≤ supStopValue G ξ o} :=
    fun k => measurableSet_le measurable_const (measurable_supStopValue hG o)
  have hnull : ∀ k : ℕ,
      μ {ξ : V → ℝ | ENNReal.ofReal (k : ℝ) ≤ supStopValue G ξ o}ᶜ = 0 := by
    intro k
    rw [prob_compl_eq_zero_iff (hAm k)]
    exact measure_ge_level_eq_one hG hν h0 hsq o hgs hann (k : ℝ)
  rw [ae_iff]
  refine measure_mono_null ?_ (measure_iUnion_null hnull)
  intro ξ hξ
  simp only [Set.mem_setOf_eq] at hξ
  obtain ⟨k, hk⟩ := ENNReal.exists_nat_gt hξ
  refine Set.mem_iUnion.2 ⟨k, ?_⟩
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le]
  rwa [ENNReal.ofReal_natCast]

end RWRS.Support
