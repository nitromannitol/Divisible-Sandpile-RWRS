/-
The positive-part mean bound of `lem:positive-part`, for an index type and a
sample space in arbitrary universes.

The frozen statement of the paper's lemma quantifies over `Type`; the same
proof works verbatim for `Type*`, and the applications of the lemma inside this
development take the index to be the set of vertices carrying positive Green
weight, which lives in the universe of the ambient vertex type.
-/
import RWRS.Setting
import RWRS.Support.PaleyZygmund
import LatticeProb.Prob.Moments
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Moments.Variance

open MeasureTheory ProbabilityTheory

/-- The universal constant of `lem:positive-part`. -/
noncomputable def RWRS.Support.cStar : ℝ := 1 / (32 * Real.sqrt 2)

theorem RWRS.Support.cStar_pos : 0 < RWRS.Support.cStar := by
  rw [RWRS.Support.cStar]; positivity

/-- **The positive-part mean bound**, in arbitrary universes.  A finite family
of independent centred variables, each bounded by a deterministic `b i` whose
square does not exceed the total variance `B ^ 2`, has
`E[(∑ Z_i)^+] ≥ c B` for the universal constant `c`. -/
theorem RWRS.Support.positivePart_bound {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) (hP : IsProbabilityMeasure P) (Z : ι → Ω → ℝ) (b : ι → ℝ)
    (_hb : ∀ i, 0 < b i) (hindep : ProbabilityTheory.iIndepFun Z P)
    (hint : ∀ i, Integrable (Z i) P) (hmean : ∀ i, ∫ ω, Z i ω ∂P = 0)
    (hbound : ∀ i, ∀ᵐ ω ∂P, |Z i ω| ≤ b i)
    (B : ℝ) (hB0 : 0 ≤ B) (hBsq : B ^ 2 = ∑ i, ProbabilityTheory.variance (Z i) P)
    (hbB : ∀ i, b i ^ 2 ≤ B ^ 2) :
    RWRS.Support.cStar * B ≤ ∫ ω, max (∑ i, Z i ω) 0 ∂P := by
  classical
  rw [RWRS.Support.cStar]
  haveI : IsProbabilityMeasure P := hP
  -- A measurable modification of the family; nothing in the hypotheses changes.
  set W : ι → Ω → ℝ := fun i => (hint i).1.mk (Z i) with hWdef
  have hWm : ∀ i, Measurable (W i) := fun i => (hint i).1.stronglyMeasurable_mk.measurable
  have hae : ∀ i, Z i =ᵐ[P] W i := fun i => (hint i).1.ae_eq_mk
  have hWindep : iIndepFun W P := hindep.congr hae
  have hWmean : ∀ i, ∫ ω, W i ω ∂P = 0 := by
    intro i; rw [← integral_congr_ae (hae i)]; exact hmean i
  have hWbd : ∀ i, ∀ᵐ ω ∂P, |W i ω| ≤ b i := by
    intro i; filter_upwards [hbound i, hae i] with ω h1 h2; rwa [← h2]
  -- Moments of the summands.
  have h4 : ∀ i, Integrable (fun ω => W i ω ^ 4) P := by
    intro i
    refine Integrable.mono' (integrable_const (b i ^ 4))
      ((hWm i).pow_const 4).aestronglyMeasurable ?_
    filter_upwards [hWbd i] with ω h
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) h 4
  have h2int : ∀ i, Integrable (fun ω => W i ω ^ 2) P := fun i =>
    LatticeProb.integrable_pow_of_integrable_pow_four (hWm i).aestronglyMeasurable (h4 i)
      (by norm_num)
  have h2nonneg : ∀ i, 0 ≤ ∫ ω, W i ω ^ 2 ∂P := fun i =>
    integral_nonneg fun ω => by positivity
  have hvar : ∀ i, variance (Z i) P = ∫ ω, W i ω ^ 2 ∂P := by
    intro i
    rw [variance_congr (hae i), variance_of_integral_eq_zero (hWm i).aemeasurable (hWmean i)]
  have hB2 : ∑ i, ∫ ω, W i ω ^ 2 ∂P = B ^ 2 := by
    rw [hBsq]; exact Finset.sum_congr rfl fun i _ => (hvar i).symm
  have h4le : ∀ i, ∫ ω, W i ω ^ 4 ∂P ≤ b i ^ 2 * ∫ ω, W i ω ^ 2 ∂P := by
    intro i
    rw [← integral_const_mul]
    refine integral_mono_ae (h4 i) ((h2int i).const_mul _) ?_
    filter_upwards [hWbd i] with ω h
    have h1 : W i ω ^ 2 ≤ b i ^ 2 := by
      have := abs_nonneg (W i ω)
      nlinarith [sq_abs (W i ω)]
    nlinarith [sq_nonneg (W i ω)]
  -- The fourth moment of the sum.
  have hsum4 : ∫ ω, (∑ i, W i ω) ^ 4 ∂P ≤ 4 * B ^ 4 := by
    have hlib := LatticeProb.integral_pow_four_finsetSum_le W hWm hWindep h4 hWmean Finset.univ
    have hfour : ∑ i, ∫ ω, W i ω ^ 4 ∂P ≤ B ^ 2 * ∑ i, ∫ ω, W i ω ^ 2 ∂P := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => le_trans (h4le i) ?_
      exact mul_le_mul_of_nonneg_right (hbB i) (h2nonneg i)
    rw [hB2] at hfour
    rw [hB2] at hlib
    nlinarith [hlib, hfour]
  have hsum2 : ∫ ω, (∑ i, W i ω) ^ 2 ∂P = B ^ 2 := by
    rw [LatticeProb.integral_sq_finsetSum W hWm hWindep h4 hWmean Finset.univ, hB2]
  -- The sum itself, and the integrability of its powers.
  set S : Ω → ℝ := fun ω => ∑ i, W i ω with hSdef
  have hSm : Measurable S := by
    refine Finset.measurable_sum Finset.univ ?_
    intro i _; exact hWm i
  have hS4 : Integrable (fun ω => S ω ^ 4) P :=
    LatticeProb.integrable_sum_pow_four W (fun i => (hWm i).aestronglyMeasurable) h4 Finset.univ
  have hS2 : Integrable (fun ω => S ω ^ 2) P :=
    LatticeProb.integrable_pow_of_integrable_pow_four hSm.aestronglyMeasurable hS4 (by norm_num)
  have hS1 : Integrable S P :=
    LatticeProb.integrable_sum_apply W hWm h4 Finset.univ
  have hS1mean : ∫ ω, S ω ∂P = 0 :=
    LatticeProb.integral_sum_apply_eq_zero W hWm h4 hWmean Finset.univ
  -- The goal only sees `Z`; replace it by `W`.
  have hgoal : ∫ ω, max (∑ i, Z i ω) 0 ∂P = ∫ ω, max (S ω) 0 ∂P := by
    refine integral_congr_ae ?_
    have : ∀ᵐ ω ∂P, ∀ i, Z i ω = W i ω := (ae_all_iff).2 hae
    filter_upwards [this] with ω h
    simp only [hSdef]
    exact congrArg (fun t => max t 0) (Finset.sum_congr rfl fun i _ => h i)
  rw [hgoal]
  rcases eq_or_lt_of_le hB0 with hB | hBpos
  · rw [← hB, mul_zero]
    exact integral_nonneg fun ω => le_max_right _ _
  -- Paley--Zygmund applied to `S^2` at `θ = 1/2`.
  set Y : Ω → ℝ := fun ω => S ω ^ 2 with hYdef
  have hYnn : ∀ ω, 0 ≤ Y ω := fun ω => by positivity
  have hYint : ∫ ω, Y ω ∂P = B ^ 2 := hsum2
  have hY2 : Integrable (fun ω => Y ω ^ 2) P := by
    have : (fun ω => Y ω ^ 2) = fun ω => S ω ^ 4 := by funext ω; simp only [hYdef]; ring
    rw [this]; exact hS4
  have hYm : Measurable Y := hSm.pow_const 2
  have hA : MeasurableSet {ω | (1 / 2 : ℝ) * ∫ ω, Y ω ∂P ≤ Y ω} :=
    measurableSet_le measurable_const hYm
  have hPZ := RWRS.Support.paley_zygmund Y hYnn hS2 hY2 (1 / 2) (by norm_num) (by norm_num) hA
  rw [hYint] at hPZ
  have hY2eq : ∫ ω, Y ω ^ 2 ∂P = ∫ ω, S ω ^ 4 ∂P := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only [hYdef]; ring
  rw [hY2eq] at hPZ
  set p : ℝ := (P {ω | (1 / 2 : ℝ) * B ^ 2 ≤ Y ω}).toReal with hpdef
  have hp0 : (0 : ℝ) ≤ p := ENNReal.toReal_nonneg
  have hp : (1 : ℝ) / 16 ≤ p := by
    have hB4 : (0 : ℝ) < B ^ 4 := by positivity
    have hmul : (∫ ω, S ω ^ 4 ∂P) * p ≤ 4 * B ^ 4 * p :=
      mul_le_mul_of_nonneg_right hsum4 hp0
    nlinarith [hPZ, hmul, hB4]
  -- Pass from `S^2` to `|S|`.
  have hsub : {ω | (1 / 2 : ℝ) * B ^ 2 ≤ Y ω} ⊆ {ω | B / Real.sqrt 2 ≤ |S ω|} := by
    intro ω hω
    simp only [Set.mem_setOf_eq, hYdef] at hω ⊢
    have h2 : (0 : ℝ) < Real.sqrt 2 := by positivity
    have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have ht : (B / Real.sqrt 2) ^ 2 = 1 / 2 * B ^ 2 := by
      field_simp [hsq]
      nlinarith [hsq]
    have hu : |S ω| ^ 2 = S ω ^ 2 := sq_abs _
    nlinarith [abs_nonneg (S ω), le_of_lt (div_pos hBpos h2), ht, hu, hω]
  have hmono : p ≤ (P {ω | B / Real.sqrt 2 ≤ |S ω|}).toReal := by
    refine ENNReal.toReal_mono (measure_ne_top P _) (measure_mono hsub)
  -- Markov's inequality for `|S|`.
  have hMark := mul_meas_ge_le_integral_of_nonneg (μ := P) (f := fun ω => |S ω|)
    (Filter.Eventually.of_forall fun ω => abs_nonneg _) hS1.abs (B / Real.sqrt 2)
  rw [measureReal_def] at hMark
  -- The positive part is half of the absolute value.
  have hpos : ∫ ω, max (S ω) 0 ∂P = (∫ ω, |S ω| ∂P) / 2 := by
    have hrw : (fun ω => max (S ω) 0) = fun ω => (|S ω| + S ω) / 2 := by
      funext ω
      rcases le_total 0 (S ω) with h | h
      · rw [max_eq_left h, abs_of_nonneg h]; ring
      · rw [max_eq_right h, abs_of_nonpos h]; ring
    rw [hrw, integral_div, integral_add hS1.abs hS1, hS1mean, add_zero]
  rw [hpos]
  have hs2pos : (0 : ℝ) < Real.sqrt 2 := by positivity
  have hkey : B / Real.sqrt 2 * (1 / 16) ≤ ∫ ω, |S ω| ∂P := by
    refine le_trans ?_ hMark
    refine mul_le_mul_of_nonneg_left (le_trans hp hmono) (le_of_lt (div_pos hBpos hs2pos))
  have hhalf : B / Real.sqrt 2 * (1 / 16) / 2 ≤ (∫ ω, |S ω| ∂P) / 2 := by linarith
  refine le_trans (le_of_eq ?_) hhalf
  field_simp
  ring


theorem RWRS.Support.exists_positivePart :
    ∃ cstar : ℝ, 0 < cstar ∧
      ∀ {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] (P : Measure Ω),
        IsProbabilityMeasure P → ∀ (Z : ι → Ω → ℝ) (b : ι → ℝ),
        (∀ i, 0 < b i) → ProbabilityTheory.iIndepFun Z P →
        (∀ i, Integrable (Z i) P) → (∀ i, ∫ ω, Z i ω ∂P = 0) →
        (∀ i, ∀ᵐ ω ∂P, |Z i ω| ≤ b i) →
        ∀ B : ℝ, 0 ≤ B → B ^ 2 = ∑ i, ProbabilityTheory.variance (Z i) P →
        (∀ i, b i ^ 2 ≤ B ^ 2) →
        cstar * B ≤ ∫ ω, max (∑ i, Z i ω) 0 ∂P :=
  ⟨RWRS.Support.cStar, RWRS.Support.cStar_pos, fun P hP Z b hb hindep hint hmean hbound B hB0
    hBsq hbB => RWRS.Support.positivePart_bound P hP Z b hb hindep hint hmean hbound B hB0
      hBsq hbB⟩
