/-
Step 4 of `lem:moment-sharpness`: the second-moment method over the ball.

The number of good sites is a sum of indicators.  Its mean is the sum of the
probabilities and its second moment the double sum of the probabilities of the
pairwise intersections, which the pairwise bound controls.  The Paley--Zygmund
inequality at `θ = 1/2` bounds the probability that the count is at least half
its mean, and a count is an integer, so half a positive mean already forces it
to be at least one; the count is at least one exactly on the union.
-/
import RWRS.Support.PaleyZygmund
import RWRS.Support.SecondMoment

namespace RWRS.Support

open MeasureTheory

variable {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- The mean of a sum of indicators. -/
theorem integral_indicator_sum (B : Finset ι) (A : ι → Set Ω)
    (hA : ∀ i, MeasurableSet (A i)) :
    ∫ ω, (∑ i ∈ B, (A i).indicator (fun _ => (1 : ℝ)) ω) ∂P
      = ∑ i ∈ B, (P (A i)).toReal := by
  rw [integral_finsetSum B (fun i _ => (integrable_const (1 : ℝ)).indicator (hA i))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_indicator (hA i), setIntegral_const, smul_eq_mul, mul_one]
  rfl

/-- The second moment of a sum of indicators. -/
theorem integral_indicator_sum_sq (B : Finset ι) (A : ι → Set Ω)
    (hA : ∀ i, MeasurableSet (A i)) :
    ∫ ω, (∑ i ∈ B, (A i).indicator (fun _ => (1 : ℝ)) ω) ^ 2 ∂P
      = ∑ i ∈ B, ∑ j ∈ B, (P (A i ∩ A j)).toReal := by
  classical
  have hexp : ∀ ω : Ω, (∑ i ∈ B, (A i).indicator (fun _ => (1 : ℝ)) ω) ^ 2
      = ∑ i ∈ B, ∑ j ∈ B, ((A i ∩ A j).indicator (fun _ => (1 : ℝ)) ω) := by
    intro ω
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    by_cases hi : ω ∈ A i <;> by_cases hj : ω ∈ A j <;>
      simp [hi, hj, Set.mem_inter_iff]
  rw [integral_congr_ae (Filter.Eventually.of_forall hexp)]
  rw [integral_finsetSum B (fun i _ => integrable_finsetSum B (fun j _ =>
    (integrable_const (1 : ℝ)).indicator ((hA i).inter (hA j))))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum B (fun j _ =>
    (integrable_const (1 : ℝ)).indicator ((hA i).inter (hA j)))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_indicator ((hA i).inter (hA j)), setIntegral_const, smul_eq_mul, mul_one]
  rfl

omit [MeasurableSpace Ω] in
/-- A sum of indicators is at most the number of terms. -/
theorem indicator_sum_le_card (B : Finset ι) (A : ι → Set Ω) (ω : Ω) :
    (∑ i ∈ B, (A i).indicator (fun _ => (1 : ℝ)) ω) ≤ (B.card : ℝ) := by
  calc (∑ i ∈ B, (A i).indicator (fun _ => (1 : ℝ)) ω)
      ≤ ∑ _i ∈ B, (1 : ℝ) := by
        refine Finset.sum_le_sum fun i _ => ?_
        by_cases h : ω ∈ A i <;> simp [h]
    _ = (B.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]

open scoped Classical in
omit [MeasurableSpace Ω] in
/-- A sum of indicators counts the members. -/
theorem indicator_sum_eq_card (B : Finset ι) (A : ι → Set Ω) (ω : Ω) :
    (∑ i ∈ B, (A i).indicator (fun _ => (1 : ℝ)) ω)
      = ((B.filter (fun i => ω ∈ A i)).card : ℝ) := by
  classical
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : ω ∈ A i <;> simp [h]

open scoped Classical in
omit [MeasurableSpace Ω] in
/-- The count is at least one exactly on the union. -/
theorem one_le_indicator_sum_iff (B : Finset ι) (A : ι → Set Ω) (ω : Ω) :
    (1 : ℝ) ≤ (∑ i ∈ B, (A i).indicator (fun _ => (1 : ℝ)) ω) ↔ ω ∈ ⋃ i ∈ B, A i := by
  classical
  rw [indicator_sum_eq_card]
  constructor
  · intro h
    have hcard : 0 < (B.filter (fun i => ω ∈ A i)).card := by exact_mod_cast lt_of_lt_of_le zero_lt_one h
    obtain ⟨i, hi⟩ := Finset.card_pos.1 hcard
    rw [Finset.mem_filter] at hi
    exact Set.mem_biUnion hi.1 hi.2
  · intro h
    rw [Set.mem_iUnion₂] at h
    obtain ⟨i, hiB, hi⟩ := h
    have : i ∈ B.filter (fun i => ω ∈ A i) := Finset.mem_filter.2 ⟨hiB, hi⟩
    have hcard : 1 ≤ (B.filter (fun i => ω ∈ A i)).card := Finset.card_pos.2 ⟨i, this⟩
    exact_mod_cast hcard

/-- **Step 4.**  The second-moment bound on the probability that some site of a
finite family is good. -/
theorem meas_biUnion_lower [DecidableEq ι] (B : Finset ι) (A : ι → Set Ω)
    (hA : ∀ i, MeasurableSet (A i)) {p : ℝ} (hp : 0 ≤ p)
    (hlow : ∀ i ∈ B, 3 / 4 * p ≤ (P (A i)).toReal)
    (hup : ∀ i ∈ B, (P (A i)).toReal ≤ p)
    (hpair : ∀ i ∈ B, ∀ j ∈ B, i ≠ j → (P (A i ∩ A j)).toReal ≤ p * p) :
    9 / 128 * min ((B.card : ℝ) * p) 1 ≤ (P (⋃ i ∈ B, A i)).toReal := by
  classical
  set X : Ω → ℝ := fun ω => ∑ i ∈ B, (A i).indicator (fun _ => (1 : ℝ)) ω with hX
  set s : ℝ := (B.card : ℝ) * p with hs
  have hs0 : 0 ≤ s := by positivity
  have hU : MeasurableSet (⋃ i ∈ B, A i) := by
    exact MeasurableSet.biUnion B.countable_toSet fun i _ => hA i
  have hPU : 0 ≤ (P (⋃ i ∈ B, A i)).toReal := ENNReal.toReal_nonneg
  rcases eq_or_lt_of_le hs0 with hzero | hpos
  · rw [← hzero]
    simp
  -- the count and its moments
  have hXnn : ∀ ω, 0 ≤ X ω := fun ω =>
    Finset.sum_nonneg fun i _ => Set.indicator_nonneg (fun _ _ => zero_le_one) ω
  have hXint : ∀ ω, ∃ k : ℕ, X ω = (k : ℝ) := fun ω =>
    ⟨(B.filter (fun i => ω ∈ A i)).card, indicator_sum_eq_card B A ω⟩
  have hXmeas : Measurable X :=
    Finset.measurable_sum _ fun i _ => (measurable_const).indicator (hA i)
  have hXi : Integrable X P :=
    integrable_finsetSum _ fun i _ => (integrable_const (1 : ℝ)).indicator (hA i)
  have hXi2 : Integrable (fun ω => X ω ^ 2) P := by
    refine Integrable.mono' (integrable_const ((B.card : ℝ) ^ 2))
      (hXmeas.pow_const 2).aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
    have hle : X ω ≤ (B.card : ℝ) := indicator_sum_le_card B A ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [hXnn ω]
  have hmean_le : ∫ ω, X ω ∂P ≤ s := by
    rw [hX, integral_indicator_sum B A hA, hs]
    calc ∑ i ∈ B, (P (A i)).toReal ≤ ∑ _i ∈ B, p := Finset.sum_le_sum hup
      _ = (B.card : ℝ) * p := by rw [Finset.sum_const, nsmul_eq_mul]
  have hmean_ge : 3 / 4 * s ≤ ∫ ω, X ω ∂P := by
    rw [hX, integral_indicator_sum B A hA, hs]
    calc 3 / 4 * ((B.card : ℝ) * p) = ∑ _i ∈ B, 3 / 4 * p := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ ∑ i ∈ B, (P (A i)).toReal := Finset.sum_le_sum hlow
  have hsq_le : ∫ ω, X ω ^ 2 ∂P ≤ s + s ^ 2 := by
    rw [hX, integral_indicator_sum_sq B A hA]
    have hrow : ∀ i ∈ B, ∑ j ∈ B, (P (A i ∩ A j)).toReal ≤ p + (B.card : ℝ) * (p * p) := by
      intro i hi
      rw [← Finset.add_sum_erase B _ hi]
      have h1 : (P (A i ∩ A i)).toReal ≤ p := by rw [Set.inter_self]; exact hup i hi
      have h2 : ∑ j ∈ B.erase i, (P (A i ∩ A j)).toReal ≤ (B.card : ℝ) * (p * p) := by
        calc ∑ j ∈ B.erase i, (P (A i ∩ A j)).toReal
            ≤ ∑ _j ∈ B.erase i, (p * p) := Finset.sum_le_sum (fun j hj =>
                hpair i hi j (Finset.mem_of_mem_erase hj) (Ne.symm (Finset.ne_of_mem_erase hj)))
          _ = ((B.erase i).card : ℝ) * (p * p) := by rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (B.card : ℝ) * (p * p) := by
              refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg hp hp)
              exact_mod_cast Finset.card_le_card (Finset.erase_subset i B)
      linarith
    calc ∑ i ∈ B, ∑ j ∈ B, (P (A i ∩ A j)).toReal
        ≤ ∑ _i ∈ B, (p + (B.card : ℝ) * (p * p)) := Finset.sum_le_sum hrow
      _ = (B.card : ℝ) * p + ((B.card : ℝ) * p) ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ = s + s ^ 2 := by rw [hs]
  -- Paley--Zygmund at θ = 1/2
  have hEXpos : 0 < ∫ ω, X ω ∂P := lt_of_lt_of_le (by linarith) hmean_ge
  have hAset : MeasurableSet {ω | (1 / 2 : ℝ) * ∫ ω, X ω ∂P ≤ X ω} :=
    measurableSet_le measurable_const hXmeas
  have hpz := paley_zygmund X hXnn hXi hXi2 (1 / 2) (by norm_num) (by norm_num) hAset
  have hsubset : {ω | (1 / 2 : ℝ) * ∫ ω, X ω ∂P ≤ X ω} ⊆ ⋃ i ∈ B, A i := by
    intro ω hω
    refine (one_le_indicator_sum_iff B A ω).1 ?_
    have hω' : (∫ ω, X ω ∂P) / 2 ≤ X ω := by
      have h := hω
      simp only [Set.mem_setOf_eq] at h
      linarith
    exact subset_one_le_of_pos_mean X hXint hEXpos hω'
  have hmono : (P {ω | (1 / 2 : ℝ) * ∫ ω, X ω ∂P ≤ X ω}).toReal
      ≤ (P (⋃ i ∈ B, A i)).toReal :=
    ENNReal.toReal_mono (measure_ne_top P _) (measure_mono hsubset)
  -- assemble
  set q : ℝ := (P (⋃ i ∈ B, A i)).toReal with hq
  have hkey : 9 / 64 * s ^ 2 ≤ (s + s ^ 2) * q := by
    have h1 : (1 - 1 / 2 : ℝ) ^ 2 * (∫ ω, X ω ∂P) ^ 2 ≤ (∫ ω, X ω ^ 2 ∂P) *
        (P {ω | (1 / 2 : ℝ) * ∫ ω, X ω ∂P ≤ X ω}).toReal := hpz
    have h2 : (1 / 4 : ℝ) * (3 / 4 * s) ^ 2 ≤ (1 - 1 / 2 : ℝ) ^ 2 * (∫ ω, X ω ∂P) ^ 2 := by
      have : (0 : ℝ) ≤ 3 / 4 * s := by linarith
      nlinarith [hmean_ge]
    have h3 : (∫ ω, X ω ^ 2 ∂P) *
        (P {ω | (1 / 2 : ℝ) * ∫ ω, X ω ∂P ≤ X ω}).toReal ≤ (s + s ^ 2) * q := by
      refine mul_le_mul hsq_le hmono ENNReal.toReal_nonneg ?_
      nlinarith
    nlinarith [h1, h2, h3]
  have hden : 0 < 1 + s := by linarith
  have hratio : 9 / 64 * (s / (1 + s)) ≤ q := by
    have hfac : (s + s ^ 2) = s * (1 + s) := by ring
    rw [hfac] at hkey
    have h1 : 9 / 64 * s ≤ (1 + s) * q := by nlinarith
    rw [← mul_div_assoc, div_le_iff₀ hden]
    linarith
  have hmin := div_one_add_ge_half_min hs0
  have h2 := mul_le_mul_of_nonneg_left hmin (by norm_num : (0 : ℝ) ≤ 9 / 64)
  linarith [h2, hratio]

end RWRS.Support
