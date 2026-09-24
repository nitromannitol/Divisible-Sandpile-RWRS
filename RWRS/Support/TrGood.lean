/-
`lem:tr-good`: almost surely, all but finitely many levels of the tree of pipes
carry a good pipe.

At level `n` there are `B^n` pipes, each with at least `L_n/4` sites in its first
half, so at least `B^n L_n / 4` sites in all; each carries a Pareto variable of
index `q` and is good when it reaches `K L_n`.  The expected number of good sites
is therefore at least `K^{-q} B^n L_n^{1-q}/4`, and since `α(q-1) < 1` and
`L_n ≤ B^{αn}` this is at least a constant times `(B^{1-α(q-1)})^n`, which grows
geometrically.  The probability that no site is good is at most the exponential
of minus that quantity, which is summable, so the first Borel-Cantelli lemma
applies.
-/
import RWRS.Support.Spike
import RWRS.Support.CombArith
import RWRS.Support.RayGadget

namespace RWRS.Support

open MeasureTheory Filter
open scoped ENNReal

variable {B : ℕ} {α : ℝ}

/-! ### The sites in the first half of the level-`n` pipes -/

theorem mem_wordsEq {k : ℕ} {w : List (Fin B)} (h : w.length = k) : w ∈ wordsEq B k := by
  subst h
  exact Finset.mem_image.2 ⟨fun i => w[i], Finset.mem_univ _, by simp⟩

open scoped Classical in
/-- The sites in the first half of some level-`n` pipe. -/
noncomputable def firstHalfFinset (B : ℕ) (L : ℕ → ℕ) (n : ℕ) : Finset (List (Fin B) × ℕ) :=
  (wordsEq B n) ×ˢ Finset.Icc 1 (L n / 2)

open scoped Classical in
theorem mem_firstHalfFinset {L : ℕ → ℕ} {n : ℕ} {v : List (Fin B) × ℕ}
    (hw : v.1.length = n) (h1 : 1 ≤ v.2) (h2 : 2 * v.2 ≤ L n) :
    v ∈ firstHalfFinset B L n :=
  Finset.mem_product.2 ⟨mem_wordsEq hw, Finset.mem_Icc.2 ⟨h1, by omega⟩⟩

open scoped Classical in
theorem firstHalf_of_mem {L : ℕ → ℕ} {n : ℕ} {v : List (Fin B) × ℕ}
    (hv : v ∈ firstHalfFinset B L n) :
    v.1.length = n ∧ 1 ≤ v.2 ∧ 2 * v.2 ≤ L n := by
  rw [firstHalfFinset, Finset.mem_product] at hv
  obtain ⟨hw, hi⟩ := hv
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hi
  exact ⟨length_of_mem_wordsEq hw, h1, by omega⟩

open scoped Classical in
theorem card_firstHalfFinset (L : ℕ → ℕ) (n : ℕ) :
    (firstHalfFinset B L n).card = B ^ n * (L n / 2) := by
  rw [firstHalfFinset, Finset.card_product, card_wordsEq, Nat.card_Icc]
  simp

open scoped Classical in
theorem card_firstHalfFinset_pos (hc : CombCond B α) {n : ℕ} (hn : 1 ≤ n) :
    0 < (firstHalfFinset B (combLen B α) n).card := by
  rw [card_firstHalfFinset]
  have h4 : 4 ≤ combLen B α n := four_le_combLen hc hn
  have hB2 : 2 ≤ B := hc.1
  have hB : 0 < B ^ n := pow_pos (by omega : 0 < B) n
  have : 0 < combLen B α n / 2 := by omega
  exact Nat.mul_pos hB this

open scoped Classical in
theorem card_firstHalfFinset_ge (hc : CombCond B α) {n : ℕ} (hn : 1 ≤ n) :
    (B : ℝ) ^ n * (combLen B α n : ℝ) / 4
      ≤ ((firstHalfFinset B (combLen B α) n).card : ℝ) := by
  have h4 : 4 ≤ combLen B α n := four_le_combLen hc hn
  have hdiv : combLen B α n ≤ 4 * (combLen B α n / 2) := by omega
  have hdivR : (combLen B α n : ℝ) ≤ 4 * ((combLen B α n / 2 : ℕ) : ℝ) := by
    exact_mod_cast hdiv
  have hBpos : (0 : ℝ) < (B : ℝ) ^ n := by
    have := cast_B_pos hc; positivity
  rw [card_firstHalfFinset]
  push_cast
  nlinarith

/-! ### The mean number of good sites grows geometrically -/

theorem base_geom_eq (hc : CombCond B α) (q : ℝ) (n : ℕ) :
    (B : ℝ) ^ n * (((B : ℝ) ^ α) ^ n) ^ (1 - q)
      = ((B : ℝ) ^ (1 - α * (q - 1))) ^ n := by
  have hBpos := cast_B_pos hc
  rw [base_pow hc n, ← Real.rpow_natCast ((B : ℝ)) n,
    ← Real.rpow_mul hBpos.le, ← Real.rpow_natCast ((B : ℝ) ^ (1 - α * (q - 1))) n,
    ← Real.rpow_mul hBpos.le, ← Real.rpow_add hBpos]
  congr 1
  ring

theorem one_lt_base_geom (hc : CombCond B α) {q : ℝ} (hq : 1 < q) (hα : α < 1 / (q - 1)) :
    1 < (B : ℝ) ^ (1 - α * (q - 1)) := by
  have hBpos := cast_B_pos hc
  have hB1 : (1 : ℝ) < (B : ℝ) := by have := cast_B_ge hc; linarith
  have hq1 : (0 : ℝ) < q - 1 := by linarith
  have hlt : α * (q - 1) < 1 := by
    rw [lt_div_iff₀ hq1] at hα
    linarith
  exact Real.one_lt_rpow_iff_of_pos hBpos |>.2 (Or.inl ⟨hB1, by linarith⟩)

open scoped Classical in
/-- **The mean number of good sites at level `n` grows geometrically.** -/
theorem mean_good_ge (hc : CombCond B α) {q K : ℝ} (hq : 1 < q) (hK : 0 < K)
    {n : ℕ} (hn : 1 ≤ n) :
    K ^ (-q) / 4 * ((B : ℝ) ^ (1 - α * (q - 1))) ^ n
      ≤ ((firstHalfFinset B (combLen B α) n).card : ℝ)
          * (K * (combLen B α n : ℝ)) ^ (-q) := by
  have hLpos : (0 : ℝ) < (combLen B α n : ℝ) := by
    exact_mod_cast combLen_pos' hc n
  have hbpos := base_pos hc
  have hBpos := cast_B_pos hc
  have hBn : (0 : ℝ) < (B : ℝ) ^ n := by positivity
  have hsplit : (K * (combLen B α n : ℝ)) ^ (-q)
      = K ^ (-q) * (combLen B α n : ℝ) ^ (-q) := Real.mul_rpow hK.le hLpos.le
  have hKpow : (0 : ℝ) < K ^ (-q) := Real.rpow_pos_of_pos hK _
  have hLpow : (0 : ℝ) < (combLen B α n : ℝ) ^ (-q) := Real.rpow_pos_of_pos hLpos _
  -- the key comparison of powers
  have hLle : (combLen B α n : ℝ) ≤ ((B : ℝ) ^ α) ^ n := combLen_le hc n
  have hXpos : (0 : ℝ) < ((B : ℝ) ^ α) ^ n := by positivity
  have hcmp : (((B : ℝ) ^ α) ^ n) ^ (1 - q) ≤ (combLen B α n : ℝ) ^ (1 - q) :=
    Real.rpow_le_rpow_of_nonpos hLpos hLle (by linarith)
  have hid : (combLen B α n : ℝ) * (combLen B α n : ℝ) ^ (-q)
      = (combLen B α n : ℝ) ^ (1 - q) := by
    rw [show (1 : ℝ) - q = 1 + -q by ring, Real.rpow_add hLpos, Real.rpow_one]
  have hgeom := base_geom_eq hc q n
  have hstep : ((B : ℝ) ^ (1 - α * (q - 1))) ^ n
      ≤ (B : ℝ) ^ n * ((combLen B α n : ℝ) * (combLen B α n : ℝ) ^ (-q)) := by
    rw [hid, ← hgeom]
    exact mul_le_mul_of_nonneg_left hcmp hBn.le
  have hcard := card_firstHalfFinset_ge hc hn
  have hmul : ((B : ℝ) ^ n * (combLen B α n : ℝ) / 4) * (K ^ (-q) * (combLen B α n : ℝ) ^ (-q))
      ≤ ((firstHalfFinset B (combLen B α) n).card : ℝ)
          * (K ^ (-q) * (combLen B α n : ℝ) ^ (-q)) :=
    mul_le_mul_of_nonneg_right hcard (by positivity)
  rw [hsplit]
  nlinarith [hstep, hmul, hKpow]

/-! ### The probability that no site of a finite set is good -/

theorem measure_all_lt_le {V : Type*} (ν : Measure ℝ) [IsProbabilityMeasure ν] {q : ℝ}
    (hq : 0 < q) (hpar : IsPareto ν q) (S : Finset V) (hS : 0 < S.card) {c θ : ℝ}
    (hθ : θ ≤ (S.card : ℝ) * c ^ (-q)) :
    iidLaw V ν {Y : V → ℝ | ∀ v ∈ S, Y v < c} ≤ ENNReal.ofReal (Real.exp (-θ)) := by
  classical
  haveI : IsProbabilityMeasure (iidLaw V ν) := by rw [iidLaw]; infer_instance
  rw [measure_forall_lt]
  rcases le_or_gt 1 c with hc1 | hc1
  · have hcpos : (0 : ℝ) < c := by linarith
    have hp0 : (0 : ℝ) < c ^ (-q) := Real.rpow_pos_of_pos hcpos _
    have hp1 : c ^ (-q) ≤ 1 := by
      rw [Real.rpow_neg hcpos.le, inv_le_one_iff₀]
      exact Or.inr (Real.one_le_rpow hc1 hq.le)
    rw [pareto_Iio ν hq hpar hc1, ← ENNReal.ofReal_pow (by linarith)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 := one_sub_pow_le_exp hp1 S.card
    have h2 : Real.exp (-((S.card : ℝ) * c ^ (-q))) ≤ Real.exp (-θ) :=
      Real.exp_le_exp.2 (by linarith)
    linarith
  · have hzero : ν (Set.Iio c) = 0 := by
      have h1 : ν (Set.Iio (1 : ℝ)) = 0 := by
        have hIci : ν (Set.Ici (1 : ℝ)) = ENNReal.ofReal ((1 : ℝ) ^ (-q)) := hpar 1 le_rfl
        rw [Real.one_rpow] at hIci
        have hcompl : Set.Iio (1 : ℝ) = (Set.Ici (1 : ℝ))ᶜ := by ext z; simp
        rw [hcompl, prob_compl_eq_one_sub measurableSet_Ici, hIci]
        simp
      exact le_antisymm (le_trans (measure_mono (Set.Iio_subset_Iio hc1.le)) h1.le) bot_le
    rw [hzero, zero_pow (by omega : S.card ≠ 0)]
    exact bot_le

/-! ### Summability -/

theorem summable_exp_neg_geom {c r : ℝ} (hc : 0 < c) (hr : 1 < r) :
    Summable (fun n : ℕ => Real.exp (-(c * r ^ n))) := by
  have hratio : Real.exp (-(c * (r - 1))) < 1 := by
    refine Real.exp_lt_one_iff.2 ?_
    have : 0 < c * (r - 1) := by nlinarith
    linarith
  have hgeo : Summable (fun n : ℕ => Real.exp (-c) * Real.exp (-(c * (r - 1))) ^ n) :=
    (summable_geometric_of_lt_one (le_of_lt (Real.exp_pos _)) hratio).mul_left _
  refine Summable.of_nonneg_of_le (fun n => (Real.exp_pos _).le) (fun n => ?_) hgeo
  have hbern : 1 + (n : ℝ) * (r - 1) ≤ r ^ n := by
    have := one_add_mul_le_pow (a := r - 1) (by linarith) n
    simpa using this
  have hmul : c * (1 + (n : ℝ) * (r - 1)) ≤ c * r ^ n :=
    mul_le_mul_of_nonneg_left hbern hc.le
  calc Real.exp (-(c * r ^ n)) ≤ Real.exp (-(c * (1 + (n : ℝ) * (r - 1)))) :=
        Real.exp_le_exp.2 (by linarith)
    _ = Real.exp (-c) * Real.exp (-(c * (r - 1))) ^ n := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
        ring

end RWRS.Support
