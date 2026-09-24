/-
`prop:comb-estimates` for the pipe lengths `L_j = ⌊B^{αj}⌋` of
`ssec:comb-estimates`.

The abstract estimates are instantiated at those lengths: `2 ≤ L_j` for `j ≥ 1`
and `L_{j+1} ≤ (B-1)L_j` come from `B^α ≥ 4` and `2B^α ≤ B-1`, and the level
terms `I_j L_j^2` are dominated by `4 (2B^{1-2α})^{n-j} I_n L_n^2`, a geometric
series because `2B^{1-2α} < 1`.  The growth constant is `λ = B^{2α-1}/4`.
-/
import RWRS.Support.CombSum
import RWRS.Support.CombArith

namespace RWRS.Support

variable {B : ℕ} {α : ℝ} {n : ℕ} {w : List (Fin B)}

theorem combLen_zero (B : ℕ) (α : ℝ) : combLen B α 0 = 1 := by
  rw [combLen]
  norm_num

/-! ### Reindexing a geometric sum -/

theorem sum_Icc_reflect (r : ℝ) (m : ℕ) :
    ∑ j ∈ Finset.Icc 1 m, r ^ (m - j) = ∑ k ∈ Finset.range m, r ^ k := by
  have hIcc : Finset.Icc 1 m = (Finset.range m).image (· + 1) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨k - 1, by omega, by omega⟩
    · rintro ⟨i, hi, rfl⟩; omega
  rw [hIcc, Finset.sum_image (by intro a _ b _ h; simp only at h; omega),
    ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun i hi => ?_
  have him : i < m := Finset.mem_range.1 hi
  congr 1
  omega

/-! ### The level terms are geometric -/

theorem level_term_le (hc : CombCond B α) (e : Bool) (hwn : w.length = n) (hn : 1 ≤ n)
    {j : ℕ} (hj : 1 ≤ j) (hjn : j ≤ n) :
    combI B (combLen B α) e n w j * (combLen B α j : ℝ) ^ 2
      ≤ 4 * (2 * (B : ℝ) / ((B : ℝ) ^ α) ^ 2) ^ (n - j)
          * (combI B (combLen B α) e n w n * (combLen B α n : ℝ) ^ 2) := by
  have hB := hc.1
  have hL2 : ∀ j, 1 ≤ j → 2 ≤ combLen B α j := fun j hj => two_le_combLen hc hj
  have hLstep : ∀ j, 1 ≤ j →
      (combLen B α (j + 1) : ℝ) ≤ ((B : ℝ) - 1) * (combLen B α j : ℝ) :=
    fun j hj => combLen_succ_le_mul hc hj
  have hbpos := base_pos hc
  have hBpos := cast_B_pos hc
  have hIle := combI_le_pow hB hL2 hLstep e hwn hn j hj hjn
  have hInn := combI_nonneg hB hL2 e hwn hn n hn le_rfl
  have hsq := combLen_sq_ratio hc hn hjn
  have hb2 : (0 : ℝ) < ((B : ℝ) ^ α) ^ 2 := by positivity
  have hb2n : (0 : ℝ) < (((B : ℝ) ^ α) ^ 2) ^ (n - j) := by positivity
  have hLjsq : (0 : ℝ) ≤ (combLen B α j : ℝ) ^ 2 := by positivity
  have hIjnn := combI_nonneg hB hL2 e hwn hn j hj hjn
  have hpow : (0 : ℝ) ≤ (2 * (B : ℝ)) ^ (n - j) := by positivity
  have hratio : (2 * (B : ℝ) / ((B : ℝ) ^ α) ^ 2) ^ (n - j)
      = (2 * (B : ℝ)) ^ (n - j) / (((B : ℝ) ^ α) ^ 2) ^ (n - j) := by
    rw [div_pow]
  rw [hratio]
  have step1 : combI B (combLen B α) e n w j * (combLen B α j : ℝ) ^ 2
      ≤ (2 * (B : ℝ)) ^ (n - j) * combI B (combLen B α) e n w n * (combLen B α j : ℝ) ^ 2 := by
    nlinarith
  have step2 : (combLen B α j : ℝ) ^ 2
      ≤ 4 * (combLen B α n : ℝ) ^ 2 / (((B : ℝ) ^ α) ^ 2) ^ (n - j) := by
    rw [le_div_iff₀ hb2n]
    linarith [hsq]
  have hcoef : (0 : ℝ) ≤ (2 * (B : ℝ)) ^ (n - j) * combI B (combLen B α) e n w n :=
    mul_nonneg hpow hInn
  have step3 : (2 * (B : ℝ)) ^ (n - j) * combI B (combLen B α) e n w n
        * (combLen B α j : ℝ) ^ 2
      ≤ (2 * (B : ℝ)) ^ (n - j) * combI B (combLen B α) e n w n
        * (4 * (combLen B α n : ℝ) ^ 2 / (((B : ℝ) ^ α) ^ 2) ^ (n - j)) :=
    mul_le_mul_of_nonneg_left step2 hcoef
  have hfinal : (2 * (B : ℝ)) ^ (n - j) * combI B (combLen B α) e n w n
        * (4 * (combLen B α n : ℝ) ^ 2 / (((B : ℝ) ^ α) ^ 2) ^ (n - j))
      = 4 * ((2 * (B : ℝ)) ^ (n - j) / (((B : ℝ) ^ α) ^ 2) ^ (n - j))
        * (combI B (combLen B α) e n w n * (combLen B α n : ℝ) ^ 2) := by
    field_simp
  linarith [step1, step3, hfinal.le, hfinal.ge]

/-! ### Part (c) with an explicit constant -/

/-- The constant `C_comb` of part (c), depending only on `B` and `α`. -/
noncomputable def combConst (B : ℕ) (α : ℝ) : ℝ :=
  16 * ((B : ℝ) + 1) / (1 - 2 * (B : ℝ) / ((B : ℝ) ^ α) ^ 2)

theorem combConst_pos (hc : CombCond B α) : 0 < combConst B α := by
  have h1 := combRatio_lt_one hc
  have h2 := cast_B_pos hc
  rw [combConst]
  apply div_pos (by linarith) (by linarith)

open scoped Classical in
theorem comb_mass_const (hc : CombCond B α) (e : Bool) (hwn : w.length = n) (hn : 1 ≤ n) :
    ∑ u ∈ combFinset B (combLen B α) n w, combVoltage B (combLen B α) e n w u
      ≤ combConst B α * combI B (combLen B α) e n w n * (combLen B α n : ℝ) ^ 2 := by
  classical
  have hB := hc.1
  have hL2 : ∀ j, 1 ≤ j → 2 ≤ combLen B α j := fun j hj => two_le_combLen hc hj
  have hLstep : ∀ j, 1 ≤ j →
      (combLen B α (j + 1) : ℝ) ≤ ((B : ℝ) - 1) * (combLen B α j : ℝ) :=
    fun j hj => combLen_succ_le_mul hc hj
  have hmass := comb_mass_le hB hL2 (combLen_zero B α) hLstep e hwn hn
  set ρ := 2 * (B : ℝ) / ((B : ℝ) ^ α) ^ 2 with hρ
  have hρ0 : 0 ≤ ρ := (combRatio_pos hc).le
  have hρ1 : ρ < 1 := combRatio_lt_one hc
  have hBc := cast_B_ge hc
  have hInn := combI_nonneg hB hL2 e hwn hn n hn le_rfl
  have hLnsq : (0 : ℝ) ≤ (combLen B α n : ℝ) ^ 2 := by positivity
  have hMnn : (0 : ℝ) ≤ combI B (combLen B α) e n w n * (combLen B α n : ℝ) ^ 2 :=
    mul_nonneg hInn hLnsq
  -- each level term
  have hterm : ∀ j ∈ Finset.Icc 1 n,
      4 * ((B : ℝ) + 1) * combI B (combLen B α) e n w j * (combLen B α j : ℝ) ^ 2
        ≤ (16 * ((B : ℝ) + 1)
            * (combI B (combLen B α) e n w n * (combLen B α n : ℝ) ^ 2)) * ρ ^ (n - j) := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    have h := level_term_le hc e hwn hn hj.1 hj.2
    have hcoef : (0 : ℝ) ≤ 4 * ((B : ℝ) + 1) := by linarith
    nlinarith [h]
  have hsum := Finset.sum_le_sum hterm
  have hgeom : ∑ j ∈ Finset.Icc 1 n,
      (16 * ((B : ℝ) + 1) * (combI B (combLen B α) e n w n * (combLen B α n : ℝ) ^ 2))
        * ρ ^ (n - j)
      = (16 * ((B : ℝ) + 1) * (combI B (combLen B α) e n w n * (combLen B α n : ℝ) ^ 2))
        * ∑ k ∈ Finset.range n, ρ ^ k := by
    rw [← Finset.mul_sum, sum_Icc_reflect]
  rw [hgeom] at hsum
  have hgle := sum_geom_le hρ0 hρ1 n
  have hCnn : (0 : ℝ) ≤ 16 * ((B : ℝ) + 1)
      * (combI B (combLen B α) e n w n * (combLen B α n : ℝ) ^ 2) := by
    have : (0 : ℝ) ≤ 16 * ((B : ℝ) + 1) := by linarith
    exact mul_nonneg this hMnn
  have hlast : (16 * ((B : ℝ) + 1)
      * (combI B (combLen B α) e n w n * (combLen B α n : ℝ) ^ 2))
      * ∑ k ∈ Finset.range n, ρ ^ k
      ≤ combConst B α * combI B (combLen B α) e n w n * (combLen B α n : ℝ) ^ 2 := by
    have h1 : (16 * ((B : ℝ) + 1)
        * (combI B (combLen B α) e n w n * (combLen B α n : ℝ) ^ 2))
        * ∑ k ∈ Finset.range n, ρ ^ k
        ≤ (16 * ((B : ℝ) + 1)
            * (combI B (combLen B α) e n w n * (combLen B α n : ℝ) ^ 2)) * (1 / (1 - ρ)) :=
      mul_le_mul_of_nonneg_left hgle hCnn
    have h2 : (16 * ((B : ℝ) + 1)
        * (combI B (combLen B α) e n w n * (combLen B α n : ℝ) ^ 2)) * (1 / (1 - ρ))
        = combConst B α * combI B (combLen B α) e n w n * (combLen B α n : ℝ) ^ 2 := by
      rw [combConst, ← hρ]
      field_simp
    linarith
  linarith

/-! ### Part (e) -/

theorem comb_growth (hc : CombCond B α) (e : Bool) (hwn : w.length = n) (hn : 1 ≤ n) :
    combLambda B α ^ n / 4
      ≤ combI B (combLen B α) e n w n * (combLen B α n : ℝ) ^ 2 := by
  have hB := hc.1
  have hL2 : ∀ j, 1 ≤ j → 2 ≤ combLen B α j := fun j hj => two_le_combLen hc hj
  have hLstep : ∀ j, 1 ≤ j →
      (combLen B α (j + 1) : ℝ) ≤ ((B : ℝ) - 1) * (combLen B α j : ℝ) :=
    fun j hj => combLen_succ_le_mul hc hj
  have hLone := two_combLen_one_le hc
  have hI := combI_ge_pow hB hL2 hLstep hLone e hwn hn n hn le_rfl
  have hL := combLen_ge hc hn
  have hbpos := base_pos hc
  have hBpos := cast_B_pos hc
  have h4B : (0 : ℝ) < 4 * (B : ℝ) := by linarith
  have hpow : (0 : ℝ) < (4 * (B : ℝ)) ^ n := pow_pos h4B n
  have hbn : (0 : ℝ) < ((B : ℝ) ^ α) ^ n := pow_pos hbpos n
  have hLsq : (((B : ℝ) ^ α) ^ n) ^ 2 / 4 ≤ (combLen B α n : ℝ) ^ 2 := by
    have hLnn : (0 : ℝ) ≤ (combLen B α n : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hkey : ((4 * (B : ℝ)) ^ n)⁻¹ * ((((B : ℝ) ^ α) ^ n) ^ 2 / 4)
      ≤ combI B (combLen B α) e n w n * (combLen B α n : ℝ) ^ 2 := by
    have h1 : (0 : ℝ) < ((4 * (B : ℝ)) ^ n)⁻¹ := by positivity
    have h2 : (0 : ℝ) ≤ (((B : ℝ) ^ α) ^ n) ^ 2 / 4 := by positivity
    nlinarith
  refine le_trans (le_of_eq ?_) hkey
  rw [combLambda_eq hc]
  rw [div_pow]
  have hcollapse : (((B : ℝ) ^ α) ^ 2) ^ n = (((B : ℝ) ^ α) ^ n) ^ 2 := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  rw [hcollapse]
  field_simp

end RWRS.Support
