/-
Parts (a), (b) and (e) of `prop:comb-estimates`: the continuation resistance,
the trunk currents and their exponential growth.

Everything is read off the node law.  The trunk currents are nonnegative by a
downward induction from the terminal pipe, where `V_{n-1} = I_n L_n` because the
far endpoint of the terminal pipe is outside the comb.  The continuation
resistance bound `V_j ≤ 2 I_{j+1} L_{j+1}` is the trunk step together with the
node law at `b_{j+1}`, which says that the `B-1` side currents alone already
account for `(B-1) V_{j+1} / L_{j+2}` of `I_{j+1}`, and `L_{j+2} ≤ (B-1)L_{j+1}`.
-/
import RWRS.Support.CombVolt

namespace RWRS.Support

variable {B : ℕ} {L : ℕ → ℕ} {n : ℕ} {w : List (Fin B)}

theorem combLen_cast_pos (hL2 : ∀ j, 1 ≤ j → 2 ≤ L j) {j : ℕ} (hj : 1 ≤ j) :
    (0 : ℝ) < (L j : ℝ) := by
  have := hL2 j hj
  have : 0 < L j := by omega
  exact_mod_cast this

theorem combV_nonneg (hL2 : ∀ j, 1 ≤ j → 2 ≤ L j) (e : Bool) (hwn : w.length = n) (j : ℕ) :
    0 ≤ combV B L e n w j := combVoltage_nonneg hL2 e hwn _

/-- `V_{n-1} = I_n L_n`: the terminal pipe ends at the boundary. -/
theorem terminal_step (hB : 2 ≤ B) (hL2 : ∀ j, 1 ≤ j → 2 ≤ L j) (e : Bool)
    (hwn : w.length = n) (hn : 1 ≤ n) :
    combV B L e n w (n - 1) = (L n : ℝ) * combI B L e n w n := by
  have hstep := trunk_step hB hL2 e hwn hn (j := n) hn le_rfl
  rw [trunk_end hL2 e hwn] at hstep
  linarith

/-- **The trunk currents are nonnegative.** -/
theorem combI_nonneg (hB : 2 ≤ B) (hL2 : ∀ j, 1 ≤ j → 2 ≤ L j) (e : Bool)
    (hwn : w.length = n) (hn : 1 ≤ n) :
    ∀ j, 1 ≤ j → j ≤ n → 0 ≤ combI B L e n w j := by
  have key : ∀ k j, n - j = k → 1 ≤ j → j ≤ n → 0 ≤ combI B L e n w j := by
    intro k
    induction k with
    | zero =>
        intro j hk hj hjn
        have hjn' : j = n := by omega
        subst hjn'
        have hterm := terminal_step hB hL2 e hwn hn
        have hV := combV_nonneg hL2 e hwn (j - 1)
        have hL := combLen_cast_pos hL2 (j := j) hj
        nlinarith
    | succ k ih =>
        intro j hk hj hjn
        have hjn' : j < n := by omega
        have hnext := ih (j + 1) (by omega) (by omega) (by omega)
        have hnode := node_law_branch hB hL2 e hwn hn hj hjn'
        have hV := combV_nonneg hL2 e hwn j
        have hL := combLen_cast_pos hL2 (j := j + 1) (by omega)
        have hBr : (1 : ℝ) ≤ (B : ℝ) - 1 := by
          have : (2 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
          linarith
        nlinarith
  exact fun j hj hjn => key (n - j) j rfl hj hjn

/-- **Part (a): the continuation resistance.**  `V_j ≤ 2 I_{j+1} L_{j+1}`. -/
theorem combV_le_two_mul (hB : 2 ≤ B) (hL2 : ∀ j, 1 ≤ j → 2 ≤ L j)
    (hLstep : ∀ j, 1 ≤ j → (L (j + 1) : ℝ) ≤ ((B : ℝ) - 1) * (L j : ℝ))
    (e : Bool) (hwn : w.length = n) (hn : 1 ≤ n) {j : ℕ} (hjn : j < n) :
    combV B L e n w j ≤ 2 * combI B L e n w (j + 1) * (L (j + 1) : ℝ) := by
  have hBr : (1 : ℝ) ≤ (B : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
    linarith
  have hI1 := combI_nonneg hB hL2 e hwn hn (j + 1) (by omega) (by omega)
  have hL1 := combLen_cast_pos hL2 (j := j + 1) (by omega)
  rcases eq_or_lt_of_le (show j + 1 ≤ n by omega) with heq | hlt
  · have hj' : j = n - 1 := by omega
    subst hj'
    have hterm := terminal_step hB hL2 e hwn hn
    rw [show n - 1 + 1 = n by omega] at *
    nlinarith
  · have hstep := trunk_step hB hL2 e hwn hn (j := j + 1) (by omega) (by omega)
    rw [show j + 1 - 1 = j by omega] at hstep
    have hnode := node_law_branch hB hL2 e hwn hn (j := j + 1) (by omega) hlt
    have hI2 := combI_nonneg hB hL2 e hwn hn (j + 2) (by omega) (by omega)
    have hL2' := combLen_cast_pos hL2 (j := j + 2) (by omega)
    have hLs := hLstep (j + 1) (by omega)
    have hVnn := combV_nonneg hL2 e hwn (j + 1)
    rw [show j + 1 + 1 = j + 2 by omega] at hnode hLs
    -- (B-1) V_{j+1} ≤ I_{j+1} L_{j+2} ≤ I_{j+1} (B-1) L_{j+1}
    have h1 : ((B : ℝ) - 1) * combV B L e n w (j + 1)
        ≤ combI B L e n w (j + 1) * (L (j + 2) : ℝ) := by nlinarith
    have h2 : ((B : ℝ) - 1) * combV B L e n w (j + 1)
        ≤ combI B L e n w (j + 1) * (((B : ℝ) - 1) * (L (j + 1) : ℝ)) := by nlinarith
    have h3 : combV B L e n w (j + 1) ≤ combI B L e n w (j + 1) * (L (j + 1) : ℝ) := by
      nlinarith
    linarith

/-- **Part (a) in the form of a resistance.**  `R_j ≤ 2 L_{j+1}`. -/
theorem combR_le (hB : 2 ≤ B) (hL2 : ∀ j, 1 ≤ j → 2 ≤ L j)
    (hLstep : ∀ j, 1 ≤ j → (L (j + 1) : ℝ) ≤ ((B : ℝ) - 1) * (L j : ℝ))
    (e : Bool) (hwn : w.length = n) (hn : 1 ≤ n) {j : ℕ} (hjn : j < n) :
    combR B L e n w j ≤ 2 * (L (j + 1) : ℝ) := by
  have hV := combV_le_two_mul hB hL2 hLstep e hwn hn hjn
  have hI := combI_nonneg hB hL2 e hwn hn (j + 1) (by omega) (by omega)
  have hVnn := combV_nonneg hL2 e hwn j
  have hL1 := combLen_cast_pos hL2 (j := j + 1) (by omega)
  rw [combR]
  rcases eq_or_lt_of_le hI with heq | hpos
  · rw [← heq, div_zero]
    positivity
  · rw [div_le_iff₀ hpos]
    nlinarith

/-- **Part (b), first inequality.**  `I_1 ≥ 1/(4B)`. -/
theorem combI_one_ge (hB : 2 ≤ B) (hL2 : ∀ j, 1 ≤ j → 2 ≤ L j)
    (hLstep : ∀ j, 1 ≤ j → (L (j + 1) : ℝ) ≤ ((B : ℝ) - 1) * (L j : ℝ))
    (hLone : 2 * (L 1 : ℝ) ≤ (B : ℝ) - 1)
    (e : Bool) (hwn : w.length = n) (hn : 1 ≤ n) :
    1 / (4 * (B : ℝ)) ≤ combI B L e n w 1 := by
  have hBc : (2 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
  have hroot := node_law_root hB hL2 e hwn hn
  have hV0 := combV_le_two_mul hB hL2 hLstep e hwn hn (j := 0) (by omega)
  rw [show (0 : ℕ) + 1 = 1 from rfl] at hV0
  have hI1 := combI_nonneg hB hL2 e hwn hn 1 le_rfl hn
  have hV0nn := combV_nonneg hL2 e hwn 0
  have hL1 := combLen_cast_pos hL2 (j := 1) le_rfl
  have hextra : (if e then combV B L e n w 0 * (L 1 : ℝ) else 0)
      ≤ ((B : ℝ) - 1) * (combI B L e n w 1 * (L 1 : ℝ)) := by
    have hb : combV B L e n w 0 * (L 1 : ℝ)
        ≤ ((B : ℝ) - 1) * (combI B L e n w 1 * (L 1 : ℝ)) := by nlinarith
    cases e with
    | false => simp only [Bool.false_eq_true, if_false]; nlinarith
    | true => simpa using hb
  have hside : ((B : ℝ) - 1) * combV B L e n w 0
      ≤ 2 * ((B : ℝ) - 1) * (combI B L e n w 1 * (L 1 : ℝ)) := by nlinarith
  have hkey : (L 1 : ℝ) ≤ 4 * (B : ℝ) * (combI B L e n w 1 * (L 1 : ℝ)) := by nlinarith
  rw [div_le_iff₀ (by nlinarith : (0 : ℝ) < 4 * (B : ℝ))]
  nlinarith

/-- **Part (b), second inequality.**  `I_{j+1} ≥ I_j/(2B)`. -/
theorem combI_step_ge (hB : 2 ≤ B) (hL2 : ∀ j, 1 ≤ j → 2 ≤ L j)
    (hLstep : ∀ j, 1 ≤ j → (L (j + 1) : ℝ) ≤ ((B : ℝ) - 1) * (L j : ℝ))
    (e : Bool) (hwn : w.length = n) (hn : 1 ≤ n) {j : ℕ} (hj : 1 ≤ j) (hjn : j < n) :
    combI B L e n w j / (2 * (B : ℝ)) ≤ combI B L e n w (j + 1) := by
  have hBc : (2 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
  have hnode := node_law_branch hB hL2 e hwn hn hj hjn
  have hV := combV_le_two_mul hB hL2 hLstep e hwn hn hjn
  have hI1 := combI_nonneg hB hL2 e hwn hn (j + 1) (by omega) (by omega)
  have hL1 := combLen_cast_pos hL2 (j := j + 1) (by omega)
  have hkey : combI B L e n w j * (L (j + 1) : ℝ)
      ≤ 2 * (B : ℝ) * (combI B L e n w (j + 1) * (L (j + 1) : ℝ)) := by nlinarith
  rw [div_le_iff₀ (by nlinarith : (0 : ℝ) < 2 * (B : ℝ))]
  nlinarith

/-- **Part (b), the consequence.**  `I_j ≥ (4B)^{-j}`. -/
theorem combI_ge_pow (hB : 2 ≤ B) (hL2 : ∀ j, 1 ≤ j → 2 ≤ L j)
    (hLstep : ∀ j, 1 ≤ j → (L (j + 1) : ℝ) ≤ ((B : ℝ) - 1) * (L j : ℝ))
    (hLone : 2 * (L 1 : ℝ) ≤ (B : ℝ) - 1)
    (e : Bool) (hwn : w.length = n) (hn : 1 ≤ n) :
    ∀ j, 1 ≤ j → j ≤ n → ((4 * (B : ℝ)) ^ j)⁻¹ ≤ combI B L e n w j := by
  have hBc : (2 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
  have h4B : (0 : ℝ) < 4 * (B : ℝ) := by linarith
  intro j hj
  induction j, hj using Nat.le_induction with
  | base =>
      intro _
      have := combI_one_ge hB hL2 hLstep hLone e hwn hn
      rw [pow_one]
      rw [one_div] at this
      exact this
  | succ j hj ih =>
      intro hjn
      have hprev := ih (by omega)
      have hstep := combI_step_ge hB hL2 hLstep e hwn hn hj (by omega)
      have hpow : (0 : ℝ) < (4 * (B : ℝ)) ^ j := pow_pos h4B j
      have hpow' : (0 : ℝ) < (4 * (B : ℝ)) ^ (j + 1) := pow_pos h4B (j + 1)
      have hchain : ((4 * (B : ℝ)) ^ j)⁻¹ / (2 * (B : ℝ)) ≤ combI B L e n w (j + 1) := by
        refine le_trans ?_ hstep
        gcongr
      refine le_trans ?_ hchain
      have heq1 : ((4 * (B : ℝ)) ^ j)⁻¹ / (2 * (B : ℝ))
          = ((4 * (B : ℝ)) ^ j * (2 * (B : ℝ)))⁻¹ := by
        field_simp
      have heq2 : ((4 * (B : ℝ)) ^ (j + 1))⁻¹
          = ((4 * (B : ℝ)) ^ j * (4 * (B : ℝ)))⁻¹ := by
        rw [pow_succ]
      rw [heq1, heq2]
      gcongr
      linarith

/-- The trunk currents grow by at most `2B` per level towards the root. -/
theorem combI_le_pow (hB : 2 ≤ B) (hL2 : ∀ j, 1 ≤ j → 2 ≤ L j)
    (hLstep : ∀ j, 1 ≤ j → (L (j + 1) : ℝ) ≤ ((B : ℝ) - 1) * (L j : ℝ))
    (e : Bool) (hwn : w.length = n) (hn : 1 ≤ n) :
    ∀ j, 1 ≤ j → j ≤ n →
      combI B L e n w j ≤ (2 * (B : ℝ)) ^ (n - j) * combI B L e n w n := by
  have hBc : (2 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
  have key : ∀ k j, n - j = k → 1 ≤ j → j ≤ n →
      combI B L e n w j ≤ (2 * (B : ℝ)) ^ k * combI B L e n w n := by
    intro k
    induction k with
    | zero =>
        intro j hk hj hjn
        have : j = n := by omega
        subst this
        simp
    | succ k ih =>
        intro j hk hj hjn
        have hjn' : j < n := by omega
        have hprev := ih (j + 1) (by omega) (by omega) (by omega)
        have hstep := combI_step_ge hB hL2 hLstep e hwn hn hj hjn'
        have hI : combI B L e n w j ≤ 2 * (B : ℝ) * combI B L e n w (j + 1) := by
          rw [div_le_iff₀ (by linarith : (0 : ℝ) < 2 * (B : ℝ))] at hstep
          linarith
        have hpk : (0 : ℝ) ≤ (2 * (B : ℝ)) ^ k := by positivity
        calc combI B L e n w j ≤ 2 * (B : ℝ) * combI B L e n w (j + 1) := hI
          _ ≤ 2 * (B : ℝ) * ((2 * (B : ℝ)) ^ k * combI B L e n w n) := by nlinarith
          _ = (2 * (B : ℝ)) ^ (k + 1) * combI B L e n w n := by ring
  exact fun j hj hjn => key (n - j) j rfl hj hjn

end RWRS.Support
