/-
Lemma 6.12 of `rwrs.tex`, frozen.  `rwrs.tex:1740-1747` (label
`lem:rec-geometry`), under the setup of `sec:recurrent-nonstab`
(`rwrs.tex:1717-1736`), where `α = 1/(d_f-1)`, equivalently `d_f = 1 + 1/α`:

  "Let $C_R\coloneqq2/(1-B^{-\alpha})$.  There exist constants
   $c_N,C_N,C_{\mathrm{ball}}>0$ depending only on $B$ and $\alpha$ such that
   the following hold.
   (a) For every $m\geq1$, $L_m\leq R_m\leq C_RL_m$.
   (b) For every $m\geq0$, $c_NR_m^{d_f}\leq N_m\leq C_NR_m^{d_f}$.
   (c) For every $m\geq1$ and every $1\leq t\leq R_m$,
   $|B_{H(m)}(x,t)\setminus\{x\}|\leq C_{\mathrm{ball}}t^{d_f}$."

`R_m` is `gadgetRadius`, `N_m` is `gadgetSize`, `H(m)` is `gadgetGraph` and its
root `x` is `gadgetRoot`.  The cardinality in (c) is the `encard` of the ball,
in `[0,∞]`, so a hypothetical infinite ball would not be given a junk finite
value.
-/
import RWRS.Support.GadgetBall
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

open scoped ENNReal

-- FROZEN-STATEMENT-BEGIN
theorem RWRS.Frozen.gadgetGeometry (B : ℕ) (α d_f : ℝ) (hcond : RWRS.CombCond B α)
    (hdf : d_f = 1 + 1 / α) :
    ∃ c_N C_N C_ball : ℝ, 0 < c_N ∧ 0 < C_N ∧ 0 < C_ball ∧
      (∀ m : ℕ, 1 ≤ m →
        (RWRS.combLen B α m : ℝ) ≤ (RWRS.gadgetRadius (RWRS.combLen B α) m : ℝ) ∧
        (RWRS.gadgetRadius (RWRS.combLen B α) m : ℝ)
          ≤ 2 / (1 - (B : ℝ) ^ (-α)) * (RWRS.combLen B α m : ℝ)) ∧
      (∀ m : ℕ,
        c_N * (RWRS.gadgetRadius (RWRS.combLen B α) m : ℝ) ^ d_f
            ≤ (RWRS.gadgetSize B (RWRS.combLen B α) m : ℝ) ∧
        (RWRS.gadgetSize B (RWRS.combLen B α) m : ℝ)
            ≤ C_N * (RWRS.gadgetRadius (RWRS.combLen B α) m : ℝ) ^ d_f) ∧
      (∀ m : ℕ, 1 ≤ m → ∀ t : ℕ, 1 ≤ t → t ≤ RWRS.gadgetRadius (RWRS.combLen B α) m →
        (RWRS.closedBall (RWRS.gadgetGraph B (RWRS.combLen B α) m)
              (RWRS.gadgetRoot B (RWRS.combLen B α) m) t \
            {RWRS.gadgetRoot B (RWRS.combLen B α) m}).encard
          ≤ ENNReal.ofReal (C_ball * (t : ℝ) ^ d_f))
-- FROZEN-STATEMENT-END
:= by
  classical
  have hb4 : (4 : ℝ) ≤ (B : ℝ) ^ α := RWRS.Support.base_ge hcond
  have hden : (0 : ℝ) < (B : ℝ) ^ α - 1 := by linarith
  have hApos : (0 : ℝ) < (B : ℝ) ^ α / ((B : ℝ) ^ α - 1) := by
    apply div_pos <;> linarith
  have hApow : (0 : ℝ) < ((B : ℝ) ^ α / ((B : ℝ) ^ α - 1)) ^ d_f :=
    Real.rpow_pos_of_pos hApos _
  have hBpos : (0 : ℝ) < (B : ℝ) := RWRS.Support.cast_B_pos hcond
  refine ⟨1 / (2 * ((B : ℝ) ^ α / ((B : ℝ) ^ α - 1)) ^ d_f), 2 * (2 : ℝ) ^ d_f,
    4 * (B : ℝ) ^ 2 * (2 : ℝ) ^ (1 / α), by positivity, by positivity, by positivity,
    ?_, ?_, ?_⟩
  · intro m hm
    exact RWRS.Support.gadgetRadius_bounds hcond hm
  · intro m
    exact RWRS.Support.gadgetSize_asymp hcond hdf m
  · intro m hm t ht htm
    have h1 := RWRS.Support.encard_ball_le_card hcond htm
    have h2 := RWRS.Support.card_bound_real (B := B) (α := α) hcond hdf ht
    set N := (RWRS.Support.wordsLe B
      (RWRS.Support.gadgetLevel (RWRS.combLen B α) t + 1)).card * (t + 1) with hN
    calc ((RWRS.closedBall (RWRS.gadgetGraph B (RWRS.combLen B α) m)
              (RWRS.gadgetRoot B (RWRS.combLen B α) m) t \
            {RWRS.gadgetRoot B (RWRS.combLen B α) m}).encard : ℝ≥0∞)
        ≤ ((N : ℕ∞) : ℝ≥0∞) := ENat.toENNReal_mono h1
      _ = ENNReal.ofReal (N : ℝ) := by simp
      _ ≤ ENNReal.ofReal (4 * (B : ℝ) ^ 2 * (2 : ℝ) ^ (1 / α) * (t : ℝ) ^ d_f) :=
          ENNReal.ofReal_le_ofReal h2
