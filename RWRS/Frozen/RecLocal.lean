/-
Corollary 6.13 of `rwrs.tex`, frozen.  `rwrs.tex:1792-1799` (label
`cor:rec-loc`), under the setup of `sec:recurrent-nonstab`:

  "Define $\delta\coloneqq\frac{\log\lambda}{\alpha\log B}>0$ and
   $\lambda=\frac{B^{2\alpha-1}}{4}$.  There exists $c_{\mathrm{loc}}>0$ such
   that whenever a vertex $v$ in the first half of the terminal pipe satisfies
   $Y_v\geq KL_m$, then
   $\sum_{u\in D_{m,\omega}}g(u)a(u)\geq c_{\mathrm{loc}}R_m^{\delta}$."

Here `a(v) = Y_v - b` and `K = 2 + 2b(C_comb+1)` as in `eq:rec-ab` and
`eq:rec-K`, with `C_comb` the constant of `prop:comb-estimates`(c); the
hypothesis `hC` says that `C_comb` is such a constant, so the corollary is
stated for the constant the paper feeds it.  The exponent `δ` is
`log λ / (α log B)`.
-/
import RWRS.Support.CombFinal
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base

open scoped ENNReal

-- FROZEN-STATEMENT-BEGIN
theorem RWRS.Frozen.recLocal (B : ℕ) (α : ℝ) (hcond : RWRS.CombCond B α)
    (C_comb : ℝ) (hCpos : 0 < C_comb)
    (hC : ∀ (e : Bool) (n : ℕ) (w : List (Fin B)), w.length = n → 1 ≤ n →
      (∑' u : ↥(RWRS.combSet B (RWRS.combLen B α) n w),
          RWRS.combVoltage B (RWRS.combLen B α) e n w u)
        ≤ C_comb * RWRS.combI B (RWRS.combLen B α) e n w n
            * (RWRS.combLen B α n : ℝ) ^ 2) :
    ∃ c_loc : ℝ, 0 < c_loc ∧
      ∀ (e : Bool) (m : ℕ) (ω : List (Fin B)), ω.length = m → 1 ≤ m →
        ∀ (Y : List (Fin B) × ℕ → ℝ) (b : ℝ), 0 ≤ b → (∀ v, 1 ≤ Y v) →
          ∀ v ∈ RWRS.combFirstHalf B (RWRS.combLen B α) m ω,
            (2 + 2 * b * (C_comb + 1)) * (RWRS.combLen B α m : ℝ) ≤ Y v →
            c_loc * (RWRS.gadgetRadius (RWRS.combLen B α) m : ℝ)
                ^ (Real.log (RWRS.combLambda B α) / (α * Real.log B))
              ≤ ∑' u : ↥(RWRS.combSet B (RWRS.combLen B α) m ω),
                  RWRS.combVoltage B (RWRS.combLen B α) e m ω u * (Y u - b)
-- FROZEN-STATEMENT-END
:= by
  classical
  have hB := hcond.1
  have hL2 : ∀ j, 1 ≤ j → 2 ≤ RWRS.combLen B α j :=
    fun j hj => RWRS.Support.two_le_combLen hcond hj
  have hBpos : (0 : ℝ) < (B : ℝ) := RWRS.Support.cast_B_pos hcond
  have hbpos : (0 : ℝ) < (B : ℝ) ^ α := RWRS.Support.base_pos hcond
  have hδpos := RWRS.Support.delta_pos hcond
  have hlampos : (0 : ℝ) < RWRS.combLambda B α := by
    have : (1 : ℝ) < RWRS.combLambda B α := hcond.2.2.2.2.2.2
    linarith
  have hαpos := RWRS.Support.alpha_pos hcond
  -- the constant of the radius bound
  have hinv : (0 : ℝ) < 1 - (B : ℝ) ^ (-α) := by
    have h1 : (B : ℝ) ^ (-α) < 1 := by
      rw [Real.rpow_neg hBpos.le]
      have h2 : (1 : ℝ) < (B : ℝ) ^ α := by
        have := RWRS.Support.base_ge hcond; linarith
      rw [inv_lt_one_iff₀]
      exact Or.inr h2
    linarith
  set K₀ : ℝ := 2 / (1 - (B : ℝ) ^ (-α)) with hK₀def
  have hK₀pos : (0 : ℝ) < K₀ := by rw [hK₀def]; positivity
  have hKδ : (0 : ℝ) < K₀ ^ (Real.log (RWRS.combLambda B α) / (α * Real.log B)) :=
    Real.rpow_pos_of_pos hK₀pos _
  refine ⟨1 / (4 * K₀ ^ (Real.log (RWRS.combLambda B α) / (α * Real.log B))), by positivity, ?_⟩
  intro e m ω hω hm Y b hb hY v hv hYv
  -- the spike bound
  have htsum : ∀ (f : List (Fin B) × ℕ → ℝ),
      (∑' u : ↥(RWRS.combSet B (RWRS.combLen B α) m ω), f u)
        = ∑ u ∈ RWRS.Support.combFinset B (RWRS.combLen B α) m ω, f u := by
    intro f
    rw [← RWRS.Support.coe_combFinset (B := B) (L := RWRS.combLen B α) m ω]
    exact Finset.tsum_subtype' _ f
  have hmass : ∑ u ∈ RWRS.Support.combFinset B (RWRS.combLen B α) m ω,
      RWRS.combVoltage B (RWRS.combLen B α) e m ω u
      ≤ C_comb * RWRS.combI B (RWRS.combLen B α) e m ω m
          * (RWRS.combLen B α m : ℝ) ^ 2 := by
    rw [← htsum (fun u => RWRS.combVoltage B (RWRS.combLen B α) e m ω u)]
    exact hC e m ω hω hm
  have ha : ∀ u ∈ RWRS.combSet B (RWRS.combLen B α) m ω, -b ≤ Y u - b := by
    intro u _
    have := hY u
    linarith
  have hav : (2 + 2 * b * (C_comb + 1)) * (RWRS.combLen B α m : ℝ) - b ≤ Y v - b := by
    linarith [hYv]
  have hspike := RWRS.Support.comb_spike hB hL2 e hω hm hCpos hmass
    (fun u => Y u - b) hb ha hv hav
  rw [htsum (fun u => RWRS.combVoltage B (RWRS.combLen B α) e m ω u * (Y u - b))]
  have hgrow := RWRS.Support.comb_growth hcond e hω hm
  have hstep1 : 1 / (4 * K₀ ^ (Real.log (RWRS.combLambda B α) / (α * Real.log B)))
      * (RWRS.gadgetRadius (RWRS.combLen B α) m : ℝ)
          ^ (Real.log (RWRS.combLambda B α) / (α * Real.log B))
      ≤ RWRS.combLambda B α ^ m / 4 := by
    have hR := RWRS.Support.gadgetRadius_le hcond hm
    have hL := RWRS.Support.combLen_le hcond m
    have hRnn : (0 : ℝ) ≤ (RWRS.gadgetRadius (RWRS.combLen B α) m : ℝ) := Nat.cast_nonneg _
    have hchain : (RWRS.gadgetRadius (RWRS.combLen B α) m : ℝ) ≤ K₀ * ((B : ℝ) ^ α) ^ m := by
      have hLnn : (0 : ℝ) ≤ (RWRS.combLen B α m : ℝ) := Nat.cast_nonneg _
      calc (RWRS.gadgetRadius (RWRS.combLen B α) m : ℝ)
          ≤ K₀ * (RWRS.combLen B α m : ℝ) := by rw [hK₀def]; exact hR
        _ ≤ K₀ * ((B : ℝ) ^ α) ^ m := by nlinarith
    have hpowle : (RWRS.gadgetRadius (RWRS.combLen B α) m : ℝ)
          ^ (Real.log (RWRS.combLambda B α) / (α * Real.log B))
        ≤ (K₀ * ((B : ℝ) ^ α) ^ m)
          ^ (Real.log (RWRS.combLambda B α) / (α * Real.log B)) :=
      Real.rpow_le_rpow hRnn hchain hδpos.le
    have hsplit : (K₀ * ((B : ℝ) ^ α) ^ m)
          ^ (Real.log (RWRS.combLambda B α) / (α * Real.log B))
        = K₀ ^ (Real.log (RWRS.combLambda B α) / (α * Real.log B))
          * RWRS.combLambda B α ^ m := by
      rw [Real.mul_rpow hK₀pos.le (by positivity)]
      congr 1
      rw [RWRS.Support.base_pow hcond m, ← Real.rpow_mul hBpos.le]
      have hexp : α * (m : ℝ) * (Real.log (RWRS.combLambda B α) / (α * Real.log B))
          = (Real.log (RWRS.combLambda B α) / Real.log B) * (m : ℝ) := by
        have hlogB : Real.log (B : ℝ) ≠ 0 := ne_of_gt (RWRS.Support.log_base_pos hcond)
        field_simp
      have hBne : (B : ℝ) ≠ 1 := by
        have h2 : (2 : ℝ) ≤ (B : ℝ) := RWRS.Support.cast_B_ge hcond
        intro hcon
        rw [hcon] at h2
        norm_num at h2
      rw [hexp, Real.rpow_mul hBpos.le, Real.rpow_natCast]
      congr 1
      rw [Real.log_div_log, Real.rpow_logb hBpos hBne hlampos]
    rw [hsplit] at hpowle
    have hlamm : (0 : ℝ) < RWRS.combLambda B α ^ m := pow_pos hlampos m
    rw [one_div, inv_mul_eq_div, div_le_iff₀ (by positivity)]
    nlinarith [hpowle]
  linarith [hstep1, hgrow, hspike]
