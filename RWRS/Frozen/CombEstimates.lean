/-
Proposition 6.7 of `rwrs.tex`, frozen.  `rwrs.tex:1530-1545` (label
`prop:comb-estimates`), under the setup of `ssec:comb-estimates`
(`rwrs.tex:1505-1528`):

  "(a) (Continuation resistance) For every $0\leq j\leq n-1$, one has
   $R_j\leq2L_{j+1}$, and hence $V_j\leq2I_{j+1}L_{j+1}$.
   (b) (Trunk currents) The trunk currents satisfy $I_1\geq1/(4B)$ and
   $I_{j+1}\geq I_j/(2B)$ for every $1\leq j\leq n-1$.  Consequently,
   $I_n\geq(4B)^{-n}$.
   (c) (Total voltage mass) There exists $C_{\mathrm{comb}}>0$ depending only on
   $B$ and $\alpha$ such that $\sum_{u\in D_{w,n}}g(u)\leq C_{\mathrm{comb}}I_nL_n^2$.
   (d) (Spike contribution) Let $a\colon D_{w,n}\to\R$ satisfy $a(u)\geq-b$ for
   all $u$, for some finite $b\geq0$, and set $K\coloneqq2+2b(C_{\mathrm{comb}}+1)$.
   If a vertex $v$ in the first half of the terminal pipe $P_w$ (at distance at
   least $L_n/2$ from the boundary) satisfies $a(v)\geq KL_n-b$, then
   $\sum_{u\in D_{w,n}}g(u)a(u)\geq I_nL_n^2$.
   (e) (Exponential growth) $I_nL_n^2\geq\lambda^n/4$."

The setup is the tree of pipes of `RWRS.pipeGraph` with pipe lengths
`L_j = ⌊B^{αj}⌋`, the comb `RWRS.combSet`, and the voltage
`RWRS.combVoltage`, the killed Green function with unit current entering at the
root.  With unit conductances the current through a pipe is the voltage drop
across one of its edges, which is `RWRS.combI`, and `RWRS.combR` is defined by
Ohm's law `V_j = I_{j+1}R_j`, so that identity needs no separate hypothesis.
The flag `e` is the paper's "at most one extra boundary edge of unit resistance"
at the root, which is present exactly when `e` is on.  The constant
`C_comb` depends only on `B` and `α`, so it is bound before `n` and `w`.
-/
import RWRS.Support.CombFinal
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

open scoped ENNReal

-- FROZEN-STATEMENT-BEGIN
theorem RWRS.Frozen.combEstimates (B : ℕ) (α : ℝ) (hcond : RWRS.CombCond B α) :
    (∀ (e : Bool) (n : ℕ) (w : List (Fin B)), w.length = n → 1 ≤ n →
      ∀ j : ℕ, j ≤ n - 1 →
        RWRS.combR B (RWRS.combLen B α) e n w j ≤ 2 * (RWRS.combLen B α (j + 1) : ℝ) ∧
        RWRS.combV B (RWRS.combLen B α) e n w j
          ≤ 2 * RWRS.combI B (RWRS.combLen B α) e n w (j + 1)
            * (RWRS.combLen B α (j + 1) : ℝ)) ∧
    (∀ (e : Bool) (n : ℕ) (w : List (Fin B)), w.length = n → 1 ≤ n →
      1 / (4 * (B : ℝ)) ≤ RWRS.combI B (RWRS.combLen B α) e n w 1 ∧
      (∀ j : ℕ, 1 ≤ j → j ≤ n - 1 →
        RWRS.combI B (RWRS.combLen B α) e n w j / (2 * (B : ℝ))
          ≤ RWRS.combI B (RWRS.combLen B α) e n w (j + 1)) ∧
      (4 * (B : ℝ)) ^ (-(n : ℝ)) ≤ RWRS.combI B (RWRS.combLen B α) e n w n) ∧
    (∃ C_comb : ℝ, 0 < C_comb ∧
      (∀ (e : Bool) (n : ℕ) (w : List (Fin B)), w.length = n → 1 ≤ n →
        (∑' u : ↥(RWRS.combSet B (RWRS.combLen B α) n w),
            RWRS.combVoltage B (RWRS.combLen B α) e n w u)
          ≤ C_comb * RWRS.combI B (RWRS.combLen B α) e n w n
              * (RWRS.combLen B α n : ℝ) ^ 2) ∧
      (∀ (e : Bool) (n : ℕ) (w : List (Fin B)), w.length = n → 1 ≤ n →
        ∀ (a : List (Fin B) × ℕ → ℝ) (b : ℝ), 0 ≤ b →
          (∀ u ∈ RWRS.combSet B (RWRS.combLen B α) n w, -b ≤ a u) →
          ∀ v ∈ RWRS.combFirstHalf B (RWRS.combLen B α) n w,
            (2 + 2 * b * (C_comb + 1)) * (RWRS.combLen B α n : ℝ) - b ≤ a v →
            RWRS.combI B (RWRS.combLen B α) e n w n * (RWRS.combLen B α n : ℝ) ^ 2
              ≤ ∑' u : ↥(RWRS.combSet B (RWRS.combLen B α) n w),
                  RWRS.combVoltage B (RWRS.combLen B α) e n w u * a u)) ∧
    (∀ (e : Bool) (n : ℕ) (w : List (Fin B)), w.length = n → 1 ≤ n →
      RWRS.combLambda B α ^ n / 4
        ≤ RWRS.combI B (RWRS.combLen B α) e n w n * (RWRS.combLen B α n : ℝ) ^ 2)
-- FROZEN-STATEMENT-END
:= by
  classical
  have hB := hcond.1
  have hL2 : ∀ j, 1 ≤ j → 2 ≤ RWRS.combLen B α j :=
    fun j hj => RWRS.Support.two_le_combLen hcond hj
  have hLstep : ∀ j, 1 ≤ j →
      (RWRS.combLen B α (j + 1) : ℝ) ≤ ((B : ℝ) - 1) * (RWRS.combLen B α j : ℝ) :=
    fun j hj => RWRS.Support.combLen_succ_le_mul hcond hj
  have hLone := RWRS.Support.two_combLen_one_le hcond
  have htsum : ∀ (e : Bool) (n : ℕ) (w : List (Fin B)) (f : List (Fin B) × ℕ → ℝ),
      (∑' u : ↥(RWRS.combSet B (RWRS.combLen B α) n w), f u)
        = ∑ u ∈ RWRS.Support.combFinset B (RWRS.combLen B α) n w, f u := by
    intro e n w f
    rw [← RWRS.Support.coe_combFinset (B := B) (L := RWRS.combLen B α) n w]
    exact Finset.tsum_subtype' _ f
  refine ⟨?_, ?_, ⟨RWRS.Support.combConst B α, RWRS.Support.combConst_pos hcond, ?_, ?_⟩, ?_⟩
  · intro e n w hwn hn j hj
    have hjn : j < n := by omega
    exact ⟨RWRS.Support.combR_le hB hL2 hLstep e hwn hn hjn,
      RWRS.Support.combV_le_two_mul hB hL2 hLstep e hwn hn hjn⟩
  · intro e n w hwn hn
    refine ⟨RWRS.Support.combI_one_ge hB hL2 hLstep hLone e hwn hn, ?_, ?_⟩
    · intro j hj hjn
      exact RWRS.Support.combI_step_ge hB hL2 hLstep e hwn hn hj (by omega)
    · have hpos : (0 : ℝ) < 4 * (B : ℝ) := by
        have : (2 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
        linarith
      have hrpow : (4 * (B : ℝ)) ^ (-(n : ℝ)) = ((4 * (B : ℝ)) ^ n)⁻¹ := by
        rw [Real.rpow_neg hpos.le, Real.rpow_natCast]
      rw [hrpow]
      exact RWRS.Support.combI_ge_pow hB hL2 hLstep hLone e hwn hn n hn le_rfl
  · intro e n w hwn hn
    rw [htsum e n w (fun u => RWRS.combVoltage B (RWRS.combLen B α) e n w u)]
    exact RWRS.Support.comb_mass_const hcond e hwn hn
  · intro e n w hwn hn a b hb ha v hv hav
    rw [htsum e n w (fun u => RWRS.combVoltage B (RWRS.combLen B α) e n w u * a u)]
    exact RWRS.Support.comb_spike hB hL2 e hwn hn (RWRS.Support.combConst_pos hcond)
      (RWRS.Support.comb_mass_const hcond e hwn hn)
      a hb ha hv hav
  · intro e n w hwn hn
    exact RWRS.Support.comb_growth hcond e hwn hn
