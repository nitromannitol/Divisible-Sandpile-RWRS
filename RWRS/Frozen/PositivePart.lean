/-
Lemma 5.3 of `rwrs.tex`, frozen.  `rwrs.tex:600-605` (label
`lem:positive-part`):

  "Let $(Z_i)_{i\in I}$ be a finite collection of independent mean-zero random
   variables with $|Z_i|\leq b_i$ a.s. for deterministic $b_i>0$.  Let
   $B^2\coloneqq\sum_{i\in I}\var(Z_i)$.  If $\max_i b_i^2\leq B^2$, then there
   exists a universal constant $c_\star>0$ such that
   $\E[(\sum_{i\in I}Z_i)^+]\geq c_\star B$."

The constant is universal, so it is bound before the probability space, the
index set, and the variables.  `B` is the nonnegative square root of the sum of
the variances, which is how the paper's `B^2` and `B` are used.
-/
import RWRS.Support.PositivePart

open MeasureTheory ProbabilityTheory

-- FROZEN-STATEMENT-BEGIN
theorem RWRS.Frozen.positivePart :
    ∃ cstar : ℝ, 0 < cstar ∧
      ∀ {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι] (P : Measure Ω),
        IsProbabilityMeasure P → ∀ (Z : ι → Ω → ℝ) (b : ι → ℝ),
        (∀ i, 0 < b i) → ProbabilityTheory.iIndepFun Z P →
        (∀ i, Integrable (Z i) P) → (∀ i, ∫ ω, Z i ω ∂P = 0) →
        (∀ i, ∀ᵐ ω ∂P, |Z i ω| ≤ b i) →
        ∀ B : ℝ, 0 ≤ B → B ^ 2 = ∑ i, ProbabilityTheory.variance (Z i) P →
        (∀ i, b i ^ 2 ≤ B ^ 2) →
        cstar * B ≤ ∫ ω, max (∑ i, Z i ω) 0 ∂P
-- FROZEN-STATEMENT-END
:= by
  obtain ⟨cstar, hcstar, h⟩ := RWRS.Support.exists_positivePart
  refine ⟨cstar, hcstar, ?_⟩
  intro Ω ι _ _ P hP
  exact h P hP
