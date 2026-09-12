/-
Lemma 5.13 of `rwrs.tex`, frozen.  `rwrs.tex:1077-1095` (label
`lem:fuk-nagaev`):

  "Let $(Y_i)_{i\in I}$ be a finite collection of independent mean-zero random
   variables with $M_p\coloneqq\sum_{i\in I}\E[|Y_i|^p]<\infty$ for some
   $p\geq1$.
   (a) (Polynomial tail, $p\in[1,2]$) If $p\in[1,2]$, then for all $t>0$,
   $\P(|\sum_i Y_i|\geq t)\leq C_p M_p/t^p$.  Here $C_p<\infty$ depends only
   on $p$.
   (b) (Polynomial $+$ Gaussian tail) If $p\geq2$ and
   $B^2\coloneqq\sum_i\E[Y_i^2]<\infty$, then for all $t>0$,
   $\P(|\sum_i Y_i|\geq t)\leq C_p M_p/t^p+2\exp(-ct^2/B^2)$.  Here $c>0$ and
   $C_p<\infty$ depend only on $p$.
   (c) (Bernstein) If $|Y_i|\leq M$ a.s. for each $i$ and
   $B^2\coloneqq\sum_i\E[Y_i^2]<\infty$, then for all $t>0$,
   $\P(|\sum_i Y_i|\geq t)\leq 2\exp(-\frac{t^2/2}{B^2+Mt/3})$."

The constants of (a) and (b) depend only on `p`, so they are bound before the
probability space, the index set and the variables; the constants of (c) are
explicit.  Probabilities are compared in `[0,∞]`.  The paper proves the lemma by
citation, so the three parts are the three cited results, taken here as explicit
hypotheses.
-/
import RWRS.External.VonBahrEsseen
import RWRS.External.FukNagaevTail
import RWRS.External.Bernstein

open MeasureTheory
open scoped ENNReal

-- FROZEN-STATEMENT-BEGIN
theorem RWRS.Frozen.fukNagaev (hVBE : RWRS.External.VonBahrEsseen)
    (hFN : RWRS.External.FukNagaevTail) (hBer : RWRS.External.Bernstein) :
    (∀ p : ℝ, 1 ≤ p → p ≤ 2 → ∃ Cp : ℝ, 0 < Cp ∧
      ∀ {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι] (P : Measure Ω), IsProbabilityMeasure P →
        ∀ (Y : ι → Ω → ℝ), ProbabilityTheory.iIndepFun Y P → (∀ i, Integrable (Y i) P) →
        (∀ i, ∫ ω, Y i ω ∂P = 0) →
        ∀ Mp : ℝ, Mp = ∑ i, (∫⁻ ω, ENNReal.ofReal (|Y i ω| ^ p) ∂P).toReal →
          (∀ i, (∫⁻ ω, ENNReal.ofReal (|Y i ω| ^ p) ∂P) ≠ ⊤) →
          ∀ t : ℝ, 0 < t →
            P {ω | t ≤ |∑ i, Y i ω|} ≤ ENNReal.ofReal (Cp * Mp / t ^ p)) ∧
    (∀ p : ℝ, 2 ≤ p → ∃ c Cp : ℝ, 0 < c ∧ 0 < Cp ∧
      ∀ {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι] (P : Measure Ω), IsProbabilityMeasure P →
        ∀ (Y : ι → Ω → ℝ), ProbabilityTheory.iIndepFun Y P → (∀ i, Integrable (Y i) P) →
        (∀ i, ∫ ω, Y i ω ∂P = 0) →
        ∀ Mp B : ℝ, Mp = ∑ i, (∫⁻ ω, ENNReal.ofReal (|Y i ω| ^ p) ∂P).toReal →
          (∀ i, (∫⁻ ω, ENNReal.ofReal (|Y i ω| ^ p) ∂P) ≠ ⊤) →
          0 < B → B ^ 2 = ∑ i, ∫ ω, Y i ω ^ 2 ∂P → (∀ i, Integrable (fun ω => Y i ω ^ 2) P) →
          ∀ t : ℝ, 0 < t →
            P {ω | t ≤ |∑ i, Y i ω|}
              ≤ ENNReal.ofReal (Cp * Mp / t ^ p + 2 * Real.exp (-c * t ^ 2 / B ^ 2))) ∧
    (∀ {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι] (P : Measure Ω), IsProbabilityMeasure P →
      ∀ (Y : ι → Ω → ℝ), ProbabilityTheory.iIndepFun Y P → (∀ i, Integrable (Y i) P) →
      (∀ i, ∫ ω, Y i ω ∂P = 0) →
      ∀ M B : ℝ, 0 < M → 0 < B → (∀ i, ∀ᵐ ω ∂P, |Y i ω| ≤ M) →
        B ^ 2 = ∑ i, ∫ ω, Y i ω ^ 2 ∂P → (∀ i, Integrable (fun ω => Y i ω ^ 2) P) →
        ∀ t : ℝ, 0 < t →
          P {ω | t ≤ |∑ i, Y i ω|}
            ≤ ENNReal.ofReal (2 * Real.exp (-(t ^ 2 / 2) / (B ^ 2 + M * t / 3))))
-- FROZEN-STATEMENT-END
:= ⟨hVBE, hFN, hBer⟩
