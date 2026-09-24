/-
External input: Bernstein's inequality, cited in the proof of `lem:fuk-nagaev`
(`rwrs.tex:1096-1098`) as the source of part (c) of that lemma.  Assumed here;
it enters only as an explicit hypothesis of the result whose proof uses it.
-/
import RWRS.Setting
import Mathlib.Probability.Independence.Basic

open MeasureTheory

-- FROZEN-STATEMENT-BEGIN
/-- "If $|Y_i|\leq M$ a.s. for each $i$ and $B^2\coloneqq\sum_i\E[Y_i^2]<\infty$,
then for all $t>0$,
$\P(|\sum_iY_i|\geq t)\leq2\exp(-\frac{t^2/2}{B^2+Mt/3})$." -/
def RWRS.External.Bernstein : Prop :=
  ∀ {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι] (P : Measure Ω), IsProbabilityMeasure P →
    ∀ (Y : ι → Ω → ℝ), ProbabilityTheory.iIndepFun Y P → (∀ i, Integrable (Y i) P) →
    (∀ i, ∫ ω, Y i ω ∂P = 0) →
    ∀ M B : ℝ, 0 < M → 0 < B → (∀ i, ∀ᵐ ω ∂P, |Y i ω| ≤ M) →
      B ^ 2 = ∑ i, ∫ ω, Y i ω ^ 2 ∂P → (∀ i, Integrable (fun ω => Y i ω ^ 2) P) →
      ∀ t : ℝ, 0 < t →
        P {ω | t ≤ |∑ i, Y i ω|}
          ≤ ENNReal.ofReal (2 * Real.exp (-(t ^ 2 / 2) / (B ^ 2 + M * t / 3)))
-- FROZEN-STATEMENT-END
