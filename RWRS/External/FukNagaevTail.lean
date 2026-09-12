/-
External input: the Fuk--Nagaev inequality, cited in the proof of
`lem:fuk-nagaev` (`rwrs.tex:1096-1098`) as the source of part (b) of that
lemma.  Assumed here; it enters only as an explicit hypothesis of the result
whose proof uses it.
-/
import RWRS.Setting
import Mathlib.Probability.Independence.Basic

open MeasureTheory

-- FROZEN-STATEMENT-BEGIN
/-- "If $p\geq2$ and $B^2\coloneqq\sum_i\E[Y_i^2]<\infty$, then for all $t>0$,
$\P(|\sum_iY_i|\geq t)\leq C_pM_p/t^p+2\exp(-ct^2/B^2)$.  Here $c>0$ and
$C_p<\infty$ depend only on $p$." -/
def RWRS.External.FukNagaevTail : Prop :=
  ∀ p : ℝ, 2 ≤ p → ∃ c Cp : ℝ, 0 < c ∧ 0 < Cp ∧
    ∀ {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι] (P : Measure Ω), IsProbabilityMeasure P →
      ∀ (Y : ι → Ω → ℝ), ProbabilityTheory.iIndepFun Y P → (∀ i, Integrable (Y i) P) →
      (∀ i, ∫ ω, Y i ω ∂P = 0) →
      ∀ Mp B : ℝ, Mp = ∑ i, (∫⁻ ω, ENNReal.ofReal (|Y i ω| ^ p) ∂P).toReal →
        (∀ i, (∫⁻ ω, ENNReal.ofReal (|Y i ω| ^ p) ∂P) ≠ ⊤) →
        0 < B → B ^ 2 = ∑ i, ∫ ω, Y i ω ^ 2 ∂P → (∀ i, Integrable (fun ω => Y i ω ^ 2) P) →
        ∀ t : ℝ, 0 < t →
          P {ω | t ≤ |∑ i, Y i ω|}
            ≤ ENNReal.ofReal (Cp * Mp / t ^ p + 2 * Real.exp (-c * t ^ 2 / B ^ 2))
-- FROZEN-STATEMENT-END
