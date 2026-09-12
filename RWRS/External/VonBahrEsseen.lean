/-
External input: the von Bahr--Esseen inequality, cited in the proof of
`lem:fuk-nagaev` (`rwrs.tex:1096-1098`) as the source of part (a) of that
lemma.  Assumed here; it enters only as an explicit hypothesis of the result
whose proof uses it.
-/
import RWRS.Setting
import Mathlib.Probability.Independence.Basic

open MeasureTheory

-- FROZEN-STATEMENT-BEGIN
/-- "If $p\in[1,2]$, then for all $t>0$,
$\P(|\sum_{i\in I}Y_i|\geq t)\leq C_pM_p/t^p$.  Here $C_p<\infty$ depends only
on $p$." -/
def RWRS.External.VonBahrEsseen : Prop :=
  ∀ p : ℝ, 1 ≤ p → p ≤ 2 → ∃ Cp : ℝ, 0 < Cp ∧
    ∀ {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι] (P : Measure Ω), IsProbabilityMeasure P →
      ∀ (Y : ι → Ω → ℝ), ProbabilityTheory.iIndepFun Y P → (∀ i, Integrable (Y i) P) →
      (∀ i, ∫ ω, Y i ω ∂P = 0) →
      ∀ Mp : ℝ, Mp = ∑ i, (∫⁻ ω, ENNReal.ofReal (|Y i ω| ^ p) ∂P).toReal →
        (∀ i, (∫⁻ ω, ENNReal.ofReal (|Y i ω| ^ p) ∂P) ≠ ⊤) →
        ∀ t : ℝ, 0 < t →
          P {ω | t ≤ |∑ i, Y i ω|} ≤ ENNReal.ofReal (Cp * Mp / t ^ p)
-- FROZEN-STATEMENT-END
