/-
Cited input: Bernstein's inequality, cited in the proof of `lem:fuk-nagaev`
(`rwrs.tex:1096-1098`) as the source of part (c) of that lemma.  Proved
outright by the shared library; no hypothesis of any frozen statement carries
it any longer.

The only analytic step is the moment generating function bound: for a centred
variable with `|X| ≤ M`, the pointwise `e^u ≤ 1 + u + u²/(2(1-θ))` valid when
`|u| ≤ 3θ < 3`, which compares the tail `∑_{k≥2} u^k/k!` with a geometric series
through `k! ≥ 2·3^{k-2}`.  Independence then turns the moment generating function
of the sum into a product, and Chernoff's bound at `λ = t/(B² + Mt/3)`, where
`1 - λM/3 = B²/(B² + Mt/3)`, collapses the exponent to `-t²/(2(B² + Mt/3))`.
-/
import RWRS.Setting
import Mathlib.Probability.Independence.Basic
import LatticeProb.Prob.Bernstein

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

/-- Bernstein's inequality for bounded independent centred summands, cited in
`rwrs.tex:1096-1098` for part (c) of `lem:fuk-nagaev`.  Proved. -/
theorem RWRS.External.bernstein : RWRS.External.Bernstein
-- FROZEN-STATEMENT-END
:= by
  intro Ω ι _ _ P hP Y hindep hint hmean M B hM hB hb hB2 hsq t ht
  haveI := hP
  exact LatticeProb.bernstein P Y hindep hint hmean M B hM hB hb hB2 hsq t ht
