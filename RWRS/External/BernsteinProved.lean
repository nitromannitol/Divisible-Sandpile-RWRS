/-
Bernstein's inequality, quoted in `lem:fuk-nagaev`, is a theorem of the shared
library rather than an assumption.

The only analytic step is the moment generating function bound: for a centred
variable with `|X| ≤ M`, the pointwise `e^u ≤ 1 + u + u²/(2(1-θ))` valid when
`|u| ≤ 3θ < 3`, which compares the tail `∑_{k≥2} u^k/k!` with a geometric series
through `k! ≥ 2·3^{k-2}`.  Independence then turns the moment generating function
of the sum into a product, and Chernoff's bound at `λ = t/(B² + Mt/3)`, where
`1 - λM/3 = B²/(B² + Mt/3)`, collapses the exponent to `-t²/(2(B² + Mt/3))`.

The frozen `Prop` `RWRS.External.Bernstein` and every statement carrying it are
unchanged; this file supplies the witness.
-/
import RWRS.External.Bernstein
import LatticeProb.Prob.Bernstein

open MeasureTheory

-- FROZEN-STATEMENT-BEGIN
/-- Bernstein's inequality for bounded independent centred summands, cited in
`rwrs.tex:1096-1098` for part (c) of `lem:fuk-nagaev`.  Proved. -/
theorem RWRS.External.bernstein : RWRS.External.Bernstein
-- FROZEN-STATEMENT-END
:= by
  intro Ω ι _ _ P hP Y hindep hint hmean M B hM hB hb hB2 hsq t ht
  haveI := hP
  exact LatticeProb.bernstein P Y hindep hint hmean M B hM hB hb hB2 hsq t ht
