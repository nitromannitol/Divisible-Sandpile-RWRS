/-
External input: the universal heat kernel bound on a bounded-degree graph,
`sup_x P_x(X_n = x) ≤ C n^{-1/2}`, quoted in `rwrs.tex:144-149` from
Grigor'yan, *Introduction to Analysis on Graphs*, Example 5.14.  It is what
supplies the spectral dimension hypothesis of `prop:subcritical` with
`d_s = 1` on every infinite connected graph of bounded degree.

Assumed here.  It enters only as an explicit hypothesis of the results whose
proofs use it.
-/
import RWRS.Setting

-- FROZEN-STATEMENT-BEGIN
/-- Example 5.14 of the cited notes, as `rwrs.tex` quotes it: on graphs of
degree bounded by `d` the return probability after `n` steps is at most a
constant times `n^{-1/2}`, uniformly in the vertex and in the graph. -/
def RWRS.External.HeatKernelBoundedDegree {V : Type*} (G : SimpleGraph V)
    [G.LocallyFinite] : Prop :=
  ∀ d : ℕ, 1 ≤ d → RWRS.BoundedDegree G d → ∃ A : ℝ, 0 < A ∧
    RWRS.SpectralDimensionBound G 1 A
-- FROZEN-STATEMENT-END
