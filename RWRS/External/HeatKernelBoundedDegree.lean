/-
Cited input: the universal heat kernel bound on a bounded-degree graph,
`sup_x P_x(X_n = x) ≤ C n^{-1/2}`, quoted in `rwrs.tex:144-149` from
Grigor'yan, *Introduction to Analysis on Graphs*, Example 5.14.  It is what
supplies the spectral dimension hypothesis of `prop:subcritical` with
`d_s = 1` on every infinite connected graph of bounded degree.

Proved here on every infinite connected graph (`heatKernelBoundedDegree_of_connected`,
via the shared library's Nash-inequality machinery); no hypothesis of any
frozen statement carries it any longer.
-/
import RWRS.Setting
import RWRS.Support.LibraryBridge
import LatticeProb.Graph.OnDiagonal

-- FROZEN-STATEMENT-BEGIN
/-- Example 5.14 of the cited notes, as `rwrs.tex` quotes it: on graphs of
degree bounded by `d` the return probability after `n` steps is at most a
constant times `n^{-1/2}`, uniformly in the vertex and in the graph. -/
def RWRS.External.HeatKernelBoundedDegree {V : Type*} (G : SimpleGraph V)
    [G.LocallyFinite] : Prop :=
  ∀ d : ℕ, 1 ≤ d → RWRS.BoundedDegree G d → ∃ A : ℝ, 0 < A ∧
    RWRS.SpectralDimensionBound G 1 A

/-- Spectral dimension one on an infinite connected graph of bounded degree.
Cited in `rwrs.tex:144-149`; proved by the shared library. -/
theorem RWRS.External.heatKernelBoundedDegree_of_connected {V : Type*}
    {G : SimpleGraph V} [G.LocallyFinite] [Infinite V] (hG : G.Connected) :
    RWRS.External.HeatKernelBoundedDegree G
-- FROZEN-STATEMENT-END
:= by
  intro d hd1 hd
  obtain ⟨A, hA, hsp⟩ :=
    LatticeProb.Graph.spectralDimensionBound_of_boundedDegree hG hd1 (fun v => hd v)
  refine ⟨A, hA, fun x n hn => ?_⟩
  rw [RWRS.Support.heat_eq_lib]
  exact hsp x n hn
