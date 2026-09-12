import RWRS.External.HeatKernelBoundedDegree
import RWRS.Support.LibraryBridge
import LatticeProb.Graph.OnDiagonal

-- FROZEN-STATEMENT-BEGIN
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
