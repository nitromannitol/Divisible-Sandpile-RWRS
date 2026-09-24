import RWRS.External.HeatKernelVanishing
import RWRS.Network
import RWRS.Support.LibraryBridge
import LatticeProb.Graph.HeatVanishing

-- FROZEN-STATEMENT-BEGIN
/-- Transition probabilities tend to zero on an infinite connected graph.
Cited in `rwrs.tex:319-322`; proved by the shared library. -/
theorem RWRS.External.heatKernelVanishing_of_connected {V : Type*}
    {G : SimpleGraph V} [G.LocallyFinite] [Infinite V] (hG : G.Connected) :
    RWRS.External.HeatKernelVanishing G
-- FROZEN-STATEMENT-END
:= by
  intro x v
  have h := LatticeProb.Graph.heat_tendsto_zero hG x v
  refine h.congr fun n => ?_
  rw [RWRS.Support.heat_eq_lib]

/-- Heat kernel vanishing for connected rooted networks. -/
theorem RWRS.External.heatKernelVanishing_of_netGood {m : ℕ} :
    ∀ N : RWRS.Net m, RWRS.NetGood N →
      RWRS.External.HeatKernelVanishing (RWRS.netGraph N) := by
  intro N hN
  exact RWRS.External.heatKernelVanishing_of_connected hN
