/-
Cited input: on an infinite locally finite connected graph the `n`-step
return probability tends to zero, quoted in `rwrs.tex:319-322` and again in the
proof of `lem:clock-no-dom` from Lyons and Peres, *Probability on Trees and
Networks*, Exercise 2.1(f).

Proved here on every infinite connected graph (`heatKernelVanishing_of_connected`)
and hence on every good rooted network (`heatKernelVanishing_of_netGood`); no
hypothesis of any frozen statement carries it any longer.
-/
import RWRS.Setting
import RWRS.Network
import RWRS.Support.LibraryBridge
import LatticeProb.Graph.HeatVanishing

open Filter Topology

-- FROZEN-STATEMENT-BEGIN
/-- "Since $\P_\rho(X_n=v)\to0$ for each $v$ on infinite graphs." -/
def RWRS.External.HeatKernelVanishing {V : Type*} (G : SimpleGraph V) [G.LocallyFinite] :
    Prop :=
  ∀ x v : V, Tendsto (fun n : ℕ => RWRS.heat G n x v) atTop (𝓝 0)

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
