import RWRS.External.VoltageFunction
import LatticeProb.Network.VoltageConnected

/-!
# The voltage function exists on every infinite connected graph

The voltage function of `prop:01-law` is a theorem, not an assumption, on every
infinite connected locally finite graph, recurrent or transient.

This is the standing hypothesis of the paper (`rwrs.tex:191`).  The proof is in the
shared library, `LatticeProb.Network.exists_voltage_of_connected`: the dipole
potentials of the Green functions killed off finite sets have Laplacian
`δ_b - δ_a` inside the set, stay in a fixed box by the maximum principle and
Kirchhoff's node law, and a cluster point along the exhaustion by finite sets is
the voltage function.  No transience is needed, so this covers the recurrent
branch of `prop:01-law`, which the Green-function witness of
`RWRS/External/VoltageFunctionProved.lean` does not reach.
-/

-- FROZEN-STATEMENT-BEGIN
/-- The bounded nonnegative function with Laplacian `δ_b - δ_a` quoted in the
proof of `prop:01-law` (`rwrs.tex:513-520`; Lyons and Peres, *Probability on
Trees and Networks*, Proposition 2.1 and equation (2.4)), on every infinite
connected graph.  Proved. -/
theorem RWRS.External.voltageFunction_of_connected {V : Type*} {G : SimpleGraph V}
    [G.LocallyFinite] [Infinite V] (hG : G.Connected) :
    RWRS.External.VoltageFunction G
-- FROZEN-STATEMENT-END
:= by
  intro a b hab
  exact LatticeProb.Network.exists_voltage_of_connected hG hab
