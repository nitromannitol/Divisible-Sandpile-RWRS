/-
The voltage function of `prop:01-law` is a theorem, not an assumption, on a
doubly transient graph.

On a transient graph the Green mass supplies it with no hitting probabilities.
Writing `u_a(x) = ∑_k p_k(x,a)` for the expected total local time at `a` of the
walk started at `x`, the one-step recursion summed over `k` gives
`∑_{y ∼ x} u_a(y) = deg(x)(u_a(x) - p_0(x,a))`, that is `Δu_a = -deg(·) δ_a`, so
`u_a/deg(a) - u_b/deg(b)` has Laplacian `δ_b - δ_a`.  It is bounded because
`u_a(x) ≤ u_a(a)`, and adding the constant `u_b(b)/deg(b)`, which the Laplacian
does not see, makes it nonnegative.  Neither the hitting-probability formula of
the paper nor the reciprocity relation behind it is needed.

The frozen `Prop` `RWRS.External.VoltageFunction` and every statement carrying it
remain as stated; this file supplies a witness on transient graphs.
-/
import RWRS.External.VoltageFunction
import RWRS.Support.LibraryBridge
import LatticeProb.Network.Voltage

namespace RWRS.Support

open scoped ENNReal

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

/-- The Green function of this repository is the shared library's. -/
theorem green_eq_lib (x v : V) : green G x v = LatticeProb.Graph.green G x v := by
  simp only [RWRS.green, LatticeProb.Graph.green, heat_eq_lib]

/-- Double transience here is double transience in the shared library. -/
theorem doublyTransient_lib (hdt : RWRS.DoublyTransient G) :
    LatticeProb.Graph.DoublyTransient G := by
  intro o
  have := hdt o
  simpa only [green_eq_lib] using this

end RWRS.Support

-- FROZEN-STATEMENT-BEGIN
/-- The bounded nonnegative function with Laplacian `δ_b - δ_a` quoted in the
proof of `prop:01-law` (`rwrs.tex:513-520`), on a transient graph.  Proved. -/
theorem RWRS.External.voltageFunction {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]
    [Infinite V] (hG : G.Connected) (htrans : ∀ o : V, RWRS.green G o o ≠ ⊤) :
    RWRS.External.VoltageFunction G
-- FROZEN-STATEMENT-END
:= by
  intro a b hab
  refine LatticeProb.Network.exists_voltage_of_green_ne_top hG hab ?_ ?_
  · simpa only [RWRS.Support.green_eq_lib] using htrans a
  · simpa only [RWRS.Support.green_eq_lib] using htrans b

/-- The same on a doubly transient graph, where transience is automatic. -/
theorem RWRS.External.voltageFunction_of_doublyTransient {V : Type*} {G : SimpleGraph V}
    [G.LocallyFinite] [Infinite V] (hG : G.Connected) (hdt : RWRS.DoublyTransient G) :
    RWRS.External.VoltageFunction G := by
  intro a b hab
  exact LatticeProb.Network.exists_voltage_of_doublyTransient hG
    (RWRS.Support.doublyTransient_lib hdt) hab
