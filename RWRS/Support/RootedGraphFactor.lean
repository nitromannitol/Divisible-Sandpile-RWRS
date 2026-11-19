import RWRS.Support.NetGoodInvariant
import RWRS.Support.RootedBallIsomorphism

/-!
# Rooted graph ball sequences

The sequence of finite ball types is a measurable isomorphism invariant.
-/

namespace RWRS.Support

open MeasureTheory

/-- The sequence of rooted finite-ball types of a network. -/
noncomputable def netBallTypes {m : ℕ} (N : Net m) : ℕ → ℕ :=
  fun r => netBallType N r

/-- The sequence of rooted finite-ball types is measurable. -/
theorem measurable_netBallTypes {m : ℕ} : Measurable (netBallTypes : Net m → ℕ → ℕ) := by
  exact measurable_pi_lambda _ fun r => measurable_netBallType r

/-- Rooted isomorphic networks have identical sequences of finite-ball types. -/
theorem netBallTypes_eq_of_netIso {m : ℕ} {N N' : Net m} (h : NetIso N N') :
    netBallTypes N = netBallTypes N' := by
  funext r
  exact netBallType_eq_of_netIso h r

end RWRS.Support
