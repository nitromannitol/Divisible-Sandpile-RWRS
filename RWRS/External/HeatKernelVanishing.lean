/-
External input: on an infinite locally finite connected graph the `n`-step
return probability tends to zero, quoted in `rwrs.tex:319-322` and again in the
proof of `lem:clock-no-dom` from Lyons and Peres, *Probability on Trees and
Networks*, Exercise 2.1(f).

Assumed here.  It enters only as an explicit hypothesis of the results whose
proofs use it.
-/
import RWRS.Setting

open Filter Topology

-- FROZEN-STATEMENT-BEGIN
/-- "Since $\P_\rho(X_n=v)\to0$ for each $v$ on infinite graphs." -/
def RWRS.External.HeatKernelVanishing {V : Type*} (G : SimpleGraph V) [G.LocallyFinite] :
    Prop :=
  ∀ x v : V, Tendsto (fun n : ℕ => RWRS.heat G n x v) atTop (𝓝 0)
-- FROZEN-STATEMENT-END
