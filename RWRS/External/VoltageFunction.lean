/-
External input: the bounded function with Laplacian `δ_b - δ_a`, quoted in the
proof of `prop:01-law` (`rwrs.tex:513-520`) from Lyons and Peres, *Probability
on Trees and Networks*, Proposition 2.1 and equation (2.4).

Assumed here.  It enters only as an explicit hypothesis of the results whose
proofs use it.
-/
import RWRS.Setting

open scoped Classical

-- FROZEN-STATEMENT-BEGIN
/-- "The function $f(x)=\P_x(T_a<T_b)/(\deg(a)\P_a(T_b<T_a^+))$ satisfies
$0\leq f\leq\|f\|_\infty<\infty$ and $\Delta f=\delta_b-\delta_a$." -/
def RWRS.External.VoltageFunction {V : Type*} (G : SimpleGraph V) [G.LocallyFinite] : Prop :=
  ∀ a b : V, a ≠ b → ∃ f : V → ℝ, ∃ M : ℝ, 0 < M ∧ (∀ x, 0 ≤ f x ∧ f x ≤ M) ∧
    ∀ x : V, RWRS.laplacian G f x = (if x = b then (1 : ℝ) else 0) - (if x = a then 1 else 0)
-- FROZEN-STATEMENT-END
