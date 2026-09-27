import RWRS.Setting

/-!
# The voltage function, as an external input

External input: the bounded function with Laplacian `δ_b - δ_a`, quoted in the
proof of `prop:01-law` (`rwrs.tex:513-520`) from Lyons and Peres, *Probability
on Trees and Networks*, Proposition 2.1 and equation (2.4).

Proved on every infinite connected graph by
`RWRS.External.voltageFunction_of_connected` in
`RWRS/External/VoltageFunctionConnected.lean` (node `X-008`).
-/

open scoped Classical

-- Proved by `RWRS.External.voltageFunction_of_connected` in
-- `RWRS/External/VoltageFunctionConnected.lean` (node `X-008`) on every infinite
-- connected graph, the standing hypothesis of the paper.
/-- "The function $f(x)=\P_x(T_a<T_b)/(\deg(a)\P_a(T_b<T_a^+))$ satisfies
$0\leq f\leq\|f\|_\infty<\infty$ and $\Delta f=\delta_b-\delta_a$." -/
def RWRS.External.VoltageFunction {V : Type*} (G : SimpleGraph V) [G.LocallyFinite] : Prop :=
  ∀ a b : V, a ≠ b → ∃ f : V → ℝ, ∃ M : ℝ, 0 < M ∧ (∀ x, 0 ≤ f x ∧ f x ≤ M) ∧
    ∀ x : V, RWRS.laplacian G f x = (if x = b then (1 : ℝ) else 0) - (if x = a then 1 else 0)
