/-
The arithmetic core of the final combination in Step 1 of
`prop:doubly-transient-really-general`: the conditional bound
`E[h(Y_{J_m}) | X] ≤ (-8m + B₀)(1-e^{-1}) + B₀ e^{-1}` reorganizes as
`-8m(1-e^{-1}) + B₀`, which is what makes the expected payoff grow linearly
in `m`.
-/
import RWRS.Support.DTAdmissible

open scoped ENNReal

/-- The combination identity of `rwrs.tex:938` (`eq:payoff-identity` chain). -/
theorem step1_combination_arithmetic (m : ℕ) (B₀ : ℝ) :
    (-8 * m + B₀) * (1 - Real.exp (-1)) + B₀ * Real.exp (-1)
      = -8 * m * (1 - Real.exp (-1)) + B₀ := by
  ring
