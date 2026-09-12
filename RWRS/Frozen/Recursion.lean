/-
Lemma 3.1 of `rwrs.tex`, frozen.  `rwrs.tex:377-381` (label `lem:recursion`):

  "For all $n \geq 0$ and $x \in V$,
   $u_{n+1}(x) = \bigl(\frac{1}{\deg(x)}\sum_{y \sim x} u_n(y) + \zeta(x)\bigr)^+$."

`hG` is the standing assumption of Section 3 (`rwrs.tex:373-375`: "we fix a
locally finite connected graph $G=(V,E)$ and an initial configuration
$\sigma\colon V\to\R$"), and `[Infinite V]` is the standing assumption of
`ssec:notation` ("Throughout, $G=(V,E)$ denotes an infinite, locally finite,
connected graph").  The positive part `(\cdot)^+` is `max \cdot 0`.
-/
import RWRS.Support.Odometer

open RWRS RWRS.Support

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

-- FROZEN-STATEMENT-BEGIN
theorem RWRS.Frozen.recursion [Infinite V] (hG : G.Connected) (σ : V → ℝ) (n : ℕ) (x : V) :
    RWRS.odometer G σ (n + 1) x =
      max (RWRS.walkOp G (RWRS.odometer G σ n) x + RWRS.scenery G σ x) 0
-- FROZEN-STATEMENT-END
:= by
  rw [odometer_succ_max hG]
  have hle := odometer_le_bellman (G := G) hG σ n x
  have hnn := odometer_nonneg (G := G) σ n x
  rcases le_total (0 : ℝ) (walkOp G (odometer G σ n) x + scenery G σ x) with hA | hA
  · rw [max_eq_left hA, max_eq_left (by rw [max_eq_left hA] at hle; exact hle)]
  · rw [max_eq_right hA] at hle
    rw [max_eq_right hA, max_eq_right (by linarith)]
    linarith
