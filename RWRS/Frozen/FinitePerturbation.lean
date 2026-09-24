/-
Lemma 6.3 of `rwrs.tex`, frozen.  `rwrs.tex:1453-1456` (label
`ex:finite-perturbation`):

  "Let $G=(V,E)$ be an infinite, locally finite, and connected graph, and fix
   $o\in V$.  For $m>0$ consider the configuration
   $\sigma(v)=1+m\one_{\{v=o\}}$.  Then for every $x\in V$ and $n\geq0$, we
   have $u_n(x)=mg_n(x,o)$, and hence $u_\infty(x)=mg(x,o)\in[0,\infty]$.  In
   particular, $\sigma$ stabilizes if and only if the random walk on $G$ is
   transient.  If the walk is recurrent, then $\sigma$ explodes."

`u_∞(x)` and `g(x,o)` are both `[0,∞]`-valued, so the identity is exact and
carries the case `g(x,o) = ∞`.  Recurrence is `g(o,o) = ∞`.
-/
import RWRS.Support.HeatBasic

open scoped ENNReal

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

-- FROZEN-STATEMENT-BEGIN
theorem RWRS.Frozen.finitePerturbation [Infinite V] (hG : G.Connected) (o : V) (m : ℝ)
    (hm : 0 < m) :
    (∀ (x : V) (n : ℕ), RWRS.odometer G (RWRS.spikeConfig o m) n x
        = m * RWRS.greenTime G n x o) ∧
    (∀ x : V, RWRS.odometerLimit G (RWRS.spikeConfig o m) x
        = ENNReal.ofReal m * RWRS.green G x o) ∧
    (RWRS.Stabilizes G (RWRS.spikeConfig o m) ↔ ¬ RWRS.Recurrent G o)
-- FROZEN-STATEMENT-END
:= by
  classical
  have hdo : (0 : ℝ) < (G.degree o : ℝ) := Nat.cast_pos.mpr (RWRS.Support.degree_pos hG o)
  have hf : (fun v => RWRS.excess (RWRS.spikeConfig o m) v / (G.degree v : ℝ))
      = fun v => if v = o then m / (G.degree o : ℝ) else 0 := by
    funext v
    by_cases h : v = o
    · subst h; simp [RWRS.excess, RWRS.spikeConfig]
    · simp [RWRS.excess, RWRS.spikeConfig, h]
  have hpos : ∀ v : V, 0 ≤ RWRS.excess (RWRS.spikeConfig o m) v / (G.degree v : ℝ) := by
    intro v
    rw [congrFun hf v]
    split_ifs
    · exact div_nonneg hm.le hdo.le
    · exact le_rfl
  have hpart1 : ∀ (x : V) (n : ℕ),
      RWRS.odometer G (RWRS.spikeConfig o m) n x = m * RWRS.greenTime G n x o := by
    intro x n
    rw [RWRS.Support.odometer_eq_payoff hG _ hpos, RWRS.Support.walkExp_payoff_eq hG, hf]
    simp only [RWRS.Support.walkOp_iterate_single]
    rw [← Finset.sum_mul, RWRS.greenTime, RWRS.meanLocalTime]
    field_simp
  have hgreen : ∀ x : V, RWRS.odometerLimit G (RWRS.spikeConfig o m) x
      = ENNReal.ofReal m * RWRS.green G x o := by
    intro x
    have hstep : ∀ n : ℕ, ENNReal.ofReal (RWRS.odometer G (RWRS.spikeConfig o m) n x)
        = ENNReal.ofReal m
            * (∑ k ∈ Finset.range n, ENNReal.ofReal (RWRS.heat G k x o))
            / (G.degree o : ℝ≥0∞) := by
      intro n
      rw [hpart1 x n, RWRS.greenTime, RWRS.meanLocalTime,
        show m * ((∑ k ∈ Finset.range n, RWRS.heat G k x o) / (G.degree o : ℝ))
          = m * (∑ k ∈ Finset.range n, RWRS.heat G k x o) / (G.degree o : ℝ) from by ring,
        ENNReal.ofReal_div_of_pos hdo, ENNReal.ofReal_mul hm.le,
        ENNReal.ofReal_sum_of_nonneg (fun k _ => RWRS.Support.heat_nonneg k x o)]
      congr 1
      simp
    rw [RWRS.odometerLimit]
    simp only [hstep]
    rw [← ENNReal.iSup_div, ← ENNReal.mul_iSup, ← ENNReal.tsum_eq_iSup_nat,
      RWRS.Support.green_eq_div, mul_div_assoc]
  refine ⟨hpart1, hgreen, ?_⟩
  have hmne : ENNReal.ofReal m ≠ 0 := by simpa using hm
  have hmt : ENNReal.ofReal m ≠ ⊤ := ENNReal.ofReal_ne_top
  constructor
  · intro hst hrec
    have hv := hst o
    rw [hgreen o] at hv
    have htop : RWRS.green G o o = ⊤ := hrec
    exact hv (by rw [htop, ENNReal.mul_top hmne])
  · intro hrec v
    rw [hgreen v]
    refine ENNReal.mul_ne_top hmt ?_
    rw [RWRS.Support.green_ne_top_iff hG]
    exact RWRS.Support.green_ne_top_transfer hG
      ((RWRS.Support.green_ne_top_iff hG o o).mp hrec) v
