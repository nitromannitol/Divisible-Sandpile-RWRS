/-
The value of a bounded stopping rule against the walk average of the running
supremum.

A bounded stopping time is replaced by its minimum with the exit time of the
ball of the same radius, which does not change the walk average of length `n`
and makes the payoff bounded, so the walk average is a Bochner integral against
the law of the walk; the payoff at any time is at most `sup_n S_n`.
-/
import RWRS.Support.BallWalk
import RWRS.Support.SubTrunc

namespace RWRS.Support

open MeasureTheory LatticeProb.Graph
open scoped ENNReal

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

/-- The Bochner integral of a real function is dominated by the lower integral
of its positive part. -/
theorem ofReal_integral_le_lintegral {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {F : Ω → ℝ} (hF : Integrable F μ) :
    ENNReal.ofReal (∫ ω, F ω ∂μ) ≤ ∫⁻ ω, ENNReal.ofReal (F ω) ∂μ := by
  have hpp : Integrable (fun ω => max (F ω) 0) μ := hF.pos_part
  have h1 : ∫ ω, F ω ∂μ ≤ ∫ ω, max (F ω) 0 ∂μ :=
    integral_mono hF hpp fun ω => le_max_left _ _
  have h2 : ENNReal.ofReal (∫ ω, max (F ω) 0 ∂μ) = ∫⁻ ω, ENNReal.ofReal (max (F ω) 0) ∂μ :=
    ofReal_integral_eq_lintegral_ofReal hpp
      (Filter.Eventually.of_forall fun ω => le_max_right _ _)
  have h3 : ∀ ω, ENNReal.ofReal (max (F ω) 0) = ENNReal.ofReal (F ω) := by
    intro ω
    rcases le_or_gt (F ω) 0 with h | h
    · rw [max_eq_right h, ENNReal.ofReal_zero, (ENNReal.ofReal_eq_zero).2 h]
    · rw [max_eq_left h.le]
  calc ENNReal.ofReal (∫ ω, F ω ∂μ)
      ≤ ENNReal.ofReal (∫ ω, max (F ω) 0 ∂μ) := ENNReal.ofReal_le_ofReal h1
    _ = ∫⁻ ω, ENNReal.ofReal (max (F ω) 0) ∂μ := h2
    _ = ∫⁻ ω, ENNReal.ofReal (F ω) ∂μ := by simp_rw [h3]

variable [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] [DecidableEq V]

/-- **The value of every bounded stopping rule is at most the walk average of
`sup_n S_n`.** -/
theorem supStopValue_le_lintegral_supPayoff [Infinite V] (hG : G.Connected)
    (ξ : V → ℝ) (x : V) :
    RWRS.supStopValue G ξ x ≤ ∫⁻ X, RWRS.supPayoff G ξ X ∂(RWRS.walkLaw G x) := by
  classical
  have hdeg : ∀ v : V, 0 < G.degree v := fun v => degree_pos hG v
  haveI : IsProbabilityMeasure (RWRS.walkLaw G x) := by rw [walkLaw_eq_lib]; infer_instance
  rw [RWRS.supStopValue]
  refine iSup_le fun n => iSup_le fun a => iSup_le fun ha => ?_
  obtain ⟨τ, hτ, hτn, rfl⟩ := ha
  set B : Finset V := (finite_closedBall (G := G) x n).toFinset with hBdef
  have hBmem : ∀ v : V, v ∈ B ↔ G.edist v x ≤ (n : ℕ∞) := by
    intro v
    rw [hBdef, Set.Finite.mem_toFinset]
    rfl
  set τ' : (ℕ → V) → ℕ := fun X => min (τ X) (exitTrunc (B : Set V) n X) with hτ'def
  have hτ'stop : RWRS.IsStopping τ' :=
    isStopping_min hτ (isStopping_exitTrunc (B : Set V) n)
  have hτ'n : ∀ X, τ' X ≤ n := fun X => le_trans (min_le_left _ _) (hτn X)
  have hcongr : RWRS.walkExp G n x (fun X => RWRS.payoff G ξ (τ X) X)
      = RWRS.walkExp G n x (fun X => RWRS.payoff G ξ (τ' X) X) := by
    refine walkExp_congr_ball n x _ _ fun X hX => ?_
    have hstay : X ∈ stayIn (B : Set V) n := by
      intro j hj
      have h1 : G.edist x (X j) ≤ (j : ℕ∞) := hX j hj
      have h2 : G.edist (X j) x ≤ (n : ℕ∞) := by
        rw [SimpleGraph.edist_comm]
        exact le_trans h1 (by exact_mod_cast hj)
      have : X j ∈ B := (hBmem (X j)).2 h2
      exact_mod_cast this
    have htr : exitTrunc (B : Set V) n X = n := by rw [exitTrunc, if_pos hstay]
    have hval : τ' X = τ X := by
      simp only [hτ'def, htr]
      exact min_eq_left (hτn X)
    rw [hval]
  have hdep : DependsUpTo n (fun X => RWRS.payoff G ξ (τ' X) X) :=
    dependsUpTo_payoff_stopping hτ'stop hτ'n ξ
  have hbound : ∀ X : ℕ → V,
      ‖RWRS.payoff G ξ (τ' X) X‖ ≤ (n : ℝ) * stepBound G ξ B := by
    intro X
    rw [Real.norm_eq_abs]
    have h1 := abs_payoff_le (G := G) (ξ := ξ) (C := B) (n := τ' X) (X := X)
      (fun k hk => mem_of_lt_exitTrunc B n X (lt_of_lt_of_le hk (min_le_right _ _)))
    have h2 : ((τ' X : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hτ'n X
    have h3 : (0 : ℝ) ≤ stepBound G ξ B := stepBound_nonneg ξ B
    nlinarith
  have hmeas : Measurable fun X : ℕ → V => RWRS.payoff G ξ (τ' X) X :=
    measurable_of_dependsUpTo hdep
  have hint : RWRS.walkExp G n x (fun X => RWRS.payoff G ξ (τ' X) X)
      = ∫ X, RWRS.payoff G ξ (τ' X) X ∂(RWRS.walkLaw G x) := by
    rw [walkExp_eq_lib n x, walkLaw_eq_lib x]
    exact LatticeProb.Graph.walkExp_eq_integral hdeg n x _ hmeas
      ((n : ℝ) * stepBound G ξ B) hbound hdep
  have hintg : Integrable (fun X : ℕ → V => RWRS.payoff G ξ (τ' X) X) (RWRS.walkLaw G x) :=
    (memLp_top_of_bound hmeas.aestronglyMeasurable ((n : ℝ) * stepBound G ξ B)
      (Filter.Eventually.of_forall hbound)).integrable (by norm_num)
  rw [hcongr, hint]
  refine le_trans (ofReal_integral_le_lintegral hintg) ?_
  refine lintegral_mono fun X => ?_
  exact le_iSup (fun k : ℕ => ENNReal.ofReal (RWRS.payoff G ξ k X)) (τ' X)

end RWRS.Support
