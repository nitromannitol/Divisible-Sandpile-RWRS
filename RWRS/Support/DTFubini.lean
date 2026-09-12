/-
The walk average commutes with an integral over the scenery.

`walkExp G n x` is a finite average over the trajectories of length `n`, with
deterministic weights, so integrating it against any finite measure is the same
as integrating the integrand first.  This is what lets Step 1 of
`prop:doubly-transient-really-general` pass from the identity
`E_o[S_τ | ξ] = h_K(o) - E_o[h_K(X_τ) | ξ]`, which holds for each fixed scenery,
to its mean over the scenery.
-/
import RWRS.Support.DTStages

namespace RWRS.Support

open MeasureTheory

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

/-- **A walk average of a bounded functional is bounded.** -/
theorem abs_walkExp_le [Infinite V] (hG : G.Connected) {b : ℝ} :
    ∀ (n : ℕ) (x : V) (F : (ℕ → V) → ℝ), (∀ X, |F X| ≤ b) →
      |RWRS.walkExp G n x F| ≤ b := by
  intro n x F h
  rw [abs_le]
  constructor
  · have := walkExp_mono (G := G) (n := n) (x := x)
      (F := fun _ => -b) (F' := F) fun X => (abs_le.mp (h X)).1
    rwa [walkExp_const hG] at this
  · have := walkExp_mono (G := G) (n := n) (x := x)
      (F := F) (F' := fun _ => b) fun X => (abs_le.mp (h X)).2
    rwa [walkExp_const hG] at this

/-- **A walk average of a measurable family is measurable.** -/
theorem measurable_walkExp {Ω : Type*} [MeasurableSpace Ω] :
    ∀ (n : ℕ) (x : V) (F : Ω → (ℕ → V) → ℝ), (∀ X, Measurable fun ω => F ω X) →
      Measurable fun ω => RWRS.walkExp G n x (F ω) := by
  intro n
  induction n with
  | zero =>
      intro x F hF
      exact hF (fun _ => x)
  | succ n ih =>
      intro x F hF
      have hstep : (fun ω => RWRS.walkExp G (n + 1) x (F ω))
          = fun ω => (∑ y ∈ G.neighborFinset x,
              RWRS.walkExp G n y (fun X => F ω (RWRS.cons x X))) / (G.degree x : ℝ) := by
        funext ω
        exact walkExp_succ n x (F ω)
      rw [hstep]
      refine Measurable.div_const ?_ _
      refine Finset.measurable_sum _ fun y _ => ?_
      exact ih y (fun ω X => F ω (RWRS.cons x X)) fun X => hF (RWRS.cons x X)

/-- **The walk average commutes with the integral.**  The functional need only be
dominated by an integrable function of the scenery, not by a constant. -/
theorem integral_walkExp {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    [Infinite V] (hG : G.Connected) {B : Ω → ℝ} (hB : Integrable B μ) :
    ∀ (n : ℕ) (x : V) (F : Ω → (ℕ → V) → ℝ), (∀ X : ℕ → V, Measurable fun ω => F ω X) →
      (∀ ω X, |F ω X| ≤ B ω) →
      ∫ ω, RWRS.walkExp G n x (F ω) ∂μ = RWRS.walkExp G n x (fun X => ∫ ω, F ω X ∂μ) := by
  intro n
  induction n with
  | zero =>
      intro x F _ _
      rfl
  | succ n ih =>
      intro x F hmeas hbd
      have hstep : ∀ ω, RWRS.walkExp G (n + 1) x (F ω)
          = (∑ y ∈ G.neighborFinset x,
              RWRS.walkExp G n y (fun X => F ω (RWRS.cons x X))) / (G.degree x : ℝ) :=
        fun ω => walkExp_succ n x (F ω)
      have hint : ∀ y ∈ G.neighborFinset x,
          Integrable (fun ω => RWRS.walkExp G n y (fun X => F ω (RWRS.cons x X))) μ := by
        intro y _
        refine Integrable.mono' hB.abs
          (measurable_walkExp n y (fun ω X => F ω (RWRS.cons x X))
            (fun X => hmeas (RWRS.cons x X))).aestronglyMeasurable
          (Filter.Eventually.of_forall fun ω => ?_)
        rw [Real.norm_eq_abs]
        refine le_trans (abs_walkExp_le hG n y _ fun X => hbd ω (RWRS.cons x X)) ?_
        exact le_abs_self (B ω)
      rw [integral_congr_ae (Filter.Eventually.of_forall hstep), integral_div,
        integral_finsetSum _ hint]
      rw [walkExp_succ]
      congr 1
      refine Finset.sum_congr rfl fun y _ => ?_
      exact ih y (fun ω X => F ω (RWRS.cons x X)) (fun X => hmeas (RWRS.cons x X))
        (fun ω X => hbd ω (RWRS.cons x X))

end RWRS.Support
