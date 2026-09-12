/-
Dominated convergence for the emission at the root.

Part (i) of `thm:stationary-phase` needs `E[e_k(ρ)] → 0` from `e_k(ρ) → 0`
almost surely and the uniform bound `e_k(v) ≤ M - 1` of the truncated dynamics
(`rwrs.tex:353`).
-/
import RWRS.Support.ErgTrunc
import RWRS.Support.ErgMass

namespace RWRS.Support

open MeasureTheory Filter Topology

/-- Dominated convergence for the emission at the root: on a law under which the
configuration stabilizes almost surely and the emissions are uniformly bounded,
the mean emission tends to zero. -/
theorem tendsto_integral_netEmission (P : Measure (RWRS.Net 1)) [IsProbabilityMeasure P]
    {C : ℝ} (hbdd : ∀ k : ℕ, ∀ᵐ N ∂P, netEmission N k ≤ C)
    (hstab : ∀ᵐ N ∂P, RWRS.Stabilizes (RWRS.netGraph N) (RWRS.netConfig N)) :
    Tendsto (fun k : ℕ => ∫ N : RWRS.Net 1, netEmission N k ∂P) atTop (𝓝 (0 : ℝ)) := by
  have hlim := MeasureTheory.tendsto_integral_of_dominated_convergence
    (F := fun (k : ℕ) (N : RWRS.Net 1) => netEmission N k) (f := fun _ : RWRS.Net 1 => (0 : ℝ))
    (bound := fun _ : RWRS.Net 1 => C)
    (fun k => (measurable_netEmission k).aestronglyMeasurable)
    (integrable_const C)
    (fun k => by
      filter_upwards [hbdd k] with N hN
      rw [Real.norm_eq_abs, abs_of_nonneg (netEmission_nonneg N k)]
      exact hN)
    (by
      filter_upwards [hstab] with N hN
      exact tendsto_emission_of_stabilizes hN (RWRS.netRoot N))
  simpa using hlim

end RWRS.Support
