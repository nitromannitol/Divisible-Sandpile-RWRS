import RWRS.Support.RootedClassTransition

/-!
# Reachability of rooted classes

The positive-probability iterates of the rerooting kernel reach every vertex
of a connected representative.
-/

namespace RWRS.Support

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Classes that can reach `D` by exactly `n` positive-probability transitions. -/
noncomputable def rootedClassReach (D : Set RootedBallClass) : ℕ → Set RootedBallClass
  | 0 => D
  | n + 1 => {c | 0 < classRerootKernel c (rootedClassReach D n)}

/-- Positive-probability reachability preserves measurability. -/
theorem measurableSet_rootedClassReach {D : Set RootedBallClass} (hD : MeasurableSet D) :
    ∀ n, MeasurableSet (rootedClassReach D n)
  | 0 => hD
  | n + 1 => measurableSet_lt measurable_const
      (Kernel.measurable_coe _ (measurableSet_rootedClassReach hD n))

/-- A walk to a class event gives positive-probability reachability. -/
theorem mem_rootedClassReach_of_walk (N : GoodNet) {D : Set RootedBallClass}
    (hD : MeasurableSet D) {u v : ℕ} (p : (netGraph N.1).Walk u v)
    (hv : goodNetClass (goodNetReroot N v) ∈ D) :
    goodNetClass (goodNetReroot N u) ∈ rootedClassReach D p.length := by
  induction p with
  | nil => exact hv
  | @cons u w v huw p ih =>
      change 0 < classRerootKernel (goodNetClass (goodNetReroot N u))
        (rootedClassReach D p.length)
      exact classRerootKernel_apply_pos_of_neighbor (goodNetReroot N u)
        (measurableSet_rootedClassReach hD _) huw (ih hv)

/-- The rerooting saturation is contained in the union of positive-probability iterates. -/
theorem rootedClassSaturation_subset_iUnion_reach {D : Set RootedBallClass}
    (hD : MeasurableSet D) :
    rootedClassSaturation D ⊆ ⋃ n, rootedClassReach D n := by
  intro c hc
  let N := goodNetClassRepresentative c
  have hc' : goodNetClass N ∈ rootedClassSaturation D := by
    rw [goodNetClass_representative]
    exact hc
  obtain ⟨v, hv⟩ := (mem_rootedClassSaturation_iff D N).1 hc'
  obtain ⟨p⟩ := N.2.preconnected (netRoot N.1) v
  have h := mem_rootedClassReach_of_walk N hD p hv
  have heq : goodNetReroot N (netRoot N.1) = N := by
    apply Subtype.ext
    cases N with
    | mk N hN => cases N with | mk a b => cases b; rfl
  rw [heq, goodNetClass_representative] at h
  exact Set.mem_iUnion.mpr ⟨p.length, h⟩

/-- A stationary class law gives zero mass to every positive-probability iterate of a null event. -/
theorem measure_rootedClassReach_eq_zero (ν : Measure RootedBallClass)
    (hstat : classRerootKernel ∘ₘ ν = ν) {D : Set RootedBallClass}
    (hD : MeasurableSet D) (hzero : ν D = 0) :
    ∀ n, ν (rootedClassReach D n) = 0 := by
  intro n
  induction n with
  | zero => exact hzero
  | succ n ih =>
      have hm := measurableSet_rootedClassReach hD n
      have hint : (∫⁻ c, classRerootKernel c (rootedClassReach D n) ∂ν) = 0 := by
        rw [← Measure.bind_apply hm (Kernel.aemeasurable _), hstat, ih]
      have hae := (lintegral_eq_zero_iff (Kernel.measurable_coe _ hm)).1 hint
      apply measure_eq_zero_iff_ae_notMem.mpr
      filter_upwards [hae] with c hc
      change ¬ 0 < classRerootKernel c (rootedClassReach D n)
      simp only [Pi.zero_apply] at hc
      rw [hc]
      exact lt_irrefl _

/-- Rerooting saturation of a null event remains null for a stationary class law. -/
theorem measure_rootedClassSaturation_eq_zero (ν : Measure RootedBallClass)
    (hstat : classRerootKernel ∘ₘ ν = ν) {D : Set RootedBallClass}
    (hD : MeasurableSet D) (hzero : ν D = 0) : ν (rootedClassSaturation D) = 0 := by
  apply measure_mono_null (rootedClassSaturation_subset_iUnion_reach hD)
  exact measure_iUnion_null (measure_rootedClassReach_eq_zero ν hstat hD hzero)

end RWRS.Support
