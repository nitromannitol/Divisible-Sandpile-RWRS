import RWRS.Support.RootedClassHarmonic
import RWRS.Support.RootedClassInvariantVersion
import RWRS.Support.StationaryHarmonic

/-!
# Invariant versions of stationary harmonic class observables

A bounded measurable harmonic observable has an invariant version under any
stationary class law. In particular this applies to means of shift-invariant
path observables.
-/

namespace RWRS.Support

open MeasureTheory ProbabilityTheory

/-- A bounded harmonic class observable has a rerooting-invariant version. -/
theorem exists_invariant_version_of_harmonic (ν : Measure RootedBallClass)
    [IsProbabilityMeasure ν] (hstat : classRerootKernel ∘ₘ ν = ν)
    {f : RootedBallClass → ℝ} (hf : Measurable f)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ c, |f c| ≤ C)
    (hharm : ∀ c, f c = ∫ d, f d ∂classRerootKernel c) :
    ∃ g : RootedBallClass → ℝ, Measurable[rootedClassInvariantSigma] g ∧ f =ᵐ[ν] g := by
  let R : Set (RootedBallClass × RootedBallClass) := {p | f p.2 ≠ f p.1}
  have hR : MeasurableSet R := (measurableSet_eq_fun (hf.comp measurable_snd)
    (hf.comp measurable_fst)).compl
  let E : Set RootedBallClass := {c | 0 < classRerootKernel c (Prod.mk c ⁻¹' R)}
  have hE : MeasurableSet E := measurableSet_lt measurable_const
    (Kernel.measurable_kernel_prodMk_left hR)
  have hae := Measure.ae_ae_of_ae_compProd (ae_eq_of_stationary_harmonic ν classRerootKernel
    hstat hf hC hbound hharm)
  have hzero : ν E = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hae] with c hc
    have hz : classRerootKernel c (Prod.mk c ⁻¹' R) = 0 := by
      apply ae_iff.mp
      filter_upwards [hc] with d hd
      exact hd
    change ¬ 0 < classRerootKernel c (Prod.mk c ⁻¹' R)
    rw [hz]
    exact lt_irrefl _
  apply exists_invariant_version_of_ae_edge_eq ν hstat hf hE hzero
  intro N hN y hy
  by_contra hne
  have hD : MeasurableSet {d : RootedBallClass | f d ≠ f (goodNetClass N)} :=
    (measurableSet_eq_fun hf measurable_const).compl
  have hp := classRerootKernel_apply_pos_of_neighbor N hD hy (Ne.symm hne)
  apply hN
  exact hp

/-- A bounded shift-invariant path observable has an invariant version of its class mean. -/
theorem exists_invariant_version_pathMean (ν : Measure RootedBallClass)
    [IsProbabilityMeasure ν] (hstat : classRerootKernel ∘ₘ ν = ν)
    {L : (ℕ → RootedBallClass) → ℝ} (hL : Measurable L)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ x, |L x| ≤ C)
    (hshift : ∀ x, L (rootedClassPathShift x) = L x) :
    ∃ g : RootedBallClass → ℝ, Measurable[rootedClassInvariantSigma] g ∧
      rootedClassPathMean L =ᵐ[ν] g := by
  exact exists_invariant_version_of_harmonic ν hstat (measurable_rootedClassPathMean hL)
    hC (abs_rootedClassPathMean_le hbound) (rootedClassPathMean_harmonic hL hbound hshift)

end RWRS.Support
