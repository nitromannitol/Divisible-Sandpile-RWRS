import RWRS.Support.ConditionalClassStationarity

/-!
# Transferring class stationarity to network laws

A law supported on connected network codes is stationary in the source sense
whenever its rooted-class law is stationary for the rerooting kernel.
-/

namespace RWRS.Support

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Integrating a class observable against the class kernel gives its rerooting average. -/
theorem lintegral_classRerootKernel_goodNet (N : GoodNet) {f : RootedBallClass → ℝ≥0∞}
    (hf : Measurable f) :
    (∫⁻ c, f c ∂classRerootKernel (goodNetClass N)) =
      rerootAvg (goodNetExtend (f ∘ goodNetClass)) N.1 := by
  let R := goodNetClassRepresentative (goodNetClass N)
  have hrep : NetIso R.1 N.1 := (goodNetClass_eq_iff_netIso R N).1
    (goodNetClass_representative (goodNetClass N))
  have hiso := netInvariant_rerootAvg (netInvariant_goodNetExtend_class f) R.1 N.1 hrep
  rw [← hiso]
  change (∫⁻ c, f c ∂(((netGraph R.1).degree (netRoot R.1) : ℝ≥0∞)⁻¹ •
    ∑ y ∈ (netGraph R.1).neighborFinset (netRoot R.1),
      Measure.dirac (goodNetClass ⟨netReroot R.1 y, netGood_netReroot R.2 y⟩))) = _
  rw [lintegral_smul_measure, lintegral_finsetSum_measure]
  simp_rw [lintegral_dirac' _ hf]
  unfold rerootAvg
  rw [div_eq_mul_inv, mul_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro y hy
  rw [goodNetExtend_of_good _ _ (netGood_netReroot R.2 y)]
  rfl

/-- Stationarity of the class law implies source stationarity on connected network codes. -/
theorem isStationaryNet_of_goodNetClassLaw (Q : Measure (Net 0))
    (hgood : ∀ᵐ N ∂Q, NetGood N)
    (hstat : classRerootKernel ∘ₘ goodNetClassLaw Q = goodNetClassLaw Q) :
    IsStationaryNet Q := by
  intro h hh hiso
  obtain ⟨f, hf, hfac⟩ := exists_measurable_goodNetClass_factor_of_netIso
    (fun N : GoodNet => h N.1) (hh.comp measurable_subtype_coe)
    (fun N N' hNN' => hiso N.1 N'.1 hNN')
  let F := goodNetExtend (f ∘ goodNetClass)
  have heq : F =ᵐ[Q] h := by
    filter_upwards [hgood] with N hN
    rw [show F N = f (goodNetClass ⟨N, hN⟩) from goodNetExtend_of_good _ _ hN]
    exact hfac ⟨N, hN⟩
  have haveq : (fun N => rerootAvg F N) =ᵐ[Q] (fun N => rerootAvg h N) := by
    filter_upwards [hgood] with N hN
    unfold rerootAvg
    congr 1
    apply Finset.sum_congr rfl
    intro y hy
    rw [show F (netReroot N y) = f (goodNetClass ⟨netReroot N y, netGood_netReroot hN y⟩) from
      goodNetExtend_of_good _ _ (netGood_netReroot hN y)]
    exact hfac ⟨netReroot N y, netGood_netReroot hN y⟩
  have hclass : (∫⁻ c, f c ∂goodNetClassLaw Q) =
      ∫⁻ c, ∫⁻ d, f d ∂classRerootKernel c ∂goodNetClassLaw Q := by
    conv_lhs => rw [← hstat]
    rw [Measure.lintegral_bind (Kernel.aemeasurable _) hf.aemeasurable]
  have hr : (∫⁻ c, ∫⁻ d, f d ∂classRerootKernel c ∂goodNetClassLaw Q) =
      ∫⁻ N, rerootAvg F N ∂Q := by
    rw [lintegral_goodNetClassLaw Q hgood (hf.lintegral_kernel (κ := classRerootKernel))]
    apply lintegral_congr_ae
    filter_upwards [hgood] with N hN
    rw [goodNetExtend_of_good _ N hN]
    exact lintegral_classRerootKernel_goodNet ⟨N, hN⟩ hf

  calc
    ∫⁻ N, h N ∂Q = ∫⁻ N, F N ∂Q := (lintegral_congr_ae heq).symm
    _ = ∫⁻ c, f c ∂goodNetClassLaw Q := (lintegral_goodNetClassLaw Q hgood hf).symm
    _ = ∫⁻ c, ∫⁻ d, f d ∂classRerootKernel c ∂goodNetClassLaw Q := hclass
    _ = ∫⁻ N, rerootAvg F N ∂Q := hr
    _ = ∫⁻ N, rerootAvg h N ∂Q := lintegral_congr_ae haveq

/-- Conditional network laws of a stationary connected law are almost surely stationary. -/
theorem ae_conditional_isStationaryNet (Q : Measure (Net 0)) [IsProbabilityMeasure Q]
    (hgood : ∀ᵐ N ∂Q, NetGood N) (hstat : IsStationaryNet Q) :
    ∀ᵐ N ∂Q, IsStationaryNet (condExpKernel Q (invariantSigma 0) N) := by
  filter_upwards [LatticeProb.ae_ae_conditionalMeasure Q invariantSigma_zero_le hgood,
    ae_conditional_goodNetClassLaw_stationary Q hgood hstat] with N hN hs
  exact isStationaryNet_of_goodNetClassLaw _ hN hs

end RWRS.Support
