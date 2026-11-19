import RWRS.External.ErgodicDecomposition
import RWRS.Support.ConditionalErgodicityFromPathInformation
import RWRS.Support.RootedClassPathInformation
import RWRS.Support.RootedClassStationarityTransfer

/-!
# Ergodic decomposition of stationary rooted networks

The conditional law given rerooting-invariant events is supported on connected
networks, stationary, and ergodic. The proof passes to rooted graph classes
and identifies shift-invariant path information with invariant class information.
-/

open MeasureTheory ProbabilityTheory RWRS.Support

/-- The conditional ergodic decomposition of a stationary rooted network law. -/
theorem RWRS.External.ergodicDecomposition : RWRS.External.ErgodicDecomposition := by
  intro Q hQ hgood hstat
  haveI := hQ
  have hclass : classRerootKernel ∘ₘ goodNetClassLaw Q = goodNetClassLaw Q :=
    RWRS.Support.classRerootKernel_comp_goodNetClassLaw Q hgood hstat
  haveI := RWRS.Support.isProbabilityMeasure_goodNetClassLaw Q hgood
  have herg : ∀ᵐ N ∂Q, RWRS.IsErgodicNet (condExpKernel Q (RWRS.invariantSigma 0) N) := by
    apply RWRS.Support.ae_conditional_isErgodicNet_of_path_information Q hgood hstat
    intro L hL hbound hshift
    exact RWRS.Support.exists_invariant_class_of_shift_invariant_path
      (goodNetClassLaw Q) hclass hL zero_le_one hbound hshift
  refine ⟨fun N => condExpKernel Q (RWRS.invariantSigma 0) N, ?_, ?_, ?_, ?_⟩
  · intro N
    infer_instance
  · intro A hA
    exact measurable_condExpKernel hA
  · intro A hA B hB
    exact LatticeProb.setLIntegral_conditionalMeasure Q RWRS.Support.invariantSigma_zero_le hA hB
  · filter_upwards [LatticeProb.ae_ae_conditionalMeasure Q RWRS.Support.invariantSigma_zero_le hgood,
      RWRS.Support.ae_conditional_isStationaryNet Q hgood hstat, herg] with N hN hs he
    exact ⟨hN, hs, he⟩
