import RWRS.Support.RootedClassPathStationaryMarginals
import RWRS.Support.ConditionalKernelStationarity
import RWRS.Support.RootedClassTotalMap
import RWRS.Support.RootedClassStationaryRestriction
import RWRS.Support.ConditionalNet

/-!
# Stationarity of conditional rooted-class laws

Conditioning a stationary connected network law on its invariant σ-algebra
produces almost surely stationary laws on rooted graph classes.
-/

namespace RWRS.Support

open MeasureTheory ProbabilityTheory

/-- The invariant σ-algebra is contained in the ambient network σ-algebra. -/
theorem invariantSigma_zero_le : invariantSigma 0 ≤ (inferInstance : MeasurableSpace (Net 0)) :=
  fun _ h => h.1

/-- The class law of an invariant restriction is the corresponding class restriction. -/
theorem goodNetClassLaw_restrict_invariant (N₀ : GoodNet) (Q : Measure (Net 0))
    (hgood : ∀ᵐ N ∂Q, NetGood N) {B : Set (Net 0)}
    (hB : MeasurableSet[invariantSigma 0] B) :
    ∃ D : Set RootedBallClass, MeasurableSet[rootedClassInvariantSigma] D ∧
      goodNetClassLaw (Q.restrict B) = (goodNetClassLaw Q).restrict D := by
  obtain ⟨D, hD, hdesc⟩ := exists_classInvariant_event hB
  refine ⟨D, hD, ?_⟩
  have heq : B =ᵐ[Q] goodNetClassTotal N₀ ⁻¹' D := by
    filter_upwards [hgood] with N hN
    apply propext
    change N ∈ B ↔ goodNetClassTotal N₀ N ∈ D
    rw [goodNetClassTotal_of_good N₀ ⟨N, hN⟩]
    exact hdesc ⟨N, hN⟩
  rw [goodNetClassLaw_eq_map_total N₀ (Q.restrict B) (ae_restrict_le hgood),
    goodNetClassLaw_eq_map_total N₀ Q hgood, Measure.restrict_congr_set heq,
    Measure.restrict_map (measurable_goodNetClassTotal N₀) hD.1]

/-- The conditional rooted-class kernel, with a fixed class on disconnected codes. -/
noncomputable def conditionalClassKernel (N₀ : GoodNet) (Q : Measure (Net 0))
    [IsProbabilityMeasure Q] : @Kernel (Net 0) RootedBallClass (invariantSigma 0) _ :=
  (condExpKernel Q (invariantSigma 0)).map (goodNetClassTotal N₀)

/-- The conditional class kernel is Markov. -/
instance isMarkovKernel_conditionalClassKernel (N₀ : GoodNet) (Q : Measure (Net 0))
    [IsProbabilityMeasure Q] : IsMarkovKernel (conditionalClassKernel N₀ Q) :=
  Kernel.IsMarkovKernel.map _ (measurable_goodNetClassTotal N₀)

/-- Mixing the conditional class laws over an invariant event gives the restricted class law. -/
theorem conditionalClassKernel_comp_restrict (N₀ : GoodNet) (Q : Measure (Net 0))
    [IsProbabilityMeasure Q] (hgood : ∀ᵐ N ∂Q, NetGood N)
    {B : Set (Net 0)} (hB : MeasurableSet[invariantSigma 0] B) :
    conditionalClassKernel N₀ Q ∘ₘ (Q.trim invariantSigma_zero_le).restrict B =
      goodNetClassLaw (Q.restrict B) := by
  rw [goodNetClassLaw_eq_map_total N₀ (Q.restrict B) (ae_restrict_le hgood)]
  ext D hD
  rw [Measure.bind_apply hD (Kernel.aemeasurable _)]
  simp_rw [conditionalClassKernel, Kernel.map_apply' _ (measurable_goodNetClassTotal N₀) _ hD]
  rw [setLIntegral_trim invariantSigma_zero_le
      (measurable_condExpKernel ((measurable_goodNetClassTotal N₀) hD)) hB,
    LatticeProb.setLIntegral_conditionalMeasure Q invariantSigma_zero_le
      ((measurable_goodNetClassTotal N₀) hD) hB,
    Measure.map_apply (measurable_goodNetClassTotal N₀) hD,
    Measure.restrict_apply ((measurable_goodNetClassTotal N₀) hD)]

/-- Conditional class laws of a stationary connected network law are almost surely stationary. -/
theorem ae_conditional_goodNetClassLaw_stationary (Q : Measure (Net 0))
    [IsProbabilityMeasure Q] (hgood : ∀ᵐ N ∂Q, NetGood N) (hstat : IsStationaryNet Q) :
    ∀ᵐ N ∂Q, classRerootKernel ∘ₘ goodNetClassLaw (condExpKernel Q (invariantSigma 0) N) =
      goodNetClassLaw (condExpKernel Q (invariantSigma 0) N) := by
  obtain ⟨N, hN⟩ := hgood.exists
  let N₀ : GoodNet := ⟨N, hN⟩
  have hclass := classRerootKernel_comp_goodNetClassLaw Q hgood hstat
  have hmixed : ∀ B : Set (Net 0), MeasurableSet[invariantSigma 0] B →
      classRerootKernel ∘ₘ (conditionalClassKernel N₀ Q ∘ₘ
        (Q.trim invariantSigma_zero_le).restrict B) =
        conditionalClassKernel N₀ Q ∘ₘ (Q.trim invariantSigma_zero_le).restrict B := by
    intro B hB
    rw [conditionalClassKernel_comp_restrict N₀ Q hgood hB]
    obtain ⟨D, hD, heq⟩ := goodNetClassLaw_restrict_invariant N₀ Q hgood hB
    rw [heq]
    exact classRerootKernel_comp_restrict _ hclass hD
  have hker : ∀ᵐ M ∂Q.trim invariantSigma_zero_le,
      classRerootKernel ∘ₘ conditionalClassKernel N₀ Q M = conditionalClassKernel N₀ Q M := by
    letI : MeasurableSpace (Net 0) := invariantSigma 0
    exact ae_kernel_stationary_of_restrict (Q.trim invariantSigma_zero_le)
      (conditionalClassKernel N₀ Q) classRerootKernel hmixed
  have hker' := ae_of_ae_trim invariantSigma_zero_le hker
  have hsupport := LatticeProb.ae_ae_conditionalMeasure Q invariantSigma_zero_le hgood
  filter_upwards [hker', hsupport] with M hM hMg
  have heq : conditionalClassKernel N₀ Q M = goodNetClassLaw (condExpKernel Q (invariantSigma 0) M) := by
    rw [conditionalClassKernel, Kernel.map_apply _ (measurable_goodNetClassTotal N₀),
      goodNetClassLaw_eq_map_total N₀ _ hMg]
  rwa [heq] at hM

end RWRS.Support
