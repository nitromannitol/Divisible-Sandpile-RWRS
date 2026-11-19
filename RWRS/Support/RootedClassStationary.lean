import RWRS.Support.ClassRerootAverage

/-!
# Stationarity on rooted graph classes

A stationary law supported on connected codes pushes forward to a law that
preserves the descended one-step averages of measurable class observables.
-/

namespace RWRS.Support

open MeasureTheory
open scoped ENNReal

/-- Push a network law to the realized rooted graph classes. -/
noncomputable def goodNetClassLaw (Q : Measure (Net 0)) : Measure RootedBallClass :=
  (Q.comap (Subtype.val : GoodNet → Net 0)).map goodNetClass

/-- Integrals of class observables are integrals of their zero extensions. -/
theorem lintegral_goodNetClassLaw (Q : Measure (Net 0))
    (hgood : ∀ᵐ N ∂Q, NetGood N) {f : RootedBallClass → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ c, f c ∂goodNetClassLaw Q =
      ∫⁻ N, goodNetExtend (f ∘ goodNetClass) N ∂Q := by
  let H := goodNetExtend (f ∘ goodNetClass)
  calc
    ∫⁻ c, f c ∂goodNetClassLaw Q =
        ∫⁻ N : GoodNet, f (goodNetClass N) ∂(Q.comap (Subtype.val : GoodNet → Net 0)) := by
      exact lintegral_map hf measurable_goodNetClass
    _ = ∫⁻ N : GoodNet, H N.1 ∂(Q.comap (Subtype.val : GoodNet → Net 0)) := by
      apply lintegral_congr
      intro N
      exact (goodNetExtend_of_good (f ∘ goodNetClass) N.1 N.2).symm
    _ = ∫⁻ N in {N : Net 0 | NetGood N}, H N ∂Q :=
      lintegral_subtype_comap measurableSet_netGood H
    _ = ∫⁻ N, H N ∂Q := by
      have hQ : Q.restrict {N : Net 0 | NetGood N} = Q :=
        Measure.restrict_eq_self_of_ae_mem hgood
      change (∫⁻ N, H N ∂(Q.restrict {N : Net 0 | NetGood N})) = _
      rw [hQ]

/-- Stationarity descends to the one-step averages of measurable class observables. -/
theorem exists_classRerootAvg_integral_eq (Q : Measure (Net 0))
    (hgood : ∀ᵐ N ∂Q, NetGood N) (hstat : IsStationaryNet Q)
    (f : RootedBallClass → ℝ≥0∞) (hf : Measurable f) :
    ∃ g : RootedBallClass → ℝ≥0∞, Measurable g ∧
      (∀ N : GoodNet,
        g (goodNetClass N) = rerootAvg (goodNetExtend (f ∘ goodNetClass)) N.1) ∧
      (∫⁻ c, g c ∂goodNetClassLaw Q) = ∫⁻ c, f c ∂goodNetClassLaw Q := by
  obtain ⟨g, hg, hgeq⟩ := exists_measurable_classRerootAvg f hf
  refine ⟨g, hg, hgeq, ?_⟩
  let H := goodNetExtend (f ∘ goodNetClass)
  have hH : Measurable H := measurable_goodNetExtend (hf.comp measurable_goodNetClass)
  have hHiso : NetInvariant H := netInvariant_goodNetExtend_class f
  calc
    ∫⁻ c, g c ∂goodNetClassLaw Q =
        ∫⁻ N : GoodNet, g (goodNetClass N) ∂(Q.comap (Subtype.val : GoodNet → Net 0)) := by
      exact lintegral_map hg measurable_goodNetClass
    _ = ∫⁻ N : GoodNet, rerootAvg H N.1 ∂(Q.comap (Subtype.val : GoodNet → Net 0)) := by
      exact lintegral_congr hgeq
    _ = ∫⁻ N in {N : Net 0 | NetGood N}, rerootAvg H N ∂Q :=
      lintegral_subtype_comap measurableSet_netGood (rerootAvg H)
    _ = ∫⁻ N, rerootAvg H N ∂Q := by
      have hQ : Q.restrict {N : Net 0 | NetGood N} = Q :=
        Measure.restrict_eq_self_of_ae_mem hgood
      change (∫⁻ N, rerootAvg H N ∂(Q.restrict {N : Net 0 | NetGood N})) = _
      rw [hQ]
    _ = ∫⁻ N, H N ∂Q := (hstat H hH hHiso).symm
    _ = ∫⁻ c, f c ∂goodNetClassLaw Q := (lintegral_goodNetClassLaw Q hgood hf).symm

end RWRS.Support
