import RWRS.Support.GoodNetExtend
import RWRS.Support.ErgReroot

/-!
# Rerooting averages on rooted graph classes

The one-step neighbor average of a measurable class observable descends to a
measurable observable on realized rooted graph classes.
-/

namespace RWRS.Support

open MeasureTheory
open scoped ENNReal

/-- The neighbor average of a measurable class observable descends measurably. -/
theorem exists_measurable_classRerootAvg (f : RootedBallClass → ℝ≥0∞) (hf : Measurable f) :
    ∃ g : RootedBallClass → ℝ≥0∞, Measurable g ∧
      ∀ N : GoodNet,
        g (goodNetClass N) = rerootAvg (goodNetExtend (f ∘ goodNetClass)) N.1 := by
  let H : Net 0 → ℝ≥0∞ := goodNetExtend (f ∘ goodNetClass)
  have hH : Measurable H := measurable_goodNetExtend (hf.comp measurable_goodNetClass)
  have hHiso : NetInvariant H := netInvariant_goodNetExtend_class f
  have hAvg : Measurable fun N : GoodNet => rerootAvg H N.1 :=
    (measurable_rerootAvg hH).comp measurable_subtype_coe
  have hAvgIso : ∀ N N' : GoodNet, NetIso N.1 N'.1 →
      rerootAvg H N.1 = rerootAvg H N'.1 := by
    intro N N' h
    exact netInvariant_rerootAvg hHiso N.1 N'.1 h
  exact exists_measurable_goodNetClass_factor_of_netIso _ hAvg hAvgIso

end RWRS.Support
