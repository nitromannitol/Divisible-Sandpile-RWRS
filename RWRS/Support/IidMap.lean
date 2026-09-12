/-
One identification of the i.i.d. law of a scenery.

The field restricted to a subset of the index set is the i.i.d. field indexed by
that subset.  This is what carries a statement about the scenery on a graph
whose vertex set is a subset of a larger index set to the same statement on the
larger one.
-/
import RWRS.Scenery

open MeasureTheory

namespace RWRS.Support

/-- **The restriction of an i.i.d. field to a subset of its index set** is the
i.i.d. field indexed by that subset. -/
theorem iidLaw_restrict {ι : Type*} (S : Set ι) (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    (RWRS.iidLaw ι ν).map S.restrict = RWRS.iidLaw S ν := by
  simpa [RWRS.iidLaw] using
    (Measure.infinitePi_map_restrict' (μ := fun _ : ι => ν) (I := S))

end RWRS.Support
