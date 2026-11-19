import RWRS.Support.RootedGraphClasses

/-!
# Extension from connected networks

A measurable observable on connected networks extends by zero to all network
codes. Isomorphism invariance is preserved by this extension.
-/

namespace RWRS.Support

open MeasureTheory Function
open scoped ENNReal

/-- Extend an observable on connected networks by zero. -/
noncomputable def goodNetExtend (f : GoodNet → ℝ≥0∞) : Net 0 → ℝ≥0∞ :=
  Function.extend (Subtype.val : GoodNet → Net 0) f (fun _ => 0)

/-- The extension agrees with the original observable on connected networks. -/
theorem goodNetExtend_of_good (f : GoodNet → ℝ≥0∞) (N : Net 0) (hN : NetGood N) :
    goodNetExtend f N = f ⟨N, hN⟩ := by
  exact Subtype.val_injective.extend_apply f (fun _ => 0) ⟨N, hN⟩

/-- The extension vanishes on disconnected networks. -/
theorem goodNetExtend_of_not_good (f : GoodNet → ℝ≥0∞) (N : Net 0) (hN : ¬ NetGood N) :
    goodNetExtend f N = 0 := by
  apply Function.extend_apply'
  rintro ⟨⟨M, hM⟩, hMN⟩
  exact hN (hMN ▸ hM)

/-- The zero extension of a measurable observable is measurable. -/
theorem measurable_goodNetExtend {f : GoodNet → ℝ≥0∞} (hf : Measurable f) :
    Measurable (goodNetExtend f) :=
  (MeasurableEmbedding.subtype_coe measurableSet_netGood).measurable_extend hf measurable_const

/-- The zero extension of an isomorphism-invariant observable is isomorphism invariant. -/
theorem netInvariant_goodNetExtend {f : GoodNet → ℝ≥0∞}
    (hf : ∀ N N' : GoodNet, NetIso N.1 N'.1 → f N = f N') :
    NetInvariant (goodNetExtend f) := by
  intro N N' h
  by_cases hN : NetGood N
  · have hN' : NetGood N' := (netGood_iff_of_netIso h).1 hN
    rw [goodNetExtend_of_good f N hN, goodNetExtend_of_good f N' hN']
    exact hf ⟨N, hN⟩ ⟨N', hN'⟩ h
  · have hN' : ¬ NetGood N' := fun h' => hN ((netGood_iff_of_netIso h).2 h')
    rw [goodNetExtend_of_not_good f N hN, goodNetExtend_of_not_good f N' hN']

/-- A class observable, extended by zero, is isomorphism invariant. -/
theorem netInvariant_goodNetExtend_class (f : RootedBallClass → ℝ≥0∞) :
    NetInvariant (goodNetExtend (f ∘ goodNetClass)) := by
  apply netInvariant_goodNetExtend
  intro N N' h
  change f (goodNetClass N) = f (goodNetClass N')
  rw [(goodNetClass_eq_iff_netIso N N').2 h]

end RWRS.Support
