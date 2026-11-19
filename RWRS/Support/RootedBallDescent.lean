import RWRS.Support.RootedGraphFactor
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Measurable descent to rooted ball sequences

A measurable function on connected graph codes that is constant on fibers of
the ball sequence descends measurably to the space of realized sequences.
-/

namespace RWRS.Support

open MeasureTheory

/-- Connected unmarked network codes. -/
abbrev GoodNet := {N : Net 0 // NetGood N}

/-- Connected network codes form a standard Borel space. -/
instance : StandardBorelSpace GoodNet := measurableSet_netGood.standardBorel

/-- The sequence of rooted ball types of a connected network. -/
noncomputable def goodNetBallTypes (N : GoodNet) : ℕ → ℕ := netBallTypes N.1

/-- The realized rooted ball type sequences. -/
abbrev RootedBallClass := Set.range goodNetBallTypes

/-- A connected network mapped to its rooted ball type sequence. -/
noncomputable def goodNetClass (N : GoodNet) : RootedBallClass :=
  ⟨goodNetBallTypes N, ⟨N, rfl⟩⟩

/-- The rooted ball sequence map is measurable. -/
theorem measurable_goodNetClass : Measurable goodNetClass := by
  exact (measurable_netBallTypes.comp measurable_subtype_coe).subtype_mk

/-- Every realized sequence is the sequence of a connected network. -/
theorem goodNetClass_surjective : Function.Surjective goodNetClass := by
  rintro ⟨v, N, rfl⟩
  exact ⟨N, rfl⟩

/-- A measurable function constant on ball-sequence fibers descends measurably. -/
theorem exists_measurable_goodNetClass_factor {β : Type*} [MeasurableSpace β]
    (f : GoodNet → β) (hf : Measurable f)
    (hclass : ∀ N N', goodNetClass N = goodNetClass N' → f N = f N') :
    ∃ g : RootedBallClass → β, Measurable g ∧ ∀ N, g (goodNetClass N) = f N := by
  classical
  let g : RootedBallClass → β := fun y => f (Classical.choose y.property)
  have hcomp : g ∘ goodNetClass = f := by
    funext N
    apply hclass
    apply Subtype.ext
    exact Classical.choose_spec (goodNetClass N).property
  have hg : Measurable g :=
    (measurable_goodNetClass.measurable_comp_iff_of_surjective goodNetClass_surjective).mp
      (by rw [hcomp]; exact hf)
  exact ⟨g, hg, fun N => congrFun hcomp N⟩

end RWRS.Support
