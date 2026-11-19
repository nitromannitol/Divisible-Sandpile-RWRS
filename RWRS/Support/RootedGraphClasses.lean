import RWRS.Support.RootedBallDescent
import RWRS.Support.RootedGraphIsomorphism

/-!
# Rooted graph classes and measurable observables

Connected rooted graphs have the same finite-ball sequence precisely when
they are isomorphic. Measurable isomorphism-invariant observables descend to
the space of realized sequences.
-/

namespace RWRS.Support

open MeasureTheory

/-- Connected rooted graphs have the same ball class exactly when isomorphic. -/
theorem goodNetClass_eq_iff_netIso (N N' : GoodNet) :
    goodNetClass N = goodNetClass N' ↔ NetIso N.1 N'.1 := by
  constructor
  · intro h
    apply netIso_of_netBallTypes_eq N.2 N'.2
    exact congrArg Subtype.val h
  · intro h
    apply Subtype.ext
    exact netBallTypes_eq_of_netIso h

/-- Every measurable isomorphism-invariant observable descends to ball classes. -/
theorem exists_measurable_goodNetClass_factor_of_netIso {β : Type*} [MeasurableSpace β]
    (f : GoodNet → β) (hf : Measurable f)
    (hiso : ∀ N N', NetIso N.1 N'.1 → f N = f N') :
    ∃ g : RootedBallClass → β, Measurable g ∧ ∀ N, g (goodNetClass N) = f N := by
  apply exists_measurable_goodNetClass_factor f hf
  intro N N' h
  exact hiso N N' ((goodNetClass_eq_iff_netIso N N').1 h)

end RWRS.Support
