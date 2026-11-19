import RWRS.Support.RootedBallProjection
import Mathlib.Order.KonigLemma

/-!
# Compatible rooted ball isomorphisms

Kőnig's lemma selects compatible finite-ball isomorphisms when all rooted
ball types agree.
-/

namespace RWRS.Support

/-- Equal rooted-ball types at every radius admit compatible ball isomorphisms. -/
theorem exists_compatible_rootedBallIso {m : ℕ} {N N' : Net m}
    (h : ∀ r, netBallType N r = netBallType N' r) :
    ∃ f : ∀ r, RootedBallIso N N' r,
      ∀ ⦃i j⦄ (hij : i ≤ j), (f j).restrict hij = f i := by
  classical
  letI (r : ℕ) : Nonempty (RootedBallIso N N' r) :=
    nonempty_rootedBallIso_of_netBallType_eq (h r)
  letI (r : ℕ) : Finite (RootedBallIso N N' r) := finite_rootedBallIso N N' r
  let π : {i j : ℕ} → i ≤ j → RootedBallIso N N' j → RootedBallIso N N' i :=
    fun {_ _} hij φ => φ.restrict hij
  apply exists_seq_forall_proj_of_forall_finite π
  · intro i a
    exact a.restrict_refl
  · intro i j k hij hjk a
    exact a.restrict_restrict hij hjk
  · intro i a
    exact Set.toFinite _

end RWRS.Support
