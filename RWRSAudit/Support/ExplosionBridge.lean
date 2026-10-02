import Mathlib
import RWRS.MainTheorems
import RWRSAudit.Explosion.SolutionBasic

/-!
# Bridge from the `Explosion` vocabulary to the repository

The vocabulary of `RWRSAudit/Explosion/Challenge.lean` (copied verbatim into
`RWRSAudit/Explosion/SolutionBasic.lean`, which imports only Mathlib) is a statement-level copy
of the repository definitions. It contains no structure: every declaration is a definition over
Mathlib types, written token for token as in `RWRS/Basic.lean`, `RWRS/Scenery.lean` and
`RWRS/Setting.lean`. Each constant that the statement of `explosion` depends on is therefore
definitionally equal to its repository counterpart, and this file records each identification as
an equation of constants, proved by `rfl`, which the kernel checks by unfolding both sides.
Nothing is asserted.

**It is imported by the `Solution` file only.**  The `Challenge` and `SolutionBasic` files must
stay Mathlib-only: a repository import inside the vocabulary changes instance elaboration there
and breaks the comparator's constant-by-constant closure check.
-/

namespace RWRSAudit.Bridge

/-! ### Non-recursive definitions -/

theorem emission_eq : @RWRSAudit.emission = @RWRS.emission := rfl

theorem topple_eq : @RWRSAudit.topple = @RWRS.topple := rfl

theorem config_eq : @RWRSAudit.config = @RWRS.config := rfl

theorem odometer_eq : @RWRSAudit.odometer = @RWRS.odometer := rfl

theorem odometerLimit_eq : @RWRSAudit.odometerLimit = @RWRS.odometerLimit := rfl

theorem Stabilizes_eq : @RWRSAudit.Stabilizes = @RWRS.Stabilizes := rfl

theorem iidLaw_eq : @RWRSAudit.iidLaw = @RWRS.iidLaw := rfl

theorem posPart_eq : @RWRSAudit.posPart = @RWRS.posPart := rfl

theorem negPart_eq : @RWRSAudit.negPart = @RWRS.negPart := rfl

theorem extMean_eq : @RWRSAudit.extMean = @RWRS.extMean := rfl

theorem HasExtMean_eq : @RWRSAudit.HasExtMean = @RWRS.HasExtMean := rfl

theorem IsSymmetric_eq : @RWRSAudit.IsSymmetric = @RWRS.IsSymmetric := rfl

theorem evar_eq : @RWRSAudit.evar = @RWRS.evar := rfl

theorem BoundedDegree_eq : @RWRSAudit.BoundedDegree = @RWRS.BoundedDegree := rfl

end RWRSAudit.Bridge
