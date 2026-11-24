import RWRS.MainTheorems
import RWRS.StationaryTheorems

/-!
# Axioms audit

Building this module prints the axiom dependencies of the three main theorems
of `RWRS/MainTheorems.lean` and of the stationary zero-one law and phase
result of `RWRS/StationaryTheorems.lean`, which take no ergodic decomposition
hypothesis.  Each must report exactly the three standard foundational axioms of
Mathlib: `propext`, `Classical.choice`, `Quot.sound`.

The results the paper cites without proof are not axioms here: each is a
`Prop` in `RWRS/External/` and is proved in this repository.  The one that
frozen statements carry as a hypothesis, the ergodic decomposition, is
discharged in `RWRS/StationaryTheorems.lean`.

This file is not imported by the library root; the report runs when it is built
explicitly (`lake build RWRS.Meta.AxiomsAudit`), as continuous integration
does on every push.
-/

#print axioms RWRS.optimalStopping
#print axioms RWRS.explosion
#print axioms RWRS.stabilization
#print axioms RWRS.zeroOneStationary
#print axioms RWRS.stationaryPhase
