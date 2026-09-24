/-
External input: the ergodic decomposition of a stationary random rooted graph,
quoted in the proof of `lem:01-stationary` (`rwrs.tex:337-342`) from Benjamini
and Curien, *Ergodic theory on stationary random graphs*, Section 2.1:
conditionally on the σ-algebra `I_G` of rerooting-invariant events, the law of
`(G,ρ)` is stationary and ergodic.

The conditional law is a kernel `K` on rooted graphs: `K N` is a probability
measure, the map `N ↦ K N A` is `I_G`-measurable, and the conditional
expectation identity `∫⁻_{B} K N A dQ = Q (A ∩ B)` holds for every
rerooting-invariant `B`, which is what makes `K` a version of the conditional
law of `(G,ρ)` given `I_G` rather than an unindexed mixture.  Taking
`B = univ` recovers the mixture identity `Q A = ∫⁻ K N A dQ`.  Almost every
component is again supported on connected rooted graphs, stationary, and
ergodic.

The marks are NOT part of this input: that they remain i.i.d. under the
conditional law is proved, in `RWRS.Support.condExp_indicator_markIid`, from the identity
above and the product construction of `markIid`.

Assumed here.  It enters only as an explicit hypothesis of the results whose
proofs use it.
-/
import RWRS.Network

open MeasureTheory
open scoped ENNReal

-- FROZEN-STATEMENT-BEGIN
/-- "By the ergodic decomposition, conditionally on $\mathcal I_G$ the law of
$(G,\rho)$ is stationary and ergodic." -/
def RWRS.External.ErgodicDecomposition : Prop :=
  ∀ Q : Measure (RWRS.Net 0), IsProbabilityMeasure Q → (∀ᵐ N ∂Q, RWRS.NetGood N) →
    RWRS.IsStationaryNet Q →
    ∃ K : RWRS.Net 0 → Measure (RWRS.Net 0),
      (∀ N, IsProbabilityMeasure (K N)) ∧
      (∀ A : Set (RWRS.Net 0), MeasurableSet A →
        Measurable[RWRS.invariantSigma 0] fun N => K N A) ∧
      (∀ A : Set (RWRS.Net 0), MeasurableSet A →
        ∀ B : Set (RWRS.Net 0), MeasurableSet[RWRS.invariantSigma 0] B →
          (∫⁻ N in B, K N A ∂Q) = Q (A ∩ B)) ∧
      (∀ᵐ N ∂Q, (∀ᵐ M ∂(K N), RWRS.NetGood M) ∧
        RWRS.IsStationaryNet (K N) ∧ RWRS.IsErgodicNet (K N))
-- FROZEN-STATEMENT-END
