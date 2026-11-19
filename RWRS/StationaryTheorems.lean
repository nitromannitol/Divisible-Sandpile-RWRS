import RWRS.Frozen.StationaryPhase
import RWRS.Support.ErgodicDecomposition

/-!
# Stationary random-network results

The stationary zero–one law and phase result follow without an ergodic
decomposition hypothesis, using the ergodic decomposition theorem.
-/

open MeasureTheory

/-- The stationary zero–one conclusion for the marked network law. -/
theorem RWRS.zeroOneStationary
    (Q : Measure (RWRS.Net 0)) (hQ : IsProbabilityMeasure Q)
    (hgood : ∀ᵐ N ∂Q, RWRS.NetGood N) (hstat : RWRS.IsStationaryNet Q)
    (ν : Measure ℝ) (hν : IsProbabilityMeasure ν) :
    ∀ᵐ N ∂(RWRS.markIid Q ν),
      (RWRS.markIid Q ν)[Set.indicator
          {M : RWRS.Net 1 | RWRS.Stabilizes (RWRS.netGraph M) (RWRS.netConfig M)}
          (fun _ => (1 : ℝ)) | RWRS.graphInvariantSigma 1] N = 0 ∨
      (RWRS.markIid Q ν)[Set.indicator
          {M : RWRS.Net 1 | RWRS.Stabilizes (RWRS.netGraph M) (RWRS.netConfig M)}
          (fun _ => (1 : ℝ)) | RWRS.graphInvariantSigma 1] N = 1 := by
  exact RWRS.Frozen.zeroOneStationary RWRS.External.ergodicDecomposition Q hQ hgood hstat ν hν

/-- The stationary phase conclusions for the marked network law. -/
theorem RWRS.stationaryPhase
    (Q : Measure (RWRS.Net 0)) (hQ : IsProbabilityMeasure Q)
    (hgood : ∀ᵐ N ∂Q, RWRS.NetGood N) (hstat : RWRS.IsStationaryNet Q)
    (ν : Measure ℝ) (hν : IsProbabilityMeasure ν) (hdet : RWRS.HasExtMean ν)
    (hint : Integrable (fun N => |RWRS.netWeightedMass N|) (RWRS.markIid Q ν)) :
    (1 < RWRS.extMean ν →
      RWRS.markIid Q ν
        {M : RWRS.Net 1 | RWRS.Stabilizes (RWRS.netGraph M) (RWRS.netConfig M)} = 0) ∧
    (RWRS.extMean ν < 1 →
      RWRS.markIid Q ν
        {M : RWRS.Net 1 | RWRS.Stabilizes (RWRS.netGraph M) (RWRS.netConfig M)} = 1) := by
  exact RWRS.Frozen.stationaryPhase RWRS.External.ergodicDecomposition Q hQ hgood hstat ν hν hdet hint
