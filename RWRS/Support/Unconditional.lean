/-
Corollaries of the paper's statements with every cited input discharged by a
proved companion. Each corollary retains the other hypotheses of its frozen
statement.
-/
import RWRS.External.BernsteinProved
import RWRS.External.FukNagaevTailProved
import RWRS.External.HeatKernelVanishingProved
import RWRS.External.VonBahrEsseenProved
import RWRS.Frozen.ClockNoDominance
import RWRS.Frozen.ErgodicMarked
import RWRS.Frozen.FukNagaev
import RWRS.Frozen.NoDominance
import RWRS.Frozen.Subcritical

open MeasureTheory Filter Topology
open scoped ENNReal

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

/-- Tail inequalities for independent sums, `rwrs.tex:1077-1095`. -/
theorem RWRS.fukNagaev_unconditional :
    (∀ p : ℝ, 1 ≤ p → p ≤ 2 → ∃ Cp : ℝ, 0 < Cp ∧
      ∀ {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι] (P : Measure Ω), IsProbabilityMeasure P →
        ∀ (Y : ι → Ω → ℝ), ProbabilityTheory.iIndepFun Y P → (∀ i, Integrable (Y i) P) →
        (∀ i, ∫ ω, Y i ω ∂P = 0) →
        ∀ Mp : ℝ, Mp = ∑ i, (∫⁻ ω, ENNReal.ofReal (|Y i ω| ^ p) ∂P).toReal →
          (∀ i, (∫⁻ ω, ENNReal.ofReal (|Y i ω| ^ p) ∂P) ≠ ⊤) →
          ∀ t : ℝ, 0 < t →
            P {ω | t ≤ |∑ i, Y i ω|} ≤ ENNReal.ofReal (Cp * Mp / t ^ p)) ∧
    (∀ p : ℝ, 2 ≤ p → ∃ c Cp : ℝ, 0 < c ∧ 0 < Cp ∧
      ∀ {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι] (P : Measure Ω), IsProbabilityMeasure P →
        ∀ (Y : ι → Ω → ℝ), ProbabilityTheory.iIndepFun Y P → (∀ i, Integrable (Y i) P) →
        (∀ i, ∫ ω, Y i ω ∂P = 0) →
        ∀ Mp B : ℝ, Mp = ∑ i, (∫⁻ ω, ENNReal.ofReal (|Y i ω| ^ p) ∂P).toReal →
          (∀ i, (∫⁻ ω, ENNReal.ofReal (|Y i ω| ^ p) ∂P) ≠ ⊤) →
          0 < B → B ^ 2 = ∑ i, ∫ ω, Y i ω ^ 2 ∂P → (∀ i, Integrable (fun ω => Y i ω ^ 2) P) →
          ∀ t : ℝ, 0 < t →
            P {ω | t ≤ |∑ i, Y i ω|}
              ≤ ENNReal.ofReal (Cp * Mp / t ^ p + 2 * Real.exp (-c * t ^ 2 / B ^ 2))) ∧
    (∀ {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι] (P : Measure Ω), IsProbabilityMeasure P →
      ∀ (Y : ι → Ω → ℝ), ProbabilityTheory.iIndepFun Y P → (∀ i, Integrable (Y i) P) →
      (∀ i, ∫ ω, Y i ω ∂P = 0) →
      ∀ M B : ℝ, 0 < M → 0 < B → (∀ i, ∀ᵐ ω ∂P, |Y i ω| ≤ M) →
        B ^ 2 = ∑ i, ∫ ω, Y i ω ^ 2 ∂P → (∀ i, Integrable (fun ω => Y i ω ^ 2) P) →
        ∀ t : ℝ, 0 < t →
          P {ω | t ≤ |∑ i, Y i ω|}
            ≤ ENNReal.ofReal (2 * Real.exp (-(t ^ 2 / 2) / (B ^ 2 + M * t / 3)))) := by
  exact RWRS.Frozen.fukNagaev RWRS.External.vonBahrEsseen
    RWRS.External.fukNagaevTail RWRS.External.bernstein

/-- The clock non-dominance limits, `rwrs.tex:531-536`. -/
theorem RWRS.clockNoDominance_unconditional
    [Infinite V] (hG : G.Connected) (x : V)
    (hA : Tendsto (fun n : ℕ => RWRS.clock G n x) atTop atTop) :
    Tendsto (fun n : ℕ => RWRS.supGreenTime G n x / ENNReal.ofReal (RWRS.clock G n x))
        atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => RWRS.fluct G n x / (ENNReal.ofReal (RWRS.clock G n x)) ^ 2)
        atTop (𝓝 0) := by
  exact RWRS.Frozen.clockNoDominance (RWRS.External.heatKernelVanishing_of_connected hG) hG x hA

/-- The fluctuation non-dominance limit, `rwrs.tex:629-632`. -/
theorem RWRS.noDominance_unconditional
    [Infinite V] (hG : G.Connected) (o : V)
    (hSigma : Tendsto (fun n : ℕ => RWRS.fluct G n o) atTop (𝓝 ⊤)) :
    Tendsto (fun n : ℕ => RWRS.supGreenTime G n o ^ 2 / RWRS.fluct G n o) atTop (𝓝 0) := by
  exact RWRS.Frozen.noDominance (RWRS.External.heatKernelVanishing_of_connected hG) hG o hSigma

/-- Independent marking preserves stationarity and ergodicity, `rwrs.tex:310-312`. -/
theorem RWRS.ergodicMarked_unconditional
    (Q : Measure (RWRS.Net 0)) (hQ : IsProbabilityMeasure Q)
    (hgood : ∀ᵐ N ∂Q, RWRS.NetGood N) (hstat : RWRS.IsStationaryNet Q)
    (herg : RWRS.IsErgodicNet Q) (ν : Measure ℝ) (hν : IsProbabilityMeasure ν) :
    RWRS.IsStationaryNet (RWRS.markIid Q ν) ∧ RWRS.IsErgodicNet (RWRS.markIid Q ν) := by
  exact RWRS.Frozen.ergodicMarked
    RWRS.External.heatKernelVanishing_of_netGood Q hQ hgood hstat herg ν hν

/-- Subcritical moment and stopping-value bounds, `rwrs.tex:1155-1165`. -/
theorem RWRS.subcritical_unconditional [Infinite V] [MeasurableSpace V] [MeasurableSingletonClass V]
    (hG : G.Connected)
    (d : ℕ) (hd : RWRS.BoundedDegree G d) (d_s A : ℝ) (hds : 0 < d_s)
    (hspec : RWRS.SpectralDimensionBound G d_s A)
    (ν : Measure ℝ) (hν : IsProbabilityMeasure ν) (hdet : RWRS.HasExtMean ν)
    (hmean : RWRS.extMean ν < 0)
    (p : ℝ) (hp : 1 + 2 / d_s < p) (hmom : RWRS.posMoment ν p ≠ ⊤) :
    (∀ q : ℝ, 1 ≤ q → q < (p - 1) * min (d_s / 2) 1 →
      (⨆ x : V, ∫⁻ z, RWRS.supPayoff G z.1 z.2 ^ q ∂(RWRS.jointLaw G ν x)) ≠ ⊤) ∧
    (1 < (p - 1) * min (d_s / 2) 1 →
      ∀ x : V, ∀ᵐ ξ ∂(RWRS.iidLaw V ν), RWRS.supStopValue G ξ x ≠ ⊤) := by
  exact RWRS.Frozen.subcritical RWRS.External.vonBahrEsseen
    RWRS.External.fukNagaevTail hG d hd d_s A hds hspec ν hν hdet hmean p hp hmom
