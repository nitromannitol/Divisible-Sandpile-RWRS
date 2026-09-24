/-
The stabilization half of `thm:OS` on a bounded-degree graph: the universal heat
kernel bound gives the spectral dimension `d_s = 1`, at which the subcritical
moment estimate reads `p > 3` and `q < (p-1)/2`.
-/
import RWRS.Frozen.Subcritical
import RWRS.External.HeatKernelBoundedDegree
import RWRS.Support.Green

namespace RWRS.Support

open MeasureTheory
open scoped ENNReal

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

/-- **The moments of the running payoff of a subcritical scenery are finite** on
a bounded-degree graph. -/
theorem lintegral_supPayoff_rpow_ne_top_boundedDegree [Infinite V] [MeasurableSpace V]
    [MeasurableSingletonClass V]
    (hVBE : RWRS.External.VonBahrEsseen) (hFN : RWRS.External.FukNagaevTail)
    (hHK : RWRS.External.HeatKernelBoundedDegree G)
    (hG : G.Connected) (d : ℕ) (hd : RWRS.BoundedDegree G d)
    (ν : Measure ℝ) (hν : IsProbabilityMeasure ν) (hdet : RWRS.HasExtMean ν)
    (hmean : RWRS.extMean ν < 0) (p : ℝ) (hp : 3 < p) (hmom : RWRS.posMoment ν p ≠ ⊤)
    (q : ℝ) (hq1 : 1 ≤ q) (hq2 : q < (p - 1) / 2) (x : V) :
    (∫⁻ z, RWRS.supPayoff G z.1 z.2 ^ q ∂(RWRS.jointLaw G ν x)) ≠ ⊤ := by
  have hdeg : ∀ v : V, 1 ≤ G.degree v := fun v => degree_pos hG v
  have hd1 : 1 ≤ d := le_trans (hdeg (Classical.arbitrary V)) (hd _)
  obtain ⟨A, hA0, hsp⟩ := hHK d hd1 hd
  have hpds : 1 + 2 / (1 : ℝ) < p := by norm_num; linarith
  have hqds : q < (p - 1) * min ((1 : ℝ) / 2) 1 := by
    rw [show min ((1 : ℝ) / 2) 1 = 1 / 2 by norm_num]
    linarith
  have hsub := (RWRS.Frozen.subcritical hVBE hFN hG d hd 1 A one_pos hsp ν hν hdet hmean p
    hpds hmom).1 q hq1 hqds
  refine ne_top_of_le_ne_top hsub ?_
  exact le_iSup (fun y : V => ∫⁻ z, RWRS.supPayoff G z.1 z.2 ^ q ∂(RWRS.jointLaw G ν y)) x

end RWRS.Support
