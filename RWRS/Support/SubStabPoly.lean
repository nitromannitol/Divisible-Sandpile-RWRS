/-
Stabilization for subcritical masses under rooted polynomial volume growth.

The bounded-degree heat-kernel estimate gives spectral dimension one.
The pointwise Carne--Varopoulos estimate and volume growth at the starting
vertex give a stretched-exponential exit estimate at radii
`ceil(N^(1/2+s))`, `s > 0`. The polynomial-growth Support argument then has
moment threshold `max(d_f,1) = d_f`. Volume growth transfers to every other
vertex with a vertex-dependent constant, giving stabilization everywhere.
-/
import RWRS.Support.SubPolyFinal
import RWRS.Support.SubPolyPrep
import RWRS.External.HeatKernelBoundedDegree
import RWRS.External.CarneVaropoulos
import RWRS.Support.DisplacementAtOrigin

namespace RWRS.Support

open MeasureTheory
open scoped ENNReal

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

/-- **`thm:stab`(ii)**: a subcritical mass with a finite moment of order
`p > d_f` stabilizes almost surely on a bounded-degree graph of polynomial
volume growth of exponent `d_f ≥ 1`. -/
theorem measure_stabilizes_eq_one_part_two [Infinite V] [MeasurableSpace V]
    [MeasurableSingletonClass V] [Countable V] (hG : G.Connected)
    (hHK : RWRS.External.HeatKernelBoundedDegree G)
    (hCV : RWRS.External.CarneVaropoulos G)
    (d : ℕ) (hbd : RWRS.BoundedDegree G d)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hmean : RWRS.extMean ν < 1)
    (o : V) {C d_f : ℝ} (hC : 0 < C) (hdf : 1 ≤ d_f)
    (hH1 : RWRS.VolumeGrowthUpper G o C d_f)
    {p : ℝ} (hp : d_f < p) (hmom : RWRS.posMoment ν p ≠ ⊤) :
    RWRS.iidLaw V ν {σ : V → ℝ | RWRS.Stabilizes G σ} = 1 := by
  classical
  have hdeg : ∀ v : V, 1 ≤ G.degree v := fun v => degree_pos_of_connected hG v
  have hd1 : 1 ≤ d := le_trans (hdeg o) (hbd o)
  obtain ⟨A, hA0, hsp⟩ := hHK d hd1 hbd
  set ν' : Measure ℝ := ν.map (fun z : ℝ => z - 1) with hν'
  haveI : IsProbabilityMeasure ν' :=
    Measure.isProbabilityMeasure_map (measurable_id.sub_const 1).aemeasurable
  have hmean' : RWRS.extMean ν' < 0 := extMean_map_sub_one_lt ν hmean
  have hdf0 : (0:ℝ) < d_f := lt_of_lt_of_le zero_lt_one hdf
  have hp1 : (1:ℝ) ≤ p := le_trans hdf hp.le
  have hmom' : RWRS.posMoment ν' p ≠ ⊤ :=
    ne_top_of_le_ne_top hmom (posMoment_map_sub_one_le ν (by linarith))
  have hpmax : max (2 * d_f / (2 * 1)) 1 < p := by
    rw [max_lt_iff]
    refine ⟨?_, by linarith⟩
    have hval : 2 * d_f / (2 * (1:ℝ)) = d_f := by ring
    rw [hval]
    exact hp
  refine measure_stabilizes_eq_one_of_ae_supStopValue hG ν fun v => ?_
  obtain ⟨C', hC'0, hH1'⟩ := volumeGrowthUpper_shift hG hC.le (by linarith) hH1 v
  have hExit : PolynomialExitBoundAt G v 2 :=
    polynomialExitBoundAt_of_pointwise hG hdeg d hbd v hC'0 hdf0.le hH1'
      (hCV inferInstance inferInstance hG v)
  exact ae_supStopValue_ne_top_poly_of_exit hG d hbd hdf0 v hH1' (by norm_num : (0:ℝ) < 1)
    (by norm_num : (1:ℝ) < 2) hsp (le_refl (2:ℝ)) hExit ν' hmean' hpmax hmom'

end RWRS.Support
