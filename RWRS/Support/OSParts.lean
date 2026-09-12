/-
The two explosion halves of `thm:OS`, in the form the theorem applies them.
-/
import RWRS.Support.DTVariance
import RWRS.Support.ClockRatio
import RWRS.Support.DTTrapBall
import RWRS.Frozen.DoublyTransient
import RWRS.Frozen.Critical
import RWRS.Frozen.Supercritical
import RWRS.Support.ErgProp
import RWRS.Support.Convexity
import RWRS.Support.HeatBasic

namespace RWRS.Support

open MeasureTheory Filter
open scoped ENNReal Topology

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

/-- **A deterministic time is a bounded stopping time**, so the value over
deterministic times is below the value over bounded stopping times. -/
theorem supMeanPayoff_le_supStopValue (ξ : V → ℝ) (x : V) :
    RWRS.supMeanPayoff G ξ x ≤ RWRS.supStopValue G ξ x := by
  refine iSup_le fun n => ?_
  have hmem : RWRS.meanPayoff G ξ n x ∈ RWRS.stopValues G ξ n x :=
    ⟨fun _ => n, fun k X Y _ h => h, fun _ => le_rfl, rfl⟩
  exact le_iSup_of_le n (le_iSup_of_le _ (le_iSup_of_le hmem le_rfl))

/-- **Double transience implies transience.** -/
theorem green_diag_ne_top_of_doublyTransient (hdt : RWRS.DoublyTransient G) (o : V) :
    RWRS.green G o o ≠ ⊤ := by
  intro htop
  refine hdt o ?_
  refine top_le_iff.1 ?_
  refine le_trans (le_of_eq ?_) (ENNReal.le_tsum o)
  rw [htop]
  simp

/-- **The partial Green functions increase to the Green function.** -/
theorem iSup_ofReal_greenTime (hdeg : ∀ v : V, 0 < G.degree v) (o v : V) :
    (⨆ n : ℕ, ENNReal.ofReal (RWRS.greenTime G n o v)) = RWRS.green G o v := by
  have hd : (0 : ℝ) < G.degree v := by exact_mod_cast hdeg v
  have hpt : ∀ n : ℕ, ENNReal.ofReal (RWRS.greenTime G n o v)
      = (∑ k ∈ Finset.range n, ENNReal.ofReal (RWRS.heat G k o v))
        / (G.degree v : ℝ≥0∞) := by
    intro n
    rw [RWRS.greenTime, RWRS.meanLocalTime, ENNReal.ofReal_div_of_pos hd,
      ENNReal.ofReal_sum_of_nonneg (fun k _ => heat_nonneg k o v), ENNReal.ofReal_natCast]
  rw [iSup_congr hpt, ← ENNReal.iSup_div, ← ENNReal.tsum_eq_iSup_nat]
  rfl

/-- **The partial Green function increases with the horizon.** -/
theorem greenTime_mono (hdeg : ∀ v : V, 0 < G.degree v) (o v : V) :
    Monotone fun n : ℕ => RWRS.greenTime G n o v := by
  intro m n hmn
  have hd : (0 : ℝ) < G.degree v := by exact_mod_cast hdeg v
  show RWRS.greenTime G m o v ≤ RWRS.greenTime G n o v
  rw [RWRS.greenTime, RWRS.greenTime, RWRS.meanLocalTime, RWRS.meanLocalTime]
  refine div_le_div_of_nonneg_right ?_ hd.le
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hmn)
    (fun k _ _ => heat_nonneg k o v)

/-- **The fluctuation increases with the horizon.** -/
theorem monotone_fluct (hdeg : ∀ v : V, 0 < G.degree v) (o : V) :
    Monotone fun n : ℕ => RWRS.fluct G n o := by
  intro m n hmn
  exact ENNReal.tsum_le_tsum fun v => ENNReal.ofReal_le_ofReal
    (pow_le_pow_left₀ (greenTime_nonneg m o v) (greenTime_mono hdeg o v hmn) 2)

/-- **A monotone supremum commutes with a sum.** -/
theorem tsum_iSup_comm_of_monotone {f : ℕ → V → ℝ≥0∞} (hf : ∀ v, Monotone fun n => f n v) :
    (∑' v : V, ⨆ n : ℕ, f n v) = ⨆ n : ℕ, ∑' v : V, f n v := by
  refine le_antisymm ?_ ?_
  · rw [ENNReal.tsum_eq_iSup_sum]
    refine iSup_le fun S => ?_
    rw [ENNReal.finsetSum_iSup_of_monotone (fun v => hf v)]
    exact iSup_le fun n => le_iSup_of_le n (ENNReal.sum_le_tsum S)
  · refine iSup_le fun n => ENNReal.tsum_le_tsum fun v => le_iSup (fun m => f m v) n

/-- **The square of a monotone supremum.** -/
theorem sq_iSup_of_monotone {a : ℕ → ℝ≥0∞} (ha : Monotone a) :
    (⨆ n, a n) ^ 2 = ⨆ n, (a n) ^ 2 := by
  refine le_antisymm ?_ (iSup_le fun n => pow_le_pow_left' (le_iSup a n) 2)
  rw [pow_two, ENNReal.iSup_mul]
  refine iSup_le fun i => ?_
  rw [ENNReal.mul_iSup]
  refine iSup_le fun j => ?_
  refine le_trans ?_ (le_iSup (fun n => (a n) ^ 2) (max i j))
  rw [pow_two]
  exact mul_le_mul' (ha (le_max_left i j)) (ha (le_max_right i j))

/-- **The fluctuations increase to the square Green sum.** -/
theorem iSup_fluct_eq_greenSq (hdeg : ∀ v : V, 0 < G.degree v) (o : V) :
    (⨆ n : ℕ, RWRS.fluct G n o) = greenSq G o := by
  have hsq : ∀ (n : ℕ) (v : V), ENNReal.ofReal (RWRS.greenTime G n o v ^ 2)
      = (ENNReal.ofReal (RWRS.greenTime G n o v)) ^ 2 := by
    intro n v
    rw [pow_two, pow_two, ENNReal.ofReal_mul (greenTime_nonneg n o v)]
  have hf : ∀ n : ℕ, RWRS.fluct G n o
      = ∑' v : V, (ENNReal.ofReal (RWRS.greenTime G n o v)) ^ 2 := by
    intro n
    exact tsum_congr fun v => hsq n v
  have hmono : ∀ v : V, Monotone fun n : ℕ => (ENNReal.ofReal (RWRS.greenTime G n o v)) ^ 2 := by
    intro v m n hmn
    exact pow_le_pow_left' (ENNReal.ofReal_le_ofReal (greenTime_mono hdeg o v hmn)) 2
  calc (⨆ n : ℕ, RWRS.fluct G n o)
      = ⨆ n : ℕ, ∑' v : V, (ENNReal.ofReal (RWRS.greenTime G n o v)) ^ 2 := by
        exact iSup_congr hf
    _ = ∑' v : V, ⨆ n : ℕ, (ENNReal.ofReal (RWRS.greenTime G n o v)) ^ 2 :=
        (tsum_iSup_comm_of_monotone hmono).symm
    _ = ∑' v : V, (RWRS.green G o v) ^ 2 := by
        refine tsum_congr fun v => ?_
        rw [← sq_iSup_of_monotone (a := fun n : ℕ => ENNReal.ofReal (RWRS.greenTime G n o v))
          (fun m n hmn => ENNReal.ofReal_le_ofReal (greenTime_mono hdeg o v hmn)),
          iSup_ofReal_greenTime hdeg o v]
    _ = greenSq G o := rfl

/-- **Without double transience the fluctuation diverges at some vertex.** -/
theorem exists_tendsto_fluct_top_of_not_doublyTransient (hdeg : ∀ v : V, 0 < G.degree v)
    (hdt : ¬ RWRS.DoublyTransient G) :
    ∃ o : V, Tendsto (fun n : ℕ => RWRS.fluct G n o) atTop (𝓝 ⊤) := by
  rw [RWRS.DoublyTransient] at hdt
  push Not at hdt
  obtain ⟨o, ho⟩ := hdt
  refine ⟨o, ?_⟩
  have hsup : (⨆ n : ℕ, RWRS.fluct G n o) = ⊤ := by
    rw [iSup_fluct_eq_greenSq hdeg o]
    exact ho
  rw [← hsup]
  exact tendsto_atTop_iSup (monotone_fluct hdeg o)

/-- **A vertex at which every centred scenery of positive finite variance
explodes.**  On a bounded-degree graph either the graph is doubly transient, and
then the trap selection explodes at every vertex, or it is not, and then the
fluctuation diverges at some vertex and the critical estimate explodes there. -/
theorem exists_vertex_explosion [Infinite V] (hES : RWRS.External.EfronStein V)
    (hVF : RWRS.External.VoltageFunction G) (hG : G.Connected)
    (d : ℕ) (hd0 : 0 < d) (hd : RWRS.BoundedDegree G d) :
    ∃ o : V, ∀ ρ : Measure ℝ, IsProbabilityMeasure ρ → RWRS.extMean ρ = 0 →
      0 < RWRS.evar ρ → RWRS.evar ρ < ⊤ →
      ∀ᵐ ξ ∂(RWRS.iidLaw V ρ), RWRS.supStopValue G ξ o = ⊤ := by
  have hdeg : ∀ v : V, 0 < G.degree v := fun v => degree_pos hG v
  by_cases hdt : RWRS.DoublyTransient G
  · refine ⟨Classical.arbitrary V, fun ρ hρ hmean hvar hsq => ?_⟩
    exact RWRS.Frozen.doublyTransient hG (green_diag_ne_top_of_doublyTransient hdt) hdt
      (uniformLocalTrap_of_boundedDegree d hd0 hd hdeg) ρ hρ hmean hvar hsq _
  · obtain ⟨o, hfl⟩ := exists_tendsto_fluct_top_of_not_doublyTransient hdeg hdt
    refine ⟨o, fun ρ hρ hmean hvar hsq => ?_⟩
    obtain ⟨c₁, c₂, _, _, hcrit⟩ := (RWRS.Frozen.critical hES hVF hG ρ hρ hmean hvar hsq).2
    have hmp := (hcrit o hfl).2
    filter_upwards [hmp] with ξ hξ
    refine top_le_iff.1 ?_
    rw [← hξ]
    exact supMeanPayoff_le_supStopValue ξ o

/-- **An infinite optimal stopping value at one vertex is infinite at every
vertex**: it says that the configuration does not stabilize, and then the
odometer is infinite everywhere. -/
theorem supStopValue_top_everywhere [Infinite V] (hG : G.Connected) {ξ : V → ℝ} {o : V}
    (h : RWRS.supStopValue G ξ o = ⊤) (x : V) : RWRS.supStopValue G ξ x = ⊤ := by
  rw [supStopValue_eq_odometerLimit hG] at h ⊢
  refine odometerLimit_eq_top_of_not_stabilizes hG _ (fun hs => ?_) x
  exact hs o h

/-- **Every vertex explodes** for a centred scenery of positive finite variance
on a bounded-degree graph. -/
theorem explosion_of_mean_zero [Infinite V] (hES : RWRS.External.EfronStein V)
    (hVF : RWRS.External.VoltageFunction G) (hG : G.Connected)
    (d : ℕ) (hd0 : 0 < d) (hd : RWRS.BoundedDegree G d)
    (ν : Measure ℝ) (hν : IsProbabilityMeasure ν) (hmean : RWRS.extMean ν = 0)
    (hvar : 0 < RWRS.evar ν) (hsq : RWRS.evar ν < ⊤) (x : V) :
    ∀ᵐ ξ ∂(RWRS.iidLaw V ν), RWRS.supStopValue G ξ x = ⊤ := by
  obtain ⟨o, ho⟩ := exists_vertex_explosion hES hVF hG d hd0 hd
  filter_upwards [ho ν hν hmean hvar hsq] with ξ hξ
  exact supStopValue_top_everywhere hG hξ x

/-- **The Green functions at two vertices are comparable**, with a constant
depending only on the two vertices. -/
theorem exists_green_ge [Infinite V] (hG : G.Connected) (x o : V) :
    ∃ c : ℝ≥0∞, 0 < c ∧ ∀ v : V, c * RWRS.green G o v ≤ RWRS.green G x v := by
  obtain ⟨p⟩ := hG.preconnected x o
  set r := p.length with hr
  have hc : 0 < RWRS.heat G r x o := heat_pos_of_walk hG p
  refine ⟨ENNReal.ofReal (RWRS.heat G r x o), ENNReal.ofReal_pos.2 hc, fun v => ?_⟩
  have hstep : ∀ k : ℕ,
      ENNReal.ofReal (RWRS.heat G r x o) * ENNReal.ofReal (RWRS.heat G k o v)
        ≤ ENNReal.ofReal (RWRS.heat G (r + k) x v) := by
    intro k
    rw [← ENNReal.ofReal_mul (heat_nonneg _ x o)]
    exact ENNReal.ofReal_le_ofReal (heat_ge_mul hG r k x o v)
  have hsum : ENNReal.ofReal (RWRS.heat G r x o) * (∑' k : ℕ, ENNReal.ofReal (RWRS.heat G k o v))
      ≤ ∑' k : ℕ, ENNReal.ofReal (RWRS.heat G k x v) := by
    rw [← ENNReal.tsum_mul_left]
    refine le_trans (ENNReal.tsum_le_tsum hstep) ?_
    exact ENNReal.tsum_comp_le_tsum_of_injective (add_right_injective r)
      (fun k => ENNReal.ofReal (RWRS.heat G k x v))
  rw [green_eq_div, green_eq_div, ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul,
    ← mul_assoc, mul_comm (ENNReal.ofReal (RWRS.heat G r x o)) ((G.degree v : ℝ≥0∞))⁻¹,
    mul_assoc]
  exact mul_le_mul_right hsum _

/-- **An infinite square Green sum at one vertex is infinite at every
vertex.** -/
theorem greenSq_eq_top_everywhere [Infinite V] (hG : G.Connected) {o : V}
    (ho : greenSq G o = ⊤) (x : V) : greenSq G x = ⊤ := by
  obtain ⟨c, hc, hle⟩ := exists_green_ge hG x o
  refine top_le_iff.1 ?_
  have h1 : c ^ 2 * greenSq G o ≤ greenSq G x := by
    rw [greenSq, greenSq, ← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun v => ?_
    calc c ^ 2 * RWRS.green G o v ^ 2 = (c * RWRS.green G o v) ^ 2 := by rw [mul_pow]
      _ ≤ RWRS.green G x v ^ 2 := pow_le_pow_left' (hle v) 2
  rw [ho, ENNReal.mul_top (by positivity)] at h1
  exact h1

/-- **Without double transience the fluctuation diverges at every vertex.** -/
theorem tendsto_fluct_top_of_not_doublyTransient [Infinite V] (hG : G.Connected)
    (hdeg : ∀ v : V, 0 < G.degree v) (hdt : ¬ RWRS.DoublyTransient G) (x : V) :
    Tendsto (fun n : ℕ => RWRS.fluct G n x) atTop (𝓝 ⊤) := by
  rw [RWRS.DoublyTransient] at hdt
  push Not at hdt
  obtain ⟨o, ho⟩ := hdt
  have hsup : (⨆ n : ℕ, RWRS.fluct G n x) = ⊤ := by
    rw [iSup_fluct_eq_greenSq hdeg x]
    exact greenSq_eq_top_everywhere hG (o := o) ho x
  rw [← hsup]
  exact tendsto_atTop_iSup (monotone_fluct hdeg x)

end RWRS.Support
