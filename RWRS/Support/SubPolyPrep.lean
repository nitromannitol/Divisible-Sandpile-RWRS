/-
Four preliminaries for `prop:poly-growth` and for `thm:stab`.

The first turns a finite mean odometer at every vertex into almost sure
stabilization, which is how `thm:stab`(i) reads "in particular
`P(σ stabilizes) = 1`".  The second produces the level `M_0` of the proposition,
a level the marginal charges.  The third is the positive probability of the
scenery event of Step 1: the event that the field stays below a prescribed level
at every site has positive probability as soon as the tail masses above those
levels are summable to less than one.  The fourth moves the volume growth
hypothesis `H1` from the vertex it is stated at to every other vertex, at the
cost of a larger constant, which is what turns the conclusion at one vertex into
stabilization everywhere.
-/
import RWRS.Support.SubStab

namespace RWRS.Support

open MeasureTheory
open scoped ENNReal

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

/-- **A finite mean odometer at every vertex gives almost sure stabilization.** -/
theorem measure_stabilizes_eq_one_of_lintegral [Countable V]
    (hG : G.Connected) (μ : Measure (V → ℝ)) [IsProbabilityMeasure μ]
    (h : ∀ v : V, (∫⁻ σ, RWRS.odometerLimit G σ v ∂μ) ≠ ⊤) :
    μ {σ : V → ℝ | RWRS.Stabilizes G σ} = 1 := by
  have hmeas : MeasurableSet {σ : V → ℝ | RWRS.Stabilizes G σ} := measurableSet_stabilizes hG
  have hae : ∀ᵐ σ ∂μ, RWRS.Stabilizes G σ := by
    refine (MeasureTheory.ae_all_iff).2 fun v => ?_
    have h1 : ∀ᵐ σ ∂μ, RWRS.odometerLimit G σ v < ⊤ :=
      MeasureTheory.ae_lt_top (measurable_odometerLimit v) (h v)
    filter_upwards [h1] with σ hσ
    exact ne_of_lt hσ
  have hz : μ {σ : V → ℝ | RWRS.Stabilizes G σ}ᶜ = 0 := MeasureTheory.ae_iff.1 hae
  have hcompl : μ {σ : V → ℝ | RWRS.Stabilizes G σ}ᶜ
      = 1 - μ {σ : V → ℝ | RWRS.Stabilizes G σ} := by
    rw [MeasureTheory.measure_compl hmeas (measure_ne_top μ _), measure_univ]
  rw [hcompl] at hz
  exact le_antisymm prob_le_one (tsub_eq_zero_iff_le.1 hz)

/-- **A level the marginal charges.**  A probability measure on the line puts
positive mass on some half-line `(-∞, M]` with `M ≥ 1`. -/
theorem exists_level_pos (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    ∃ M : ℝ, 1 ≤ M ∧ 0 < ν (Set.Iic M) := by
  by_contra hcon
  push Not at hcon
  have hzero : ∀ n : ℕ, ν (Set.Iic ((n : ℝ) + 1)) = 0 := by
    intro n
    have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
    exact le_antisymm (hcon ((n : ℝ) + 1) h1) bot_le
  have hunion : (Set.univ : Set ℝ) = ⋃ n : ℕ, Set.Iic ((n : ℝ) + 1) := by
    ext x
    simp only [Set.mem_univ, Set.mem_iUnion, Set.mem_Iic, true_iff]
    obtain ⟨n, hn⟩ := exists_nat_ge x
    exact ⟨n, by linarith⟩
  have hu : ν (Set.univ : Set ℝ) = 0 := by
    rw [hunion]
    refine le_antisymm ?_ bot_le
    refine le_trans (MeasureTheory.measure_iUnion_le _) ?_
    simp [hzero]
  rw [MeasureTheory.measure_univ] at hu
  exact one_ne_zero hu

/-- **The scenery event of Step 1 has positive probability.**  If the tail masses
above the levels `t` sum to less than one, the field lies below `t` at every
site with positive probability. -/
theorem meas_forall_le_pos [Countable V] (ν : Measure ℝ) [IsProbabilityMeasure ν] (t : V → ℝ)
    (h : (∑' v : V, ν (Set.Ioi (t v))) < 1) :
    0 < RWRS.iidLaw V ν {ξ : V → ℝ | ∀ v, ξ v ≤ t v} := by
  haveI : IsProbabilityMeasure (RWRS.iidLaw V ν) := instIsProbabilityMeasureIid ν
  have hcompl : {ξ : V → ℝ | ∀ v, ξ v ≤ t v}ᶜ = ⋃ v : V, {ξ : V → ℝ | ξ v ∈ Set.Ioi (t v)} := by
    ext ξ
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_Ioi, not_forall,
      not_le]
  have hle : RWRS.iidLaw V ν {ξ : V → ℝ | ∀ v, ξ v ≤ t v}ᶜ ≤ ∑' v : V, ν (Set.Ioi (t v)) := by
    rw [hcompl]
    refine le_trans (MeasureTheory.measure_iUnion_le _) ?_
    exact ENNReal.tsum_le_tsum fun v => le_of_eq (meas_coord v measurableSet_Ioi)
  have hlt : RWRS.iidLaw V ν {ξ : V → ℝ | ∀ v, ξ v ≤ t v}ᶜ < 1 := lt_of_le_of_lt hle h
  by_contra hzero
  push Not at hzero
  have h0 : RWRS.iidLaw V ν {ξ : V → ℝ | ∀ v, ξ v ≤ t v} = 0 := le_antisymm hzero bot_le
  have huniv : RWRS.iidLaw V ν (Set.univ : Set (V → ℝ)) ≤
      RWRS.iidLaw V ν {ξ : V → ℝ | ∀ v, ξ v ≤ t v}
        + RWRS.iidLaw V ν {ξ : V → ℝ | ∀ v, ξ v ≤ t v}ᶜ := by
    rw [← Set.union_compl_self {ξ : V → ℝ | ∀ v, ξ v ≤ t v}]
    exact MeasureTheory.measure_union_le _ _
  rw [MeasureTheory.measure_univ, h0, zero_add] at huniv
  exact absurd huniv (not_le.2 hlt)

omit [G.LocallyFinite] in
/-- **The volume growth hypothesis moves between vertices.**  Polynomial volume
growth at one vertex of a connected graph is polynomial volume growth at every
vertex, with a larger constant. -/
theorem volumeGrowthUpper_shift (hG : G.Connected) {o : V} {C d_f : ℝ} (hC : 0 ≤ C)
    (hdf : 0 ≤ d_f) (h : RWRS.VolumeGrowthUpper G o C d_f) (v : V) :
    ∃ C' : ℝ, 0 ≤ C' ∧ RWRS.VolumeGrowthUpper G v C' d_f := by
  have hreach : G.Reachable v o := hG.preconnected v o
  have hne : G.edist v o ≠ ⊤ := SimpleGraph.edist_ne_top_iff_reachable.2 hreach
  set D : ℕ := (G.edist v o).toNat with hD
  have hDcast : (D : ℕ∞) = G.edist v o := ENat.coe_toNat hne
  refine ⟨C * (1 + (D : ℝ)) ^ d_f, by positivity, ?_⟩
  intro r hr
  have hsub : RWRS.closedBall G v r ⊆ RWRS.closedBall G o (r + D) := by
    intro w hw
    have hw' : G.edist w v ≤ (r : ℕ∞) := hw
    have htri : G.edist w o ≤ G.edist w v + G.edist v o := SimpleGraph.edist_triangle
    have hfin : G.edist w o ≤ (r : ℕ∞) + (D : ℕ∞) := by
      rw [hDcast]
      exact le_trans htri (add_le_add hw' le_rfl)
    have hgoal : G.edist w o ≤ ((r + D : ℕ) : ℕ∞) := by
      rw [Nat.cast_add]
      exact hfin
    exact hgoal
  have hr1 : 1 ≤ r + D := by omega
  have hball := h (r + D) hr1
  have hmono0 : (RWRS.closedBall G v r).encard ≤ (RWRS.closedBall G o (r + D)).encard :=
    Set.encard_mono hsub
  have hmono : ((RWRS.closedBall G v r).encard : ℝ≥0∞)
      ≤ ((RWRS.closedBall G o (r + D)).encard : ℝ≥0∞) := by exact_mod_cast hmono0
  refine le_trans hmono (le_trans hball (ENNReal.ofReal_le_ofReal ?_))
  have hrR : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hDR : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg D
  have hstep : ((r + D : ℕ) : ℝ) ≤ (1 + (D : ℝ)) * (r : ℝ) := by
    push_cast
    nlinarith
  have hpow : ((r + D : ℕ) : ℝ) ^ d_f ≤ ((1 + (D : ℝ)) * (r : ℝ)) ^ d_f :=
    Real.rpow_le_rpow (by positivity) hstep hdf
  have hsplit : ((1 + (D : ℝ)) * (r : ℝ)) ^ d_f = (1 + (D : ℝ)) ^ d_f * (r : ℝ) ^ d_f :=
    Real.mul_rpow (by positivity) (by positivity)
  rw [hsplit] at hpow
  have hrp : (0:ℝ) ≤ (r : ℝ) ^ d_f := Real.rpow_nonneg (by linarith) d_f
  nlinarith [hpow, hC, hrp]

/-- **`thm:stab`(i), second clause**: on a bounded-degree graph a subcritical
mass with a finite moment of order `p > 3` stabilizes almost surely. -/
theorem measure_stabilizes_eq_one_part_one [Infinite V] [MeasurableSpace V]
    [MeasurableSingletonClass V] [Countable V] [DecidableEq V] (hG : G.Connected)
    (hVBE : RWRS.External.VonBahrEsseen) (hFNt : RWRS.External.FukNagaevTail)
    (d : ℕ) (hbd : RWRS.BoundedDegree G d) {A : ℝ}
    (hsp : RWRS.SpectralDimensionBound G 1 A)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hmean : RWRS.extMean ν < 1)
    {p : ℝ} (hp : 3 < p) (hmom : RWRS.posMoment ν p ≠ ⊤) :
    RWRS.iidLaw V ν {σ : V → ℝ | RWRS.Stabilizes G σ} = 1 := by
  haveI : IsProbabilityMeasure (RWRS.iidLaw V ν) := instIsProbabilityMeasureIid ν
  have hq2 : (1:ℝ) < (p - 1) / 2 := by
    rw [lt_div_iff₀ (by norm_num : (0:ℝ) < 2)]
    linarith
  have hbig := lintegral_odometerLimit_rpow_ne_top (G := G) hG hVBE hFNt d hbd hsp ν hmean
    hp hmom (q := 1) le_rfl hq2
  refine measure_stabilizes_eq_one_of_lintegral hG (RWRS.iidLaw V ν) fun v => ?_
  refine ne_top_of_le_ne_top hbig ?_
  refine le_trans (le_of_eq ?_) (le_iSup (fun w : V =>
    ∫⁻ σ, RWRS.odometerLimit G σ w ^ (1:ℝ) ∂(RWRS.iidLaw V ν)) v)
  exact lintegral_congr fun σ => (ENNReal.rpow_one _).symm

end RWRS.Support
