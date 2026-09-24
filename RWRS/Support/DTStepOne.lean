/-
Step 1 of `prop:doubly-transient-really-general`: the annealed explosion.

Assembling the constants of the trap selection with the annealed conditional
estimate: for every level `m` the mean value at a suitable horizon is at least
`(9/2)m` minus a constant of the scenery law alone, so the annealed value is
infinite.
-/
import RWRS.Support.DTAnneal
import RWRS.Support.DTConstants
import RWRS.Support.DTLeave

open scoped Classical ENNReal
open MeasureTheory

namespace RWRS.Support

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]
  [DecidableEq V] [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] [Infinite V]

/-- **Step 1**: the annealed value at the root is infinite. -/
theorem lintegral_supStopValue_eq_top (hG : G.Connected)
    (hdt : RWRS.DoublyTransient G) (htrap : RWRS.UniformLocalTrap G)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (h0 : RWRS.extMean ν = 0)
    (hvar : 0 < RWRS.evar ν) (hsq : RWRS.evar ν < ⊤) (o : V) :
    (∫⁻ ξ, RWRS.supStopValue G ξ o ∂(RWRS.iidLaw V ν)) = ⊤ := by
  classical
  have hdeg : ∀ v : V, 0 < G.degree v := fun v => degree_pos hG v
  have hint : Integrable (fun z : ℝ => z) ν := integrable_id_of_extMean_zero h0
  have habs : Integrable (fun z : ℝ => |z|) ν := hint.abs
  obtain ⟨ε, hε, hmass⟩ := exists_eps_pos_mass (ν := ν) h0 hvar
  have hple : ν (Set.Iic (-ε)) ≤ 1 := prob_le_one
  have hpne : ν (Set.Iic (-ε)) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hple
  have hp1 : ν (Set.Iic (-ε)) < 1 := measure_Iic_lt_one h0 hε
  set q : ℝ := 1 - (ν (Set.Iic (-ε))).toReal with hqdef
  have hq : 0 < q := by
    have h : (ν (Set.Iic (-ε))).toReal < (1 : ℝ≥0∞).toReal :=
      ENNReal.toReal_strict_mono ENNReal.one_ne_top hp1
    rw [ENNReal.toReal_one] at h
    simp only [hqdef]
    linarith
  have hqof : ENNReal.ofReal q = 1 - ν (Set.Iic (-ε)) := by
    rw [hqdef, ENNReal.ofReal_sub _ ENNReal.toReal_nonneg, ENNReal.ofReal_one,
      ENNReal.ofReal_toReal hpne]
  -- an exhaustion of the graph by finite sets
  obtain ⟨e, he⟩ := exists_surjective_nat V
  set g : V → ℕ := fun y => Classical.choose (he y) with hgdef
  have hge : ∀ y, e (g y) = y := fun y => Classical.choose_spec (he y)
  set Kseq : ℕ → Finset V := fun j => (Finset.range j).image e with hKseq
  have hcof : ∀ S : Finset V, ∃ j, S ⊆ Kseq j := by
    intro S
    refine ⟨S.sup g + 1, fun y hy => ?_⟩
    refine Finset.mem_image.2 ⟨g y, Finset.mem_range.2 ?_, hge y⟩
    have := Finset.le_sup (f := g) hy
    omega
  -- the per-level bound
  have key : ∀ m : ℝ, 0 < m → (∫ z, |z| ∂ν) / q ≤ 8 * m →
      ENNReal.ofReal ((9 / 2) * m - (9 / 16) * ((∫ z, |z| ∂ν) / q) - 1)
        ≤ ∫⁻ ξ, RWRS.supStopValue G ξ o ∂(RWRS.iidLaw V ν) := by
    intro m hm hgain
    obtain ⟨r, M, C, hCfam⟩ := exists_trapFamily htrap (8 * m / ε) (by positivity)
    have hCself : ∀ y : V, y ∈ C y := fun y => (hCfam y).1
    have hCball : ∀ y : V, ((C y : Finset V) : Set V) ⊆ RWRS.closedBall G y r :=
      fun y => (hCfam y).2.1
    have hcard : ∀ y : V, (C y).card ≤ M := fun y => (hCfam y).2.2.1
    have hΘ : ∀ y : V, ENNReal.ofReal (8 * m / ε) ≤ RWRS.thetaExit G (C y : Set V) y :=
      fun y => (hCfam y).2.2.2.2
    have hcompl : ∀ y : V, ENNReal.ofReal q
        ≤ RWRS.iidLaw V ν ((trapEvent (C y) ε)ᶜ) := by
      intro y
      have hc1 : 1 ≤ (C y).card := Finset.card_pos.2 ⟨y, hCself y⟩
      have hmeas : RWRS.iidLaw V ν (trapEvent (C y) ε)
          = ν (Set.Iic (-ε)) ^ (C y).card := measure_trapEvent ν _ _
      have hle : ν (Set.Iic (-ε)) ^ (C y).card ≤ ν (Set.Iic (-ε)) := by
        calc ν (Set.Iic (-ε)) ^ (C y).card ≤ ν (Set.Iic (-ε)) ^ 1 :=
              pow_le_pow_right_of_le_one' hple hc1
          _ = ν (Set.Iic (-ε)) := pow_one _
      have hcomplEq : RWRS.iidLaw V ν ((trapEvent (C y) ε)ᶜ)
          = 1 - ν (Set.Iic (-ε)) ^ (C y).card := by
        rw [measure_compl (measurableSet_trapEvent _ _)
          (by rw [hmeas]; exact ENNReal.pow_ne_top hpne), hmeas, measure_univ]
      rw [hcomplEq, hqof]
      exact tsub_le_tsub_left hle 1
    -- the number of stages
    have hpM : ν (Set.Iic (-ε)) ^ M ≠ 0 := pow_ne_zero _ (ne_of_gt hmass)
    have hlt1 : 1 - ν (Set.Iic (-ε)) ^ M < 1 :=
      ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hpM
    obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℕ, (1 - ν (Set.Iic (-ε)) ^ M) ^ (ℓ + 1)
        ≤ ENNReal.ofReal (1 / 4) := by
      have htend := ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hlt1
      have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal (1 / 4) := by
        simp only [ENNReal.ofReal_pos]
        norm_num
      obtain ⟨n, hn⟩ := (htend.eventually (gt_mem_nhds hpos)).exists
      exact ⟨n, le_trans (pow_le_pow_right_of_le_one' (le_of_lt hlt1) (by omega)) (le_of_lt hn)⟩
    obtain ⟨K, hK⟩ := exists_K_walkEvent2_prob hG hdeg hdt r C hCself o ℓ Kseq hcof
    set Cbad : ℝ := (∑ v ∈ K, RWRS.killedGreenReal G (K : Set V) v v)
      * ((K.card : ℝ) * ∫ z, |z| ∂ν) with hCbaddef
    have hCbad0 : 0 ≤ Cbad := by
      refine mul_nonneg (Finset.sum_nonneg fun v _ => ENNReal.toReal_nonneg) ?_
      exact mul_nonneg (Nat.cast_nonneg _) (integral_nonneg fun z => abs_nonneg _)
    set δ : ℝ := 1 / (Cbad + 1) with hδdef
    have hδ : 0 < δ := by positivity
    obtain ⟨N, hN, hW, hEc⟩ := exists_N_walkGood hG hdeg r C o ℓ K hK hδ
    have hval := integral_value_ge hG hdeg ν h0 hint hsq r M ℓ C K hN ε o m hCball hCself
      hcard hΘ hε (le_of_lt hm) hq hcompl hℓ hgain hW hEc
    have hsmall : Cbad * δ ≤ 1 := by
      rw [hδdef]
      rw [mul_one_div]
      rw [div_le_one (by linarith)]
      linarith
    have hlow : (9 / 2) * m - (9 / 16) * ((∫ z, |z| ∂ν) / q) - 1
        ≤ ∫ ξ : V → ℝ, RWRS.value G ξ N o ∂(RWRS.iidLaw V ν) := by
      have hexp : (9 / 16 : ℝ) * (8 * m - (∫ z, |z| ∂ν) / q)
          = (9 / 2) * m - (9 / 16) * ((∫ z, |z| ∂ν) / q) := by ring
      rw [hexp] at hval
      linarith
    have hlint : ENNReal.ofReal (∫ ξ : V → ℝ, RWRS.value G ξ N o ∂(RWRS.iidLaw V ν))
        ≤ ∫⁻ ξ, RWRS.supStopValue G ξ o ∂(RWRS.iidLaw V ν) := by
      rw [← lintegral_ofReal_value hG (by infer_instance) h0 hsq N o,
        ← iSup_lintegral_ofReal_value hG o]
      exact le_iSup (fun n : ℕ => ∫⁻ ξ, ENNReal.ofReal (RWRS.value G ξ n o)
        ∂(RWRS.iidLaw V ν)) N
    exact le_trans (ENNReal.ofReal_le_ofReal hlow) hlint
  -- the levels are unbounded
  by_contra hne
  set L : ℝ≥0∞ := ∫⁻ ξ, RWRS.supStopValue G ξ o ∂(RWRS.iidLaw V ν) with hL
  set B : ℝ := (∫ z, |z| ∂ν) / q with hB
  obtain ⟨m, hm1, hm2⟩ : ∃ m : ℝ, (0 < m ∧ B ≤ 8 * m)
      ∧ L.toReal < (9 / 2) * m - (9 / 16) * B - 1 := by
    refine ⟨max 1 (max (B / 8) ((L.toReal + 2 + (9 / 16) * B) * (2 / 9))), ⟨?_, ?_⟩, ?_⟩
    · exact lt_of_lt_of_le one_pos (le_max_left _ _)
    · have h1 : B / 8 ≤ max 1 (max (B / 8) ((L.toReal + 2 + (9 / 16) * B) * (2 / 9))) :=
        le_trans (le_max_left _ _) (le_max_right _ _)
      linarith
    · have h2 : (L.toReal + 2 + (9 / 16) * B) * (2 / 9)
          ≤ max 1 (max (B / 8) ((L.toReal + 2 + (9 / 16) * B) * (2 / 9))) :=
        le_trans (le_max_right _ _) (le_max_right _ _)
      nlinarith
  have hkey := key m hm1.1 hm1.2
  have hLtoReal : ENNReal.ofReal ((9 / 2) * m - (9 / 16) * B - 1) ≤ L := hkey
  have := ENNReal.toReal_mono hne hLtoReal
  rw [ENNReal.toReal_ofReal (by linarith [hm2, ENNReal.toReal_nonneg (a := L)])] at this
  linarith

end RWRS.Support
