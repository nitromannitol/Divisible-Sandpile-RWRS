/-
The probability that some site of a finite set carries a large value in an
i.i.d. field.

Reading the field along a finite set of sites turns the product measure into a
finite product, so the probability that every site of the set stays below a
level is the level's probability raised to the size of the set.  With a Pareto
marginal this gives the uniform lower bound on the good events of
`lem:rec-good`: the complement is a product of `1 - p` over the sites, which is
at most `exp(-|S| p)`, and the construction makes `|S| p` bounded below.
-/
import RWRS.Support.WeakLaw
import RWRS.Support.PipeTree
import RWRS.Support.GadgetBall
import LatticeProb.Prob.FiniteMarginal

namespace RWRS.Support

open MeasureTheory
open scoped ENNReal

variable {V : Type*}

/-! ### Reading the field on a finite set of sites -/

theorem measurableSet_forall_lt (S : Finset V) (c : ℝ) :
    MeasurableSet {Y : V → ℝ | ∀ v ∈ S, Y v < c} := by
  classical
  have hset : {Y : V → ℝ | ∀ v ∈ S, Y v < c}
      = ⋂ v ∈ S, {Y : V → ℝ | Y v < c} := by
    ext Y; simp [Set.mem_iInter]
  rw [hset]
  exact MeasurableSet.biInter S.countable_toSet
    fun v _ => measurableSet_lt (measurable_pi_apply v) measurable_const

/-- **The field on a finite set of sites.**  The probability that every site of
a finite set stays below a level is the level's probability raised to the size
of the set. -/
theorem measure_forall_lt (ν : Measure ℝ) [IsProbabilityMeasure ν] (S : Finset V) (c : ℝ) :
    iidLaw V ν {Y : V → ℝ | ∀ v ∈ S, Y v < c} = ν (Set.Iio c) ^ S.card := by
  classical
  set T : (V → ℝ) → ({x // x ∈ S} → ℝ) := fun ω i => ω (i : V) with hT
  have hTm : Measurable T := measurable_pi_lambda _ fun i => measurable_pi_apply (i : V)
  have hmap : (iidLaw V ν).map T = Measure.pi fun _ : {x // x ∈ S} => ν :=
    LatticeProb.infinitePi_map_comp ν (fun i : {x // x ∈ S} => (i : V))
      Subtype.val_injective
  have hset : {Y : V → ℝ | ∀ v ∈ S, Y v < c}
      = T ⁻¹' (Set.univ.pi fun _ : {x // x ∈ S} => Set.Iio c) := by
    ext Y
    simp [hT, Set.mem_pi]
  have hmeas : MeasurableSet (Set.univ.pi fun _ : {x // x ∈ S} => Set.Iio c) :=
    MeasurableSet.univ_pi fun _ => measurableSet_Iio
  rw [hset, ← Measure.map_apply hTm hmeas, hmap, Measure.pi_pi]
  simp [Finset.prod_const]

/-- The complementary bound: some site of the finite set reaches the level. -/
theorem le_measure_exists_ge (ν : Measure ℝ) [IsProbabilityMeasure ν] (S : Finset V) (c : ℝ) :
    1 - ν (Set.Iio c) ^ S.card
      ≤ iidLaw V ν {Y : V → ℝ | ∃ v ∈ S, c ≤ Y v} := by
  classical
  haveI : IsProbabilityMeasure (iidLaw V ν) := by
    rw [iidLaw]; infer_instance
  have hcompl : {Y : V → ℝ | ∃ v ∈ S, c ≤ Y v} = {Y : V → ℝ | ∀ v ∈ S, Y v < c}ᶜ := by
    ext Y
    simp [Set.mem_setOf_eq, Set.mem_compl_iff, not_forall, not_lt]
  rw [hcompl, prob_compl_eq_one_sub (measurableSet_forall_lt S c), measure_forall_lt]

/-! ### The Pareto marginal -/

theorem pareto_Iio (ν : Measure ℝ) [IsProbabilityMeasure ν] {q : ℝ} (hq : 0 < q)
    (hpar : IsPareto ν q) {c : ℝ} (hc : 1 ≤ c) :
    ν (Set.Iio c) = ENNReal.ofReal (1 - c ^ (-q)) := by
  have hcpos : (0 : ℝ) < c := by linarith
  have hp0 : (0 : ℝ) < c ^ (-q) := Real.rpow_pos_of_pos hcpos _
  have hp1 : c ^ (-q) ≤ 1 := by
    rw [Real.rpow_neg hcpos.le, inv_le_one_iff₀]
    exact Or.inr (Real.one_le_rpow hc hq.le)
  have hIci : ν (Set.Ici c) = ENNReal.ofReal (c ^ (-q)) := hpar c hc
  have hcompl : Set.Iio c = (Set.Ici c)ᶜ := by
    ext z; simp
  rw [hcompl, prob_compl_eq_one_sub measurableSet_Ici, hIci,
    show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp, ← ENNReal.ofReal_sub _ hp0.le]

/-- **The good event of a finite set of sites under a Pareto marginal.** -/
theorem le_measure_spike (ν : Measure ℝ) [IsProbabilityMeasure ν] {q : ℝ} (hq : 0 < q)
    (hpar : IsPareto ν q) (S : Finset V) {c : ℝ} (hc : 1 ≤ c) :
    ENNReal.ofReal (1 - (1 - c ^ (-q)) ^ S.card)
      ≤ iidLaw V ν {Y : V → ℝ | ∃ v ∈ S, c ≤ Y v} := by
  have hcpos : (0 : ℝ) < c := by linarith
  have hp1 : c ^ (-q) ≤ 1 := by
    rw [Real.rpow_neg hcpos.le, inv_le_one_iff₀]
    exact Or.inr (Real.one_le_rpow hc hq.le)
  refine le_trans (le_of_eq ?_) (le_measure_exists_ge ν S c)
  rw [pareto_Iio ν hq hpar hc, ← ENNReal.ofReal_pow (by linarith),
    show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp,
    ← ENNReal.ofReal_sub _ (pow_nonneg (by linarith) _)]

/-! ### The exponential bound -/

theorem one_sub_pow_le_exp {p : ℝ} (hp1 : p ≤ 1) (N : ℕ) :
    (1 - p) ^ N ≤ Real.exp (-((N : ℝ) * p)) := by
  have h1 : (1 : ℝ) - p ≤ Real.exp (-p) := by
    have := Real.add_one_le_exp (-p)
    linarith
  calc (1 - p) ^ N ≤ (Real.exp (-p)) ^ N :=
        pow_le_pow_left₀ (by linarith) h1 N
    _ = Real.exp (-((N : ℝ) * p)) := by
        rw [← Real.exp_nat_mul]
        ring_nf

/-- If the expected number of spikes is bounded below, so is the probability of
at least one. -/
theorem le_measure_spike_const (ν : Measure ℝ) [IsProbabilityMeasure ν] {q : ℝ} (hq : 0 < q)
    (hpar : IsPareto ν q) (S : Finset V) {c θ : ℝ} (hc : 1 ≤ c)
    (hmean : θ ≤ (S.card : ℝ) * c ^ (-q)) :
    ENNReal.ofReal (1 - Real.exp (-θ))
      ≤ iidLaw V ν {Y : V → ℝ | ∃ v ∈ S, c ≤ Y v} := by
  have hcpos : (0 : ℝ) < c := by linarith
  have hp0 : (0 : ℝ) < c ^ (-q) := Real.rpow_pos_of_pos hcpos _
  have hp1 : c ^ (-q) ≤ 1 := by
    rw [Real.rpow_neg hcpos.le, inv_le_one_iff₀]
    exact Or.inr (Real.one_le_rpow hc hq.le)
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) (le_measure_spike ν hq hpar S hc)
  have h1 := one_sub_pow_le_exp hp1 S.card
  have h2 : Real.exp (-((S.card : ℝ) * c ^ (-q))) ≤ Real.exp (-θ) :=
    Real.exp_le_exp.2 (by linarith)
  linarith

/-! ### The mean number of spikes in a gadget -/

variable {B : ℕ} {α : ℝ}

/-- `L_m^{d_f-1} ≤ B^m`, the identity `α(d_f - 1) = 1` in the form the good-event
bound uses. -/
theorem combLen_rpow_le (hc : CombCond B α) {d_f : ℝ} (hdf : d_f = 1 + 1 / α) (m : ℕ) :
    (combLen B α m : ℝ) ^ (d_f - 1) ≤ (B : ℝ) ^ m := by
  have hα := alpha_pos hc
  have hd1 : d_f - 1 = 1 / α := by rw [hdf]; ring
  have hle : (combLen B α m : ℝ) ≤ ((B : ℝ) ^ α) ^ m := combLen_le hc m
  rw [hd1]
  calc (combLen B α m : ℝ) ^ (1 / α)
      ≤ (((B : ℝ) ^ α) ^ m) ^ (1 / α) :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) hle (by positivity)
    _ = (B : ℝ) ^ m := base_pow_rpow_inv hc m

/-- **The mean number of spikes in a gadget is bounded below.**  With the
threshold `K L_m` and at least `B^m L_m / 4` sites, the expected number of sites
above the threshold is at least `K^{-d_f}/4`, which does not depend on `m`. -/
theorem mean_spikes_ge (hc : CombCond B α) {d_f : ℝ} (hdf : d_f = 1 + 1 / α)
    {K : ℝ} (hK : 0 < K) {m N : ℕ} (hN : (B : ℝ) ^ m * (combLen B α m : ℝ) / 4 ≤ (N : ℝ)) :
    K ^ (-d_f) / 4 ≤ (N : ℝ) * (K * (combLen B α m : ℝ)) ^ (-d_f) := by
  have hα := alpha_pos hc
  have hLpos : (0 : ℝ) < (combLen B α m : ℝ) := by
    exact_mod_cast combLen_pos' hc m
  have hBpos : (0 : ℝ) < (B : ℝ) ^ m := by
    have := cast_B_pos hc; positivity
  have hdfpos : 0 < d_f := df_pos hc hdf
  have hsplit : (K * (combLen B α m : ℝ)) ^ (-d_f)
      = K ^ (-d_f) * (combLen B α m : ℝ) ^ (-d_f) :=
    Real.mul_rpow hK.le hLpos.le
  have hKpow : (0 : ℝ) < K ^ (-d_f) := Real.rpow_pos_of_pos hK _
  have hLpow : (0 : ℝ) < (combLen B α m : ℝ) ^ (-d_f) :=
    Real.rpow_pos_of_pos hLpos _
  have hLp : (0 : ℝ) < (combLen B α m : ℝ) ^ (d_f - 1) := Real.rpow_pos_of_pos hLpos _
  have hle := combLen_rpow_le hc hdf m
  have h1 : (combLen B α m : ℝ) * (combLen B α m : ℝ) ^ (-d_f)
      = (combLen B α m : ℝ) ^ (1 - d_f) := by
    rw [show (1 : ℝ) - d_f = 1 + -d_f by ring, Real.rpow_add hLpos, Real.rpow_one]
  have h2 : (combLen B α m : ℝ) ^ (1 - d_f)
      = ((combLen B α m : ℝ) ^ (d_f - 1))⁻¹ := by
    rw [← Real.rpow_neg hLpos.le, show -(d_f - 1) = 1 - d_f by ring]
  have hkey : 1 ≤ (B : ℝ) ^ m * ((combLen B α m : ℝ) * (combLen B α m : ℝ) ^ (-d_f)) := by
    rw [h1, h2]
    calc (1 : ℝ) = (combLen B α m : ℝ) ^ (d_f - 1) * ((combLen B α m : ℝ) ^ (d_f - 1))⁻¹ := by
          field_simp
      _ ≤ (B : ℝ) ^ m * ((combLen B α m : ℝ) ^ (d_f - 1))⁻¹ :=
          mul_le_mul_of_nonneg_right hle (by positivity)
  rw [hsplit]
  have hstep : ((B : ℝ) ^ m * (combLen B α m : ℝ) / 4)
        * (K ^ (-d_f) * (combLen B α m : ℝ) ^ (-d_f))
      ≤ (N : ℝ) * (K ^ (-d_f) * (combLen B α m : ℝ) ^ (-d_f)) :=
    mul_le_mul_of_nonneg_right hN (by positivity)
  have hid : ((B : ℝ) ^ m * (combLen B α m : ℝ) / 4)
        * (K ^ (-d_f) * (combLen B α m : ℝ) ^ (-d_f))
      = K ^ (-d_f) / 4
          * ((B : ℝ) ^ m * ((combLen B α m : ℝ) * (combLen B α m : ℝ) ^ (-d_f))) := by
    ring
  have hfinal : K ^ (-d_f) / 4 * 1
      ≤ K ^ (-d_f) / 4
          * ((B : ℝ) ^ m * ((combLen B α m : ℝ) * (combLen B α m : ℝ) ^ (-d_f))) :=
    mul_le_mul_of_nonneg_left hkey (by positivity)
  linarith [hstep, hid, hfinal]

end RWRS.Support
