/-
Parallel toppling on a random rooted network: it is equivariant under
isomorphism, and it is a measurable function of the network.

Every quantity below depends on the network through its neighbour lists, so the
neighbour set of a fixed vertex takes countably many values, each on a
measurable set of networks; a function that is measurable once that value is
fixed is therefore measurable.  That is `measurable_of_countable_partition`,
and it is what carries the recursion of the toppling through the sum over the
neighbours of a vertex.
-/
import RWRS.Support.Marking
import RWRS.Support.Odometer

namespace RWRS.Support

open MeasureTheory
open scoped ENNReal

/-! ### A countable measurable partition -/

theorem measurable_of_countable_partition {α β ι : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [Countable ι] {A : ι → Set α} (hA : ∀ i, MeasurableSet (A i))
    (hcov : ∀ x, ∃ i, x ∈ A i) {F : α → β} {g : ι → α → β} (hg : ∀ i, Measurable (g i))
    (hFg : ∀ (i : ι), ∀ x ∈ A i, F x = g i x) : Measurable F := by
  intro B hB
  have hset : F ⁻¹' B = ⋃ i, A i ∩ (g i ⁻¹' B) := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := hcov x
      refine Set.mem_iUnion.2 ⟨i, hi, ?_⟩
      rw [Set.mem_preimage, ← hFg i x hi]
      exact hx
    · intro hx
      obtain ⟨i, hi, hgi⟩ := Set.mem_iUnion.1 hx
      rw [Set.mem_preimage, hFg i x hi]
      exact hgi
  rw [hset]
  exact MeasurableSet.iUnion fun i => (hA i).inter (hg i hB)

/-! ### The neighbour set of a fixed vertex -/

open scoped Classical in
theorem measurableSet_neighborFinset_eq {m : ℕ} (r : ℕ) (S : Finset ℕ) :
    MeasurableSet {N : Net m | (netGraph N).neighborFinset r = S} := by
  have hset : {N : Net m | (netGraph N).neighborFinset r = S}
      = ⋂ j : ℕ, {N : Net m | ((netGraph N).Adj r j ↔ j ∈ S)} := by
    ext N
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro h j
      rw [← SimpleGraph.mem_neighborFinset, h]
    · intro h
      ext j
      rw [SimpleGraph.mem_neighborFinset]
      exact h j
  rw [hset]
  refine MeasurableSet.iInter fun j => ?_
  by_cases hj : j ∈ S
  · have : {N : Net m | ((netGraph N).Adj r j ↔ j ∈ S)} = {N : Net m | (netGraph N).Adj r j} := by
      ext N; simp [hj]
    rw [this]; exact measurableSet_adj r j
  · have : {N : Net m | ((netGraph N).Adj r j ↔ j ∈ S)}
        = {N : Net m | (netGraph N).Adj r j}ᶜ := by
      ext N; simp [hj]
    rw [this]; exact (measurableSet_adj r j).compl

theorem measurable_neighborSum {m : ℕ} (r : ℕ) {f : Net m → ℕ → ℝ}
    (hf : ∀ y : ℕ, Measurable fun N => f N y) :
    Measurable fun N : Net m => ∑ y ∈ (netGraph N).neighborFinset r, f N y := by
  classical
  refine measurable_of_countable_partition (A := fun S : Finset ℕ =>
      {N : Net m | (netGraph N).neighborFinset r = S})
    (fun S => measurableSet_neighborFinset_eq r S)
    (fun N => ⟨(netGraph N).neighborFinset r, rfl⟩)
    (g := fun S N => ∑ y ∈ S, f N y)
    (fun S => Finset.measurable_sum _ fun y _ => hf y) ?_
  intro S N hN
  rw [show (netGraph N).neighborFinset r = S from hN]

theorem measurable_degree {m : ℕ} (r : ℕ) :
    Measurable fun N : Net m => ((netGraph N).degree r : ℝ) := by
  classical
  refine measurable_of_countable_partition (A := fun S : Finset ℕ =>
      {N : Net m | (netGraph N).neighborFinset r = S})
    (fun S => measurableSet_neighborFinset_eq r S)
    (fun N => ⟨(netGraph N).neighborFinset r, rfl⟩)
    (g := fun S _ => (S.card : ℝ)) (fun S => measurable_const) ?_
  intro S N hN
  rw [SimpleGraph.degree, show (netGraph N).neighborFinset r = S from hN]


/-! ### The toppling is a measurable function of the network -/

theorem measurable_netConfig (v : ℕ) : Measurable fun N : Net 1 => netConfig N v := by
  have hrw : (fun N : Net 1 => netConfig N v) = fun N => N.2.2 v 0 := rfl
  rw [hrw]
  exact (measurable_pi_apply (0 : Fin 1)).comp
    ((measurable_pi_apply v).comp (measurable_snd.comp measurable_snd))

theorem measurable_configOfNet (k : ℕ) : ∀ v : ℕ,
    Measurable fun N : Net 1 => config (netGraph N) (netConfig N) k v := by
  induction k with
  | zero => exact fun v => measurable_netConfig v
  | succ k ih =>
      intro v
      have hem : ∀ w : ℕ, Measurable fun N : Net 1 =>
          emission (netGraph N) (config (netGraph N) (netConfig N) k) w := by
        intro w
        simp only [emission]
        exact (((ih w).sub measurable_const).max measurable_const).div (measurable_degree w)
      have hrw : (fun N : Net 1 => config (netGraph N) (netConfig N) (k + 1) v)
          = fun N => min (config (netGraph N) (netConfig N) k v) 1
              + ∑ w ∈ (netGraph N).neighborFinset v,
                  emission (netGraph N) (config (netGraph N) (netConfig N) k) w := by
        funext N
        rw [config_succ, topple]
      rw [hrw]
      exact ((ih v).min measurable_const).add (measurable_neighborSum v hem)

theorem measurable_odometerNet (k : ℕ) (v : ℕ) :
    Measurable fun N : Net 1 => odometer (netGraph N) (netConfig N) k v := by
  refine Finset.measurable_sum _ fun j _ => ?_
  simp only [emission]
  exact (((measurable_configOfNet j v).sub measurable_const).max measurable_const).div
    (measurable_degree v)

open scoped Classical in
theorem measurable_netTopple (k : ℕ) : Measurable fun N : Net 1 => netTopple N k := by
  refine Measurable.prodMk measurable_fst (Measurable.prodMk (measurable_fst.comp measurable_snd) ?_)
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  by_cases hj : j = 0
  · simp only [hj]
    exact measurable_configOfNet k i
  · simp only [if_neg hj]
    exact measurable_odometerNet k i

/-! ### The toppling is equivariant -/

variable {m : ℕ} {N N' : Net m} {φ : ℕ ≃ ℕ}

theorem netIso_neighborFinset
    (hadj : ∀ i j, (netGraph N).Adj i j ↔ (netGraph N').Adj (φ i) (φ j)) (i : ℕ) :
    (netGraph N').neighborFinset (φ i) = ((netGraph N).neighborFinset i).image φ := by
  classical
  ext j
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_image]
  constructor
  · intro h
    refine ⟨φ.symm j, ?_, φ.apply_symm_apply j⟩
    rw [hadj i (φ.symm j), φ.apply_symm_apply]
    exact h
  · rintro ⟨y, hy, rfl⟩
    exact (hadj i y).mp hy

theorem netIso_degree
    (hadj : ∀ i j, (netGraph N).Adj i j ↔ (netGraph N').Adj (φ i) (φ j)) (i : ℕ) :
    (netGraph N').degree (φ i) = (netGraph N).degree i := by
  classical
  rw [SimpleGraph.degree, SimpleGraph.degree, netIso_neighborFinset hadj,
    Finset.card_image_of_injective _ φ.injective]

theorem netIso_sum
    (hadj : ∀ i j, (netGraph N).Adj i j ↔ (netGraph N').Adj (φ i) (φ j))
    (f f' : ℕ → ℝ) (hff : ∀ y, f' (φ y) = f y) (i : ℕ) :
    ∑ y ∈ (netGraph N').neighborFinset (φ i), f' y
      = ∑ y ∈ (netGraph N).neighborFinset i, f y := by
  classical
  rw [netIso_neighborFinset hadj, Finset.sum_image fun a _ b _ h => φ.injective h]
  exact Finset.sum_congr rfl fun y _ => hff y

theorem netIso_config
    (hadj : ∀ i j, (netGraph N).Adj i j ↔ (netGraph N').Adj (φ i) (φ j))
    (σ σ' : ℕ → ℝ) (hσ : ∀ i, σ' (φ i) = σ i) :
    ∀ (k : ℕ) (i : ℕ), config (netGraph N') σ' k (φ i) = config (netGraph N) σ k i := by
  intro k
  induction k with
  | zero => exact hσ
  | succ k ih =>
      intro i
      have hem : ∀ y : ℕ,
          emission (netGraph N') (config (netGraph N') σ' k) (φ y)
            = emission (netGraph N) (config (netGraph N) σ k) y := by
        intro y
        rw [emission, emission, ih y, netIso_degree hadj]
      rw [config_succ, config_succ, topple, topple, ih i,
        netIso_sum hadj _ _ hem i]

theorem netIso_odometer
    (hadj : ∀ i j, (netGraph N).Adj i j ↔ (netGraph N').Adj (φ i) (φ j))
    (σ σ' : ℕ → ℝ) (hσ : ∀ i, σ' (φ i) = σ i) (k : ℕ) (i : ℕ) :
    odometer (netGraph N') σ' k (φ i) = odometer (netGraph N) σ k i := by
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [emission, emission, netIso_config hadj σ σ' hσ j i, netIso_degree hadj]

theorem netIso_netTopple {N N' : Net 1} (h : NetIso N N') (k : ℕ) :
    NetIso (netTopple N k) (netTopple N' k) := by
  classical
  obtain ⟨φ, hadj, hroot, hmark⟩ := h
  have hσ : ∀ i, netConfig N' (φ i) = netConfig N i := fun i => (congrFun (hmark i) 0).symm
  refine ⟨φ, ?_, hroot, ?_⟩
  · intro i j
    exact hadj i j
  · intro i
    funext j
    by_cases hj : j = 0
    · simp only [netMark, netTopple, hj]
      exact (netIso_config hadj _ _ hσ k i).symm
    · simp only [netMark, netTopple, if_neg hj]
      exact (netIso_odometer hadj _ _ hσ k i).symm


/-! ### Rerooting and the toppling -/

theorem netTopple_reroot (N : Net 1) (k : ℕ) (y : ℕ) :
    netTopple (netReroot N y) k = netReroot (netTopple N k) y := rfl

theorem isStationaryNet_map_netTopple (P : Measure (Net 1)) (hstat : IsStationaryNet P) (k : ℕ) :
    IsStationaryNet (P.map (fun N => netTopple N k)) := by
  rw [isStationaryNet_iff]
  intro h hm hinv
  have hT : Measurable fun N : Net 1 => netTopple N k := measurable_netTopple k
  have hinv' : NetInvariant fun N : Net 1 => h (netTopple N k) :=
    fun N N' hiso => hinv _ _ (netIso_netTopple hiso k)
  have hrr : ∀ N : Net 1,
      rerootAvg h (netTopple N k) = rerootAvg (fun M : Net 1 => h (netTopple M k)) N := fun N => rfl
  rw [lintegral_map hm hT,
    (isStationaryNet_iff P).mp hstat (fun M : Net 1 => h (netTopple M k)) (hm.comp hT) hinv',
    lintegral_map (measurable_rerootAvg hm) hT]
  exact lintegral_congr fun N => (hrr N).symm

/-! ### The emission at the root, and the inflow into it -/

/-- The mass the root emits in round `j`. -/
noncomputable def netEmission (N : Net 1) (j : ℕ) : ℝ :=
  emission (netGraph N) (config (netGraph N) (netConfig N) j) (netRoot N)

/-- The mass the root receives in round `j`, per unit of degree. -/
noncomputable def netInflow (N : Net 1) (j : ℕ) : ℝ :=
  (∑ y ∈ (netGraph N).neighborFinset (netRoot N),
      emission (netGraph N) (config (netGraph N) (netConfig N) j) y)
    / ((netGraph N).degree (netRoot N) : ℝ)

theorem netEmission_nonneg (N : Net 1) (j : ℕ) : 0 ≤ netEmission N j :=
  div_nonneg (le_max_right _ _) (Nat.cast_nonneg _)

theorem netInflow_nonneg (N : Net 1) (j : ℕ) : 0 ≤ netInflow N j :=
  div_nonneg (Finset.sum_nonneg fun _y _ => div_nonneg (le_max_right _ _) (Nat.cast_nonneg _))
    (Nat.cast_nonneg _)

/-- The emission at a named vertex, as a function of the network and that
vertex. -/
noncomputable def netEmissionAt (N : Net 1) (j : ℕ) (r : ℕ) : ℝ :=
  emission (netGraph N) (config (netGraph N) (netConfig N) j) r

/-- The inflow at a named vertex. -/
noncomputable def netInflowAt (N : Net 1) (j : ℕ) (r : ℕ) : ℝ :=
  (∑ y ∈ (netGraph N).neighborFinset r,
      emission (netGraph N) (config (netGraph N) (netConfig N) j) y)
    / ((netGraph N).degree r : ℝ)

set_option maxHeartbeats 1000000 in
theorem measurable_netEmission (j : ℕ) : Measurable fun N : Net 1 => netEmission N j := by
  have hpair : Measurable fun q : Net 1 × ℕ => netEmissionAt q.1 j q.2 := by
    refine measurable_from_prod_countable_left fun r => ?_
    simp only [netEmissionAt, emission]
    exact (((measurable_configOfNet j r).sub measurable_const).max measurable_const).div
      (measurable_degree r)
  have hsplit : (fun N : Net 1 => netEmission N j)
      = (fun q : Net 1 × ℕ => netEmissionAt q.1 j q.2) ∘ fun N : Net 1 => (N, netRoot N) := rfl
  rw [hsplit]
  exact hpair.comp (measurable_id.prodMk measurable_netRoot)

set_option maxHeartbeats 1000000 in
theorem measurable_netInflow (j : ℕ) : Measurable fun N : Net 1 => netInflow N j := by
  have hem : ∀ y : ℕ, Measurable fun N : Net 1 =>
      emission (netGraph N) (config (netGraph N) (netConfig N) j) y := by
    intro y
    simp only [emission]
    exact (((measurable_configOfNet j y).sub measurable_const).max measurable_const).div
      (measurable_degree y)
  have hpair : Measurable fun q : Net 1 × ℕ => netInflowAt q.1 j q.2 := by
    refine measurable_from_prod_countable_left fun r => ?_
    simp only [netInflowAt]
    exact (measurable_neighborSum r hem).div (measurable_degree r)
  have hsplit : (fun N : Net 1 => netInflow N j)
      = (fun q : Net 1 × ℕ => netInflowAt q.1 j q.2) ∘ fun N : Net 1 => (N, netRoot N) := rfl
  rw [hsplit]
  exact hpair.comp (measurable_id.prodMk measurable_netRoot)

theorem netInvariant_netEmission (j : ℕ) :
    NetInvariant fun N : Net 1 => ENNReal.ofReal (netEmission N j) := by
  rintro N N' ⟨φ, hadj, hroot, hmark⟩
  have hσ : ∀ i, netConfig N' (φ i) = netConfig N i := fun i => (congrFun (hmark i) 0).symm
  have hkey : netEmission N j = netEmission N' j := by
    show emission (netGraph N) (config (netGraph N) (netConfig N) j) (netRoot N)
        = emission (netGraph N') (config (netGraph N') (netConfig N') j) (netRoot N')
    rw [← hroot, emission, emission, netIso_config hadj _ _ hσ j (netRoot N),
      netIso_degree hadj]
  show ENNReal.ofReal (netEmission N j) = ENNReal.ofReal (netEmission N' j)
  rw [hkey]

theorem rerootAvg_netEmission (N : Net 1) (j : ℕ) (hdeg : 0 < (netGraph N).degree (netRoot N)) :
    rerootAvg (fun M : Net 1 => ENNReal.ofReal (netEmission M j)) N
      = ENNReal.ofReal (netInflow N j) := by
  have hd : (0 : ℝ) < ((netGraph N).degree (netRoot N) : ℝ) := by exact_mod_cast hdeg
  have hsum : ∑ y ∈ (netGraph N).neighborFinset (netRoot N),
        ENNReal.ofReal (netEmission (netReroot N y) j)
      = ENNReal.ofReal (∑ y ∈ (netGraph N).neighborFinset (netRoot N),
          emission (netGraph N) (config (netGraph N) (netConfig N) j) y) := by
    rw [ENNReal.ofReal_sum_of_nonneg fun y _ => emission_nonneg (G := netGraph N) _ y]
    rfl
  rw [rerootAvg, hsum, netInflow, ENNReal.ofReal_div_of_pos hd, ENNReal.ofReal_natCast]


/-! ### Conservation of the degree-weighted mass -/

/-- The degree-weighted mass at a named vertex. -/
noncomputable def netMassAt (N : Net 1) (j r : ℕ) : ℝ :=
  config (netGraph N) (netConfig N) j r / ((netGraph N).degree r : ℝ)

set_option maxHeartbeats 1000000 in
theorem measurable_netWeightedMassAt (j : ℕ) :
    Measurable fun N : Net 1 => netWeightedMassAt N j := by
  have hpair : Measurable fun q : Net 1 × ℕ => netMassAt q.1 j q.2 := by
    refine measurable_from_prod_countable_left fun r => ?_
    simp only [netMassAt]
    exact (measurable_configOfNet j r).div (measurable_degree r)
  have hsplit : (fun N : Net 1 => netWeightedMassAt N j)
      = (fun q : Net 1 × ℕ => netMassAt q.1 j q.2) ∘ fun N : Net 1 => (N, netRoot N) := rfl
  rw [hsplit]
  exact hpair.comp (measurable_id.prodMk measurable_netRoot)

theorem netWeightedMassAt_zero (N : Net 1) : netWeightedMassAt N 0 = netWeightedMass N := rfl

theorem netWeightedMassAt_succ (N : Net 1) (j : ℕ) :
    netWeightedMassAt N (j + 1)
      = min (config (netGraph N) (netConfig N) j (netRoot N)) 1
          / ((netGraph N).degree (netRoot N) : ℝ) + netInflow N j := by
  rw [netWeightedMassAt, config_succ, topple, netInflow, add_div]

theorem min_add_max_sub_one (a : ℝ) : min a 1 + max (a - 1) 0 = a := by
  rcases le_total a 1 with h | h
  · rw [min_eq_left h, max_eq_right (by linarith), add_zero]
  · rw [min_eq_right h, max_eq_left (by linarith)]
    ring

theorem degree_root_pos {N : Net 1} (h : NetGood N) : 0 < (netGraph N).degree (netRoot N) :=
  degree_pos h (netRoot N)

theorem massConservation (P : Measure (Net 1)) [IsProbabilityMeasure P]
    (hgood : ∀ᵐ N ∂P, NetGood N) (hstat : IsStationaryNet P)
    (hint : Integrable (fun N => |netWeightedMass N|) P) :
    ∀ k : ℕ, Integrable (fun N => netWeightedMassAt N k) P ∧
      ∫ N, netWeightedMassAt N k ∂P = ∫ N, netWeightedMass N ∂P := by
  have hdeg : ∀ᵐ N ∂P, 0 < ((netGraph N).degree (netRoot N) : ℝ) := by
    filter_upwards [hgood] with N hN
    exact_mod_cast degree_root_pos hN
  have hone : ∀ᵐ N ∂P, 1 / ((netGraph N).degree (netRoot N) : ℝ) ≤ 1 := by
    filter_upwards [hgood] with N hN
    have h1 : (1 : ℝ) ≤ ((netGraph N).degree (netRoot N) : ℝ) := by
      exact_mod_cast degree_root_pos hN
    rw [div_le_one (by linarith)]
    exact h1
  intro k
  induction k with
  | zero =>
      refine ⟨?_, rfl⟩
      refine ⟨(measurable_netWeightedMassAt 0).aestronglyMeasurable, ?_⟩
      have := hint.hasFiniteIntegral
      refine lt_of_le_of_lt (lintegral_mono_ae ?_) this
      filter_upwards with N
      rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs, netWeightedMassAt_zero, abs_abs]
  | succ j ih =>
      obtain ⟨hIj, hEj⟩ := ih
      -- the emission at the root is integrable
      have hbound : Integrable (fun N : Net 1 => |netWeightedMassAt N j| + 1) P :=
        hIj.abs.add (integrable_const 1)
      have hemint : Integrable (fun N : Net 1 => netEmission N j) P := by
        refine Integrable.mono' hbound (measurable_netEmission j).aestronglyMeasurable ?_
        filter_upwards [hdeg, hone] with N hd h1
        rw [Real.norm_eq_abs, abs_of_nonneg (netEmission_nonneg N j), netEmission, emission]
        have h2 : max (config (netGraph N) (netConfig N) j (netRoot N) - 1) 0
            ≤ |config (netGraph N) (netConfig N) j (netRoot N)| + 1 := by
          rcases le_total (config (netGraph N) (netConfig N) j (netRoot N)) 1 with h | h
          · rw [max_eq_right (by linarith)]
            positivity
          · rw [max_eq_left (by linarith)]
            linarith [le_abs_self (config (netGraph N) (netConfig N) j (netRoot N))]
        have h3 : max (config (netGraph N) (netConfig N) j (netRoot N) - 1) 0
              / ((netGraph N).degree (netRoot N) : ℝ)
            ≤ (|config (netGraph N) (netConfig N) j (netRoot N)| + 1)
              / ((netGraph N).degree (netRoot N) : ℝ) :=
          div_le_div_of_nonneg_right h2 hd.le
        have h4 : (|config (netGraph N) (netConfig N) j (netRoot N)| + 1)
              / ((netGraph N).degree (netRoot N) : ℝ)
            = |netWeightedMassAt N j| + 1 / ((netGraph N).degree (netRoot N) : ℝ) := by
          rw [netWeightedMassAt, abs_div, abs_of_nonneg hd.le, add_div]
        linarith [h3, h4.le, h4.ge, h1]
      -- the stationarity identity for the emission
      have hlint : ∫⁻ N, ENNReal.ofReal (netEmission N j) ∂P
          = ∫⁻ N, ENNReal.ofReal (netInflow N j) ∂P := by
        rw [(isStationaryNet_iff P).mp hstat (fun N => ENNReal.ofReal (netEmission N j))
          ((measurable_netEmission j).ennreal_ofReal) (netInvariant_netEmission j)]
        refine lintegral_congr_ae ?_
        filter_upwards [hgood] with N hN
        exact rerootAvg_netEmission N j (degree_root_pos hN)
      have hemfin : ∫⁻ N, ENNReal.ofReal (netEmission N j) ∂P ≠ ⊤ := by
        have := hemint.hasFiniteIntegral
        rw [HasFiniteIntegral,
          lintegral_congr fun N => Real.enorm_eq_ofReal (netEmission_nonneg N j)] at this
        exact this.ne
      have hinfint : Integrable (fun N : Net 1 => netInflow N j) P := by
        refine ⟨(measurable_netInflow j).aestronglyMeasurable, ?_⟩
        rw [HasFiniteIntegral, lintegral_congr fun N => Real.enorm_eq_ofReal (netInflow_nonneg N j),
          ← hlint]
        exact hemfin.lt_top
      have hinfeq : ∫ N, netInflow N j ∂P = ∫ N, netEmission N j ∂P := by
        rw [integral_eq_lintegral_of_nonneg_ae
            (Filter.Eventually.of_forall fun N => netInflow_nonneg N j)
            (measurable_netInflow j).aestronglyMeasurable,
          integral_eq_lintegral_of_nonneg_ae
            (Filter.Eventually.of_forall fun N => netEmission_nonneg N j)
            (measurable_netEmission j).aestronglyMeasurable, hlint]
      -- the retained part
      have hmm : Measurable fun N : Net 1 =>
          min (config (netGraph N) (netConfig N) j (netRoot N)) 1
            / ((netGraph N).degree (netRoot N) : ℝ) := by
        have hrw : (fun N : Net 1 => min (config (netGraph N) (netConfig N) j (netRoot N)) 1
              / ((netGraph N).degree (netRoot N) : ℝ))
            = fun N => netWeightedMassAt N (j + 1) - netInflow N j := by
          funext N
          rw [netWeightedMassAt_succ]
          ring
        rw [hrw]
        exact (measurable_netWeightedMassAt (j + 1)).sub (measurable_netInflow j)
      have hminint : Integrable (fun N : Net 1 =>
          min (config (netGraph N) (netConfig N) j (netRoot N)) 1
            / ((netGraph N).degree (netRoot N) : ℝ)) P := by
        refine Integrable.mono' hbound hmm.aestronglyMeasurable ?_
        filter_upwards [hdeg, hone] with N hd h1
        rw [Real.norm_eq_abs, abs_div, abs_of_nonneg hd.le]
        have h2 : |min (config (netGraph N) (netConfig N) j (netRoot N)) 1|
            ≤ |config (netGraph N) (netConfig N) j (netRoot N)| + 1 := by
          rcases le_total (config (netGraph N) (netConfig N) j (netRoot N)) 1 with h | h
          · rw [min_eq_left h]
            linarith
          · rw [min_eq_right h, abs_one]
            linarith [abs_nonneg (config (netGraph N) (netConfig N) j (netRoot N))]
        have h3 : |min (config (netGraph N) (netConfig N) j (netRoot N)) 1|
              / ((netGraph N).degree (netRoot N) : ℝ)
            ≤ (|config (netGraph N) (netConfig N) j (netRoot N)| + 1)
              / ((netGraph N).degree (netRoot N) : ℝ) :=
          div_le_div_of_nonneg_right h2 hd.le
        have h4 : (|config (netGraph N) (netConfig N) j (netRoot N)| + 1)
              / ((netGraph N).degree (netRoot N) : ℝ)
            = |netWeightedMassAt N j| + 1 / ((netGraph N).degree (netRoot N) : ℝ) := by
          rw [netWeightedMassAt, abs_div, abs_of_nonneg hd.le, add_div]
        linarith [h3, h4.le, h4.ge, h1]
      refine ⟨?_, ?_⟩
      · have hrw : (fun N : Net 1 => netWeightedMassAt N (j + 1))
            = fun N => min (config (netGraph N) (netConfig N) j (netRoot N)) 1
                / ((netGraph N).degree (netRoot N) : ℝ) + netInflow N j :=
          funext fun N => netWeightedMassAt_succ N j
        rw [hrw]
        exact hminint.add hinfint
      · have hrw : (fun N : Net 1 => netWeightedMassAt N (j + 1))
            = fun N => min (config (netGraph N) (netConfig N) j (netRoot N)) 1
                / ((netGraph N).degree (netRoot N) : ℝ) + netInflow N j :=
          funext fun N => netWeightedMassAt_succ N j
        rw [hrw, integral_add hminint hinfint, hinfeq, ← integral_add hminint hemint, ← hEj]
        refine integral_congr_ae (Filter.Eventually.of_forall fun N => ?_)
        show min (config (netGraph N) (netConfig N) j (netRoot N)) 1
              / ((netGraph N).degree (netRoot N) : ℝ)
            + emission (netGraph N) (config (netGraph N) (netConfig N) j) (netRoot N)
            = netWeightedMassAt N j
        rw [emission, netWeightedMassAt, ← add_div, min_add_max_sub_one]

end RWRS.Support
