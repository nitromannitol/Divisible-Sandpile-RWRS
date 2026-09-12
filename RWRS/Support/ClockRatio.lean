/-
The two ratios of `lem:clock-no-dom` and `lem:no-dominance`.

Both rest on one real statement: the diagonal value `g_n(x,x)` of the
finite-time Green function is negligible compared with the total Green mass
`A_n(x) = ∑_v g_n(x,v)` as soon as that total diverges, and likewise compared
with the square root of `Σ_n(x) = ∑_v g_n(x,v)^2` as soon as that diverges.
In the transient case the diagonal value is bounded while the total diverges.
In the recurrent case each fixed vertex carries asymptotically the whole
diagonal value, by `eventually_meanLocalTime_ge`, so any `m` vertices already
carry `m` times half of it.
-/
import RWRS.Support.Recurrence
import RWRS.Support.ShortClock
import RWRS.Support.KernelSum

namespace RWRS.Support

open Filter Topology
open scoped ENNReal

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

/-! ### The Green mass of a finite set -/

theorem greenTime_eq_zero_of_notMem_reach (n : ℕ) (x v : V) (hv : v ∉ reach G x n) :
    greenTime G n x v = 0 := by
  rw [greenTime, meanLocalTime]
  have : ∀ k ∈ Finset.range n, heat G k x v = 0 := fun k hk =>
    heat_eq_zero_of_notMem_reach k x v fun hc =>
      hv (reach_mono x (Nat.le_of_lt (Finset.mem_range.mp hk)) hc)
  rw [Finset.sum_congr rfl this]
  simp

theorem sum_greenTime_le_clock [Infinite V] (hG : G.Connected) (n : ℕ) (x : V) (F : Finset V) :
    ∑ v ∈ F, greenTime G n x v ≤ clock G n x := by
  classical
  have h2 : ∑ v ∈ reach G x n, greenTime G n x v
      = ∑ v ∈ F ∪ reach G x n, greenTime G n x v := by
    refine Finset.sum_subset Finset.subset_union_right fun v _ hv => ?_
    exact greenTime_eq_zero_of_notMem_reach n x v hv
  rw [clock_eq_green_sum hG, h2]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
    fun v _ _ => greenTime_nonneg n x v

theorem clock_nonneg [Infinite V] (hG : G.Connected) (n : ℕ) (x : V) : 0 ≤ clock G n x := by
  have := sum_greenTime_le_clock hG n x ∅
  simpa using this

/-- The tail of the Green mass is the clock, in `[0,∞]`. -/
theorem tsum_ofReal_greenTime [Infinite V] (hG : G.Connected) (n : ℕ) (x : V) :
    ∑' v : V, ENNReal.ofReal (greenTime G n x v) = ENNReal.ofReal (clock G n x) := by
  classical
  rw [tsum_eq_sum (s := reach G x n) fun v hv => by
    rw [greenTime_eq_zero_of_notMem_reach n x v hv, ENNReal.ofReal_zero]]
  rw [← ENNReal.ofReal_sum_of_nonneg fun v _ => greenTime_nonneg n x v, clock_eq_green_sum hG]

/-- The fluctuation scale is at most the largest Green value times the clock. -/
theorem fluct_le [Infinite V] (hG : G.Connected) (n : ℕ) (x : V) :
    fluct G n x ≤ supGreenTime G n x * ENNReal.ofReal (clock G n x) := by
  rw [← tsum_ofReal_greenTime hG n x, ← ENNReal.tsum_mul_left, fluct]
  refine ENNReal.tsum_le_tsum fun v => ?_
  rw [show greenTime G n x v ^ 2 = greenTime G n x v * greenTime G n x v from by ring,
    ENNReal.ofReal_mul (greenTime_nonneg n x v)]
  refine mul_le_mul' ?_ le_rfl
  exact le_iSup (fun w => ENNReal.ofReal (greenTime G n x w)) v

/-! ### The diagonal value against the clock -/

theorem greenTime_diag_le_of_transient [Infinite V] (hG : G.Connected) (x : V) {M : ℝ}
    (hM : ∀ n : ℕ, meanLocalTime G n x x ≤ M) (n : ℕ) :
    greenTime G n x x ≤ M / (G.degree x : ℝ) := by
  have hd : (0 : ℝ) < (G.degree x : ℝ) := by exact_mod_cast degree_pos hG x
  rw [greenTime]
  exact div_le_div_of_nonneg_right (hM n) hd.le

/-- In the recurrent case, `m` vertices already carry `m/2` times the diagonal
value of the finite-time Green function. -/
theorem eventually_clock_ge [Infinite V] (hG : G.Connected) (x : V) (hrec : green G x x = ⊤)
    (F : Finset V) :
    ∀ᶠ n in atTop, (F.card : ℝ) / 2 * greenTime G n x x ≤ clock G n x := by
  have hd : (0 : ℝ) < (G.degree x : ℝ) := by exact_mod_cast degree_pos hG x
  have hall : ∀ᶠ n in atTop, ∀ v ∈ F,
      (1 - (1 / 2 : ℝ)) * meanLocalTime G n x x ≤ meanLocalTime G n v x :=
    (Filter.eventually_all_finset F).2 fun v _ =>
      eventually_meanLocalTime_ge hG x v hrec (by norm_num)
  filter_upwards [hall] with n hn
  refine le_trans ?_ (sum_greenTime_le_clock hG n x F)
  have hterm : ∀ v ∈ F, (1 / 2 : ℝ) * greenTime G n x x ≤ greenTime G n x v := by
    intro v hv
    have h := hn v hv
    rw [greenTime_eq_meanLocalTime hG n x v, greenTime, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right (by linarith) hd.le
  calc (F.card : ℝ) / 2 * greenTime G n x x
      = ∑ _v ∈ F, (1 / 2 : ℝ) * greenTime G n x x := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ ∑ v ∈ F, greenTime G n x v := Finset.sum_le_sum hterm


/-! ### The two ratios -/

/-- The diagonal value of the finite-time Green function is negligible against
the clock once the clock diverges. -/
theorem tendsto_greenTime_div_clock [Infinite V] (hG : G.Connected) (x : V)
    (hA : Tendsto (fun n : ℕ => clock G n x) atTop atTop) :
    Tendsto (fun n : ℕ => greenTime G n x x / clock G n x) atTop (𝓝 0) := by
  refine NormedAddGroup.tendsto_nhds_zero.2 fun δ hδ => ?_
  by_cases hrec : green G x x = ⊤
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, 2 / δ < (m : ℝ) := exists_nat_gt (2 / δ)
    obtain ⟨F, hF⟩ := Infinite.exists_subset_card_eq V m
    have hmpos : (0 : ℝ) < m := lt_trans (by positivity) hm
    filter_upwards [eventually_clock_ge hG x hrec F, hA.eventually_gt_atTop 0] with n hn hA0
    rw [hF] at hn
    have hg : 0 ≤ greenTime G n x x := greenTime_nonneg n x x
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hg hA0.le), div_lt_iff₀ hA0]
    rw [div_lt_iff₀ hδ] at hm
    nlinarith [hn, hA0, hg]
  · obtain ⟨M, hM⟩ := meanLocalTime_bddAbove_of_transient hG x hrec
    set c : ℝ := max 0 (M / (G.degree x : ℝ)) with hc
    have hc0 : 0 ≤ c := le_max_left _ _
    filter_upwards [hA.eventually_gt_atTop (c / δ), hA.eventually_gt_atTop 0] with n hn hA0
    have hg : greenTime G n x x ≤ c :=
      le_trans (greenTime_diag_le_of_transient hG x hM n) (le_max_right _ _)
    have hg0 : 0 ≤ greenTime G n x x := greenTime_nonneg n x x
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hg0 hA0.le), div_lt_iff₀ hA0]
    rw [div_lt_iff₀ hδ] at hn
    nlinarith [hn, hg, hδ]

theorem tendsto_supGreenTime_div_clock [Infinite V] (hG : G.Connected) (x : V)
    (hA : Tendsto (fun n : ℕ => clock G n x) atTop atTop) :
    Tendsto (fun n : ℕ => supGreenTime G n x / ENNReal.ofReal (clock G n x)) atTop (𝓝 0) := by
  have hR := (ENNReal.tendsto_ofReal (tendsto_greenTime_div_clock hG x hA))
  rw [ENNReal.ofReal_zero] at hR
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hR
    (Filter.Eventually.of_forall fun n => by simp) ?_
  filter_upwards [hA.eventually_gt_atTop 0] with n hA0
  rw [ENNReal.ofReal_div_of_pos hA0]
  exact ENNReal.div_le_div_right (supGreenTime_le hG n x) _

theorem tendsto_fluct_div_clock_sq [Infinite V] (hG : G.Connected) (x : V)
    (hA : Tendsto (fun n : ℕ => clock G n x) atTop atTop) :
    Tendsto (fun n : ℕ => fluct G n x / (ENNReal.ofReal (clock G n x)) ^ 2) atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_supGreenTime_div_clock hG x hA)
    (Filter.Eventually.of_forall fun n => by simp) ?_
  filter_upwards [hA.eventually_gt_atTop 0] with n hA0
  have hne : ENNReal.ofReal (clock G n x) ≠ 0 := by
    simpa using hA0
  have hnt : ENNReal.ofReal (clock G n x) ≠ ⊤ := ENNReal.ofReal_ne_top
  calc fluct G n x / (ENNReal.ofReal (clock G n x)) ^ 2
      ≤ (supGreenTime G n x * ENNReal.ofReal (clock G n x))
          / (ENNReal.ofReal (clock G n x)) ^ 2 :=
        ENNReal.div_le_div_right (fluct_le hG n x) _
    _ = supGreenTime G n x / ENNReal.ofReal (clock G n x) := by
        rw [sq]
        exact ENNReal.mul_div_mul_right _ _ hne hnt


/-- The `ℓ²` mass of the finite-time Green function is negligible against the
square of its `ℓ¹` mass, in real form. -/
theorem tendsto_sumSq_div_clock_sq [Infinite V] (hG : G.Connected) (x : V)
    (hA : Tendsto (fun n : ℕ => clock G n x) atTop atTop) :
    Tendsto (fun n : ℕ => (∑ v ∈ reach G x n, greenTime G n x v ^ 2) / clock G n x ^ 2)
      atTop (𝓝 0) := by
  refine squeeze_zero' (Filter.Eventually.of_forall fun n => ?_) ?_
    (tendsto_greenTime_div_clock hG x hA)
  · exact div_nonneg (Finset.sum_nonneg fun v _ => by positivity) (by positivity)
  filter_upwards [hA.eventually_gt_atTop 0] with n hn
  have hsum : ∑ v ∈ reach G x n, greenTime G n x v ^ 2
      ≤ greenTime G n x x * clock G n x := by
    rw [clock_eq_green_sum hG, Finset.mul_sum]
    refine Finset.sum_le_sum fun v _ => ?_
    rw [sq]
    exact mul_le_mul_of_nonneg_right (greenTime_le_diag hG n x v) (greenTime_nonneg n x v)
  refine le_trans (div_le_div_of_nonneg_right hsum (by positivity)) (le_of_eq ?_)
  field_simp


/-! ### The diagonal value against the `ℓ²` mass

These are the ingredients of `lem:no-dominance`, in the form in which the
fluctuation scale is the real sum over the vertices reachable in `n` steps; the
finite-time Green function vanishes off that set, so the sum is the paper's
`Σ_n(o)`. -/

/-- `Σ_n(o) = ∑_v g_n(o,v)^2`, as a real sum over the reachable vertices. -/
noncomputable def sumSq (G : SimpleGraph V) [G.LocallyFinite] (n : ℕ) (o : V) : ℝ :=
  ∑ v ∈ reach G o n, greenTime G n o v ^ 2

theorem sum_sq_le_sumSq (n : ℕ) (o : V) (F : Finset V) :
    ∑ v ∈ F, greenTime G n o v ^ 2 ≤ sumSq G n o := by
  classical
  have h2 : ∑ v ∈ reach G o n, greenTime G n o v ^ 2
      = ∑ v ∈ F ∪ reach G o n, greenTime G n o v ^ 2 := by
    refine Finset.sum_subset Finset.subset_union_right fun v _ hv => ?_
    rw [greenTime_eq_zero_of_notMem_reach n o v hv]
    ring
  rw [sumSq, h2]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
    fun v _ _ => by positivity

theorem fluct_eq_ofReal_sumSq (n : ℕ) (o : V) :
    fluct G n o = ENNReal.ofReal (sumSq G n o) := by
  classical
  rw [fluct, tsum_eq_sum (s := reach G o n) fun v hv => by
    rw [greenTime_eq_zero_of_notMem_reach n o v hv]
    simp,
    ← ENNReal.ofReal_sum_of_nonneg fun v _ => by positivity]
  rfl

theorem fluct_ne_top (n : ℕ) (o : V) : fluct G n o ≠ ⊤ := by
  rw [fluct_eq_ofReal_sumSq]
  exact ENNReal.ofReal_ne_top

theorem eventually_sumSq_ge [Infinite V] (hG : G.Connected) (o : V) (hrec : green G o o = ⊤)
    (F : Finset V) :
    ∀ᶠ n in atTop, (F.card : ℝ) / 4 * greenTime G n o o ^ 2 ≤ sumSq G n o := by
  have hd : (0 : ℝ) < (G.degree o : ℝ) := by exact_mod_cast degree_pos hG o
  have hall : ∀ᶠ n in atTop, ∀ v ∈ F,
      (1 - (1 / 2 : ℝ)) * meanLocalTime G n o o ≤ meanLocalTime G n v o :=
    (Filter.eventually_all_finset F).2 fun v _ =>
      eventually_meanLocalTime_ge hG o v hrec (by norm_num)
  filter_upwards [hall] with n hn
  refine le_trans ?_ (sum_sq_le_sumSq n o F)
  have hterm : ∀ v ∈ F, (1 / 2 : ℝ) * greenTime G n o o ≤ greenTime G n o v := by
    intro v hv
    have h := hn v hv
    rw [greenTime_eq_meanLocalTime hG n o v, greenTime, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right (by linarith) hd.le
  calc (F.card : ℝ) / 4 * greenTime G n o o ^ 2
      = ∑ _v ∈ F, ((1 / 2 : ℝ) * greenTime G n o o) ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ ∑ v ∈ F, greenTime G n o v ^ 2 := by
        refine Finset.sum_le_sum fun v _ => ?_
        have h1 : 0 ≤ (1 / 2 : ℝ) * greenTime G n o o := by
          have := greenTime_nonneg (G := G) n o o; positivity
        exact pow_le_pow_left₀ h1 (hterm v (by assumption)) 2

/-- The mathematics of `lem:no-dominance`, in the real form: the diagonal value
of the finite-time Green function is negligible against the `ℓ²` mass once that
mass diverges. -/
theorem tendsto_greenTime_sq_div_sumSq [Infinite V] (hG : G.Connected) (o : V)
    (hS : Tendsto (fun n : ℕ => sumSq G n o) atTop atTop) :
    Tendsto (fun n : ℕ => greenTime G n o o ^ 2 / sumSq G n o) atTop (𝓝 0) := by
  refine NormedAddGroup.tendsto_nhds_zero.2 fun δ hδ => ?_
  by_cases hrec : green G o o = ⊤
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, 4 / δ < (m : ℝ) := exists_nat_gt (4 / δ)
    obtain ⟨F, hF⟩ := Infinite.exists_subset_card_eq V m
    have hmpos : (0 : ℝ) < m := lt_trans (by positivity) hm
    filter_upwards [eventually_sumSq_ge hG o hrec F, hS.eventually_gt_atTop 0] with n hn hS0
    rw [hF] at hn
    have hg : 0 ≤ greenTime G n o o ^ 2 := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hg hS0.le), div_lt_iff₀ hS0]
    rw [div_lt_iff₀ hδ] at hm
    nlinarith [hn, hS0, hg]
  · obtain ⟨M, hM⟩ := meanLocalTime_bddAbove_of_transient hG o hrec
    set c : ℝ := max 0 (M / (G.degree o : ℝ)) with hc
    have hc0 : 0 ≤ c := le_max_left _ _
    filter_upwards [hS.eventually_gt_atTop (c ^ 2 / δ), hS.eventually_gt_atTop 0] with n hn hS0
    have hg : greenTime G n o o ≤ c :=
      le_trans (greenTime_diag_le_of_transient hG o hM n) (le_max_right _ _)
    have hg0 : 0 ≤ greenTime G n o o := greenTime_nonneg n o o
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (by positivity) hS0.le), div_lt_iff₀ hS0]
    rw [div_lt_iff₀ hδ] at hn
    nlinarith [hn, hg, hg0, hδ, hS0]

end RWRS.Support
