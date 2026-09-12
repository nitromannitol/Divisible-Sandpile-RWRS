/-
The block bound of `lem:dyadic`.

Along one trajectory the payoff is the drift plus the fluctuation, and on a
graph of degree at most `d` the drift at a negative mean is at most
`-|m| n / d`.  Every time `n ≥ 1` lies in exactly one dyadic block, and on that
block the drift is at most `-|m| 2^k / d`, so the payoff is at most the block
maximum of the fluctuation minus that, hence at most `Y_k`.  The supremum of
the payoff is therefore at most the supremum of the `Y_k`, and raising to the
power `q` and summing gives the bound of the lemma.

The measurability side is what needs the vertex set to carry measurable
singletons: the fluctuation reads the scenery along the trajectory, and
`(ξ, X) ↦ ξ(X_k)` is measurable on the product exactly because the vertex set
is countable with measurable singletons.
-/
import RWRS.Support.Dyadic

open MeasureTheory
open scoped ENNReal

namespace RWRS.Support

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

/-! ### Two suprema -/

/-- A supremum of reals over a finite set of indices, taken over all of `ℕ`, is
the maximum of the finite supremum and of `0`, the value the empty supremum
contributes at the indices outside the set. -/
theorem iSup_mem_finset_real (s : Finset ℕ) (hs : s.Nonempty) (hc : ∃ n : ℕ, n ∉ s)
    (g : ℕ → ℝ) : (⨆ n ∈ s, g n) = max (s.sup' hs g) 0 := by
  classical
  have hpt : ∀ n : ℕ, (⨆ _ : n ∈ s, g n) = if n ∈ s then g n else 0 := by
    intro n
    by_cases hn : n ∈ s
    · rw [if_pos hn, ciSup_pos hn]
    · rw [if_neg hn]
      haveI : IsEmpty (n ∈ s) := ⟨hn⟩
      exact Real.iSup_of_isEmpty _
  have hle : ∀ n : ℕ, (if n ∈ s then g n else 0) ≤ max (s.sup' hs g) 0 := by
    intro n
    by_cases hn : n ∈ s
    · exact (if_pos hn).le.trans ((Finset.le_sup' g hn).trans (le_max_left _ _))
    · exact (if_neg hn).le.trans (le_max_right _ _)
  have hbdd : BddAbove (Set.range fun n : ℕ => if n ∈ s then g n else 0) := by
    refine ⟨max (s.sup' hs g) 0, ?_⟩
    rintro y ⟨n, rfl⟩
    exact hle n
  simp only [hpt]
  refine le_antisymm (ciSup_le hle) ?_
  refine max_le ?_ ?_
  · refine Finset.sup'_le hs g fun n hn => ?_
    have h := le_ciSup hbdd n
    rwa [if_pos hn] at h
  · obtain ⟨n, hn⟩ := hc
    have h := le_ciSup hbdd n
    rwa [if_neg hn] at h

/-- Raising a supremum to a positive power: it is enough to bound every term. -/
theorem iSup_rpow_le_of_forall {ι : Sort*} (a : ι → ℝ≥0∞) (R : ℝ≥0∞) {q : ℝ}
    (hq : 0 < q) (h : ∀ i, a i ^ q ≤ R) : (⨆ i, a i) ^ q ≤ R := by
  have hb : (R ^ (1 / q)) ^ q = R := by
    rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hq.ne', ENNReal.rpow_one]
  have hai : ∀ i, a i ≤ R ^ (1 / q) := by
    intro i
    have := h i
    rw [← hb] at this
    exact (ENNReal.rpow_le_rpow_iff hq).1 this
  calc (⨆ i, a i) ^ q ≤ (R ^ (1 / q)) ^ q :=
        ENNReal.rpow_le_rpow (iSup_le hai) hq.le
    _ = R := hb

/-- Measurability of a supremum over a finite set of indices. -/
theorem measurable_iSup_mem_finset {α : Type*} [MeasurableSpace α]
    (s : Finset ℕ) (hs : s.Nonempty) (hc : ∃ n : ℕ, n ∉ s) {F : ℕ → α → ℝ}
    (hF : ∀ n ∈ s, Measurable (F n)) :
    Measurable fun a => ⨆ n ∈ s, F n a := by
  have heq : (fun a => ⨆ n ∈ s, F n a) = fun a => max (s.sup' hs (fun n => F n a)) 0 := by
    funext a
    exact iSup_mem_finset_real s hs hc (fun n => F n a)
  rw [heq]
  have h1 : Measurable (s.sup' hs F) := Finset.measurable_sup' hs hF
  have h2 : (s.sup' hs F) = fun a => s.sup' hs (fun n => F n a) := by
    funext a
    exact Finset.sup'_apply hs F a
  rw [h2] at h1
  exact h1.max measurable_const

/-! ### The scenery read along the trajectory -/

section Meas

variable [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]

/-- Evaluating a scenery at a vertex is measurable, the vertex set being
countable with measurable singletons. -/
theorem measurable_eval : Measurable fun p : (V → ℝ) × V => p.1 p.2 :=
  measurable_from_prod_countable_left fun v => measurable_pi_apply v

/-- The scenery read at the `j`-th position of the trajectory. -/
theorem measurable_scenery_at (j : ℕ) :
    Measurable fun z : (V → ℝ) × (ℕ → V) => z.1 (z.2 j) := by
  have h : Measurable fun z : (V → ℝ) × (ℕ → V) => ((z.1, z.2 j) : (V → ℝ) × V) := by
    fun_prop
  have h2 := measurable_eval.comp h
  simpa [Function.comp_def] using h2

/-- The degree at the `j`-th position of the trajectory. -/
theorem measurable_degree_at (j : ℕ) :
    Measurable fun z : (V → ℝ) × (ℕ → V) => (G.degree (z.2 j) : ℝ) := by
  have h1 : Measurable fun v : V => (G.degree v : ℝ) := measurable_of_countable _
  have h2 : Measurable fun z : (V → ℝ) × (ℕ → V) => z.2 j := by fun_prop
  have h3 := h1.comp h2
  simpa [Function.comp_def] using h3

end Meas

/-- The fluctuation is the sum along the trajectory of the centred scenery. -/
theorem fluctuation_eq_sum (ξ : V → ℝ) (m : ℝ) (n : ℕ) (X : ℕ → V) :
    fluctuation G ξ m n X = ∑ k ∈ Finset.range n, (ξ (X k) - m) / (G.degree (X k) : ℝ) := by
  rw [fluctuation]
  exact tsum_localTime_mul (fun v => ξ v - m) n X

section Meas2

variable [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]

theorem measurable_fluctuation (m : ℝ) (n : ℕ) :
    Measurable fun z : (V → ℝ) × (ℕ → V) => fluctuation G z.1 m n z.2 := by
  simp only [fluctuation_eq_sum]
  exact Finset.measurable_sum _ fun k _ =>
    ((measurable_scenery_at k).sub measurable_const).div (measurable_degree_at k)

end Meas2

/-! ### The dyadic blocks -/

theorem block_nonempty (k : ℕ) : (Finset.Ico (2 ^ k) (2 ^ (k + 1))).Nonempty :=
  Finset.nonempty_Ico.2 (Nat.pow_lt_pow_right one_lt_two (Nat.lt_succ_self k))

theorem block_compl (k : ℕ) : ∃ n : ℕ, n ∉ Finset.Ico (2 ^ k) (2 ^ (k + 1)) := by
  refine ⟨0, fun h => ?_⟩
  have h1 := (Finset.mem_Ico.1 h).1
  have h2 : 0 < 2 ^ k := pow_pos (by norm_num) k
  omega

section Meas3

variable [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]

theorem measurable_dyadicY (m : ℝ) (d k : ℕ) :
    Measurable fun z : (V → ℝ) × (ℕ → V) => dyadicY G z.1 m d k z.2 := by
  simp only [dyadicY]
  refine Measurable.max (Measurable.sub ?_ measurable_const) measurable_const
  exact measurable_iSup_mem_finset _ (block_nonempty k) (block_compl k)
    fun n _ => measurable_fluctuation m n

theorem measurable_dyadicY_rpow (m : ℝ) (d k : ℕ) {q : ℝ} (hq : 0 ≤ q) :
    Measurable fun z : (V → ℝ) × (ℕ → V) =>
      ENNReal.ofReal (dyadicY G z.1 m d k z.2 ^ q) := by
  have h1 : Measurable fun y : ℝ => y ^ q := (Real.continuous_rpow_const hq).measurable
  have h2 := h1.comp (measurable_dyadicY (G := G) m d k)
  have h3 : Measurable fun z : (V → ℝ) × (ℕ → V) => dyadicY G z.1 m d k z.2 ^ q := by
    simpa [Function.comp_def] using h2
  exact h3.ennreal_ofReal

end Meas3

/-- Every positive time lies in the dyadic block of its base-two logarithm. -/
theorem mem_block_log {n : ℕ} (hn : 1 ≤ n) :
    n ∈ Finset.Ico (2 ^ Nat.log 2 n) (2 ^ (Nat.log 2 n + 1)) :=
  Finset.mem_Ico.2 ⟨Nat.pow_log_le_self 2 (Nat.one_le_iff_ne_zero.1 hn),
    Nat.lt_pow_succ_log_self one_lt_two n⟩

/-- **The block bound.**  At a negative mean the payoff at a time in the `k`-th
dyadic block is at most `Y_k`. -/
theorem payoff_le_dyadicY [Infinite V] (hG : G.Connected) {d : ℕ} (hd : BoundedDegree G d)
    (ξ : V → ℝ) {m : ℝ} (hm : m < 0) {n : ℕ} (hn : 1 ≤ n) (X : ℕ → V) :
    payoff G ξ n X ≤ dyadicY G ξ m d (Nat.log 2 n) X := by
  set k := Nat.log 2 n with hk
  have hmem := mem_block_log hn
  rw [← hk] at hmem
  obtain ⟨hlow, hhigh⟩ := Finset.mem_Ico.1 hmem
  have hd1 : 1 ≤ d := le_trans (degree_pos hG (X 0)) (hd (X 0))
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd1
  have hclock : (n : ℝ) / d ≤ ∑ j ∈ Finset.range n, invDeg G (X j) :=
    sum_invDeg_ge hG hd n X
  have hdrift : m * (∑ j ∈ Finset.range n, invDeg G (X j)) ≤ -(|m| / d * 2 ^ k) := by
    have h1 : m * (∑ j ∈ Finset.range n, invDeg G (X j)) ≤ m * ((n : ℝ) / d) :=
      mul_le_mul_of_nonpos_left hclock hm.le
    have h2 : m * ((n : ℝ) / d) ≤ m * ((2 ^ k : ℕ) / (d : ℝ)) := by
      refine mul_le_mul_of_nonpos_left ?_ hm.le
      have hcast : ((2 ^ k : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hlow
      exact div_le_div_of_nonneg_right hcast hdpos.le
    have h3 : m * ((2 ^ k : ℕ) / (d : ℝ)) = -(|m| / d * 2 ^ k) := by
      rw [abs_of_neg hm]
      push_cast
      ring
    linarith
  have hfluc : fluctuation G ξ m n X
      ≤ ⨆ j ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), fluctuation G ξ m j X := by
    rw [iSup_mem_finset_real _ (block_nonempty k) (block_compl k)]
    exact le_trans (Finset.le_sup' (fun j => fluctuation G ξ m j X) hmem) (le_max_left _ _)
  have hsplit := payoff_eq_drift_add (G := G) ξ m n X
  rw [dyadicY]
  refine le_max_of_le_left ?_
  rw [hsplit]
  linarith

/-- **The dyadic bound along one trajectory**, before integration. -/
theorem supPayoff_rpow_le [Infinite V] (hG : G.Connected) {d : ℕ} (hd : BoundedDegree G d)
    (ξ : V → ℝ) {m : ℝ} (hm : m < 0) {q : ℝ} (hq : 0 < q) (X : ℕ → V) :
    supPayoff G ξ X ^ q ≤ ∑' k : ℕ, ENNReal.ofReal (dyadicY G ξ m d k X ^ q) := by
  rw [supPayoff]
  refine iSup_rpow_le_of_forall _ _ hq fun n => ?_
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    rw [payoff]
    simp only [Finset.range_zero, Finset.sum_empty, ENNReal.ofReal_zero]
    rw [ENNReal.zero_rpow_of_pos hq]
    exact bot_le
  · have hle := payoff_le_dyadicY hG hd ξ hm hn X
    have hY : 0 ≤ dyadicY G ξ m d (Nat.log 2 n) X := le_max_right _ _
    calc ENNReal.ofReal (payoff G ξ n X) ^ q
        ≤ ENNReal.ofReal (dyadicY G ξ m d (Nat.log 2 n) X) ^ q :=
          ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hle) hq.le
      _ = ENNReal.ofReal (dyadicY G ξ m d (Nat.log 2 n) X ^ q) :=
          ENNReal.ofReal_rpow_of_nonneg hY hq.le
      _ ≤ ∑' k : ℕ, ENNReal.ofReal (dyadicY G ξ m d k X ^ q) := ENNReal.le_tsum _

end RWRS.Support
