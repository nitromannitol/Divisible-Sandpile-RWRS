/-
The pathwise inequality behind the local-time moments.

If a vertex is visited `m` times before time `n`, then listing the visits in
order and recording, at each visit, how many visits remain, runs through
`1,…,m` exactly once.  Bernoulli's inequality turns `∑_{i≤m} i^{p-1} ≥ m^p/p`
into the bound the induction on `p` uses: the `p`-th moment of the local time is
at most `p` times the sum, over the visits, of the `(p-1)`-st power of the
number of remaining visits.
-/
import RWRS.Support.LocalTimeMarkov
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

namespace RWRS.Support

open scoped Classical

variable {V : Type*}

/-- The number of visits to `v` in the window `[k,n)`. -/
noncomputable def tailTime (k n : ℕ) (v : V) (X : ℕ → V) : ℕ :=
  ((Finset.Ico k n).filter (fun j => X j = v)).card

/-- The visits to `v` before time `n` in the window `[k,n)` are the local time of
the shifted trajectory. -/
theorem tailTime_eq_localTime (k n : ℕ) (v : V) (X : ℕ → V) :
    tailTime k n v X = RWRS.localTime (n - k) v (fun j => X (k + j)) := by
  classical
  rw [tailTime, RWRS.localTime]
  refine Finset.card_bij (fun i _ => i - k) ?_ ?_ ?_
  · intro i hi
    rw [Finset.mem_filter, Finset.mem_Ico] at hi
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_⟩
    rw [show k + (i - k) = i by omega]
    exact hi.2
  · intro i hi j hj hij
    rw [Finset.mem_filter, Finset.mem_Ico] at hi hj
    omega
  · intro j hj
    rw [Finset.mem_filter, Finset.mem_range] at hj
    refine ⟨k + j, ?_, by omega⟩
    rw [Finset.mem_filter, Finset.mem_Ico]
    exact ⟨⟨by omega, by omega⟩, hj.2⟩

/-- The visits to `v` before time `n`. -/
noncomputable def visitSet (n : ℕ) (v : V) (X : ℕ → V) : Finset ℕ :=
  (Finset.range n).filter (fun k => X k = v)

theorem card_visitSet (n : ℕ) (v : V) (X : ℕ → V) :
    (visitSet n v X).card = RWRS.localTime n v X := rfl

theorem one_le_tailTime {n k : ℕ} {v : V} {X : ℕ → V} (hk : k ∈ visitSet n v X) :
    1 ≤ tailTime k n v X := by
  classical
  rw [visitSet, Finset.mem_filter, Finset.mem_range] at hk
  refine Finset.card_pos.2 ⟨k, ?_⟩
  rw [Finset.mem_filter, Finset.mem_Ico]
  exact ⟨⟨le_rfl, hk.1⟩, hk.2⟩

theorem tailTime_le (k n : ℕ) (v : V) (X : ℕ → V) :
    tailTime k n v X ≤ RWRS.localTime n v X := by
  classical
  refine Finset.card_le_card fun j hj => ?_
  rw [Finset.mem_filter, Finset.mem_Ico] at hj
  rw [Finset.mem_filter, Finset.mem_range]
  exact ⟨hj.1.2, hj.2⟩

/-- At a later visit fewer visits remain. -/
theorem tailTime_lt {n k k' : ℕ} {v : V} {X : ℕ → V} (hk : k ∈ visitSet n v X)
    (hkk : k < k') : tailTime k' n v X < tailTime k n v X := by
  classical
  rw [visitSet, Finset.mem_filter, Finset.mem_range] at hk
  refine Finset.card_lt_card ⟨fun j hj => ?_, fun hsub => ?_⟩
  · rw [Finset.mem_filter, Finset.mem_Ico] at hj ⊢
    exact ⟨⟨by omega, hj.1.2⟩, hj.2⟩
  · have hmem : k ∈ (Finset.Ico k n).filter (fun j => X j = v) := by
      rw [Finset.mem_filter, Finset.mem_Ico]
      exact ⟨⟨le_rfl, hk.1⟩, hk.2⟩
    have := hsub hmem
    rw [Finset.mem_filter, Finset.mem_Ico] at this
    omega

/-- **The remaining-visit counts run through `1,…,m`.** -/
theorem image_tailTime (n : ℕ) (v : V) (X : ℕ → V) :
    (visitSet n v X).image (fun k => tailTime k n v X)
      = Finset.Icc 1 (RWRS.localTime n v X) := by
  classical
  have hinj : ∀ a ∈ visitSet n v X, ∀ b ∈ visitSet n v X,
      tailTime a n v X = tailTime b n v X → a = b := by
    intro a ha b hb hab
    rcases lt_trichotomy a b with h | h | h
    · exact absurd hab (ne_of_gt (tailTime_lt ha h))
    · exact h
    · exact absurd hab.symm (ne_of_gt (tailTime_lt hb h))
  refine Finset.eq_of_subset_of_card_le (fun i hi => ?_) ?_
  · rw [Finset.mem_image] at hi
    obtain ⟨k, hk, rfl⟩ := hi
    rw [Finset.mem_Icc]
    exact ⟨one_le_tailTime hk, tailTime_le k n v X⟩
  · rw [Nat.card_Icc, Finset.card_image_of_injOn hinj, card_visitSet]
    omega

/-- The sum over the visits of a function of the remaining-visit count. -/
theorem sum_visitSet_tailTime (n : ℕ) (v : V) (X : ℕ → V) (f : ℕ → ℝ) :
    ∑ k ∈ visitSet n v X, f (tailTime k n v X)
      = ∑ i ∈ Finset.Icc 1 (RWRS.localTime n v X), f i := by
  classical
  have hinj : ∀ a ∈ visitSet n v X, ∀ b ∈ visitSet n v X,
      tailTime a n v X = tailTime b n v X → a = b := by
    intro a ha b hb hab
    rcases lt_trichotomy a b with h | h | h
    · exact absurd hab (ne_of_gt (tailTime_lt ha h))
    · exact h
    · exact absurd hab.symm (ne_of_gt (tailTime_lt hb h))
  rw [← image_tailTime n v X, Finset.sum_image hinj]

/-! ### Bernoulli -/

/-- **The `p`-th power is at most `p` times the sum of the `(p-1)`-st powers.** -/
theorem pow_le_mul_sum_pow {p : ℝ} (hp : 1 ≤ p) :
    ∀ m : ℕ, (m : ℝ) ^ p ≤ p * ∑ i ∈ Finset.Icc 1 m, (i : ℝ) ^ (p - 1) := by
  intro m
  induction m with
  | zero =>
      simp only [Nat.cast_zero, Nat.Icc_eq_range']
      rw [Real.zero_rpow (by linarith)]
      simp
  | succ m ih =>
      set a : ℝ := (m : ℝ) + 1 with ha
      have hapos : (0 : ℝ) < a := by rw [ha]; positivity
      have ha1 : (1 : ℝ) ≤ a := by rw [ha]; simp
      have hs : (-1 : ℝ) ≤ -1 / a := by
        rw [neg_div, neg_le_neg_iff, div_le_one hapos]
        exact ha1
      have hbern := one_add_mul_self_le_rpow_one_add hs hp
      have hrw : (1 : ℝ) + -1 / a = (m : ℝ) / a := by
        field_simp
        linarith [ha]
      rw [hrw, Real.div_rpow (Nat.cast_nonneg m) hapos.le] at hbern
      have hap : (0 : ℝ) < a ^ p := Real.rpow_pos_of_pos hapos p
      have hmul : a ^ p * (1 + p * (-1 / a)) ≤ (m : ℝ) ^ p := by
        have := mul_le_mul_of_nonneg_left hbern hap.le
        rwa [mul_div_cancel₀ _ (ne_of_gt hap)] at this
      have hsub : a ^ p * (1 + p * (-1 / a)) = a ^ p - p * a ^ (p - 1) := by
        have hdiv : a ^ (p - 1) = a ^ p / a := by
          rw [Real.rpow_sub hapos, Real.rpow_one]
        rw [hdiv]
        field_simp
        ring
      rw [hsub] at hmul
      have hIcc : ∑ i ∈ Finset.Icc 1 (m + 1), (i : ℝ) ^ (p - 1)
          = (∑ i ∈ Finset.Icc 1 m, (i : ℝ) ^ (p - 1)) + a ^ (p - 1) := by
        rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1)]
        congr 2
        rw [ha]
        push_cast
        ring
      rw [hIcc]
      have hcast : ((m + 1 : ℕ) : ℝ) = a := by rw [ha]; push_cast; ring
      rw [hcast]
      nlinarith [hmul, ih, hp]

/-- **The pathwise bound.** -/
theorem localTime_rpow_le {p : ℝ} (hp : 1 ≤ p) (n : ℕ) (v : V) (X : ℕ → V) :
    (RWRS.localTime n v X : ℝ) ^ p
      ≤ p * ∑ k ∈ Finset.range n,
          (if X k = v then (1 : ℝ) else 0) * (tailTime k n v X : ℝ) ^ (p - 1) := by
  classical
  have hfilter : ∑ k ∈ Finset.range n,
      (if X k = v then (1 : ℝ) else 0) * (tailTime k n v X : ℝ) ^ (p - 1)
      = ∑ k ∈ visitSet n v X, (tailTime k n v X : ℝ) ^ (p - 1) := by
    rw [visitSet, Finset.sum_filter]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : X k = v
    · rw [if_pos hk, if_pos hk, one_mul]
    · rw [if_neg hk, if_neg hk, zero_mul]
  rw [hfilter, sum_visitSet_tailTime n v X (fun i => (i : ℝ) ^ (p - 1))]
  exact pow_le_mul_sum_pow hp _

end RWRS.Support
