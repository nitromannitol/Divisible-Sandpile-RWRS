/-
The dyadic decomposition of a time interval, and the chaining decomposition of
the fluctuation.

`prop:subcritical` cuts `W_n`, for `2^k ≤ n < 2^{k+1}`, into at most `k+1`
increments over dyadic intervals.  The cut used here is the sequence of
roundings `n_j = 2^{k-j}⌊n/2^{k-j}⌋`: it starts at `n_0 = 2^k`, ends at
`n_k = n`, increases, and each step `n_{j+1} - n_j` is either empty or the
dyadic interval `[i·2^{k-j-1}, (i+1)·2^{k-j-1})` with `i < 2^{j+2}`.  So the
fluctuation at every time of the block is a sum of at most `k+1` increments over
dyadic intervals, which is what the union bound of `eq:Mk-tail-Ak` counts.
-/
import RWRS.Support.SubIncrement

namespace RWRS.Support

open scoped ENNReal

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

/-- The time `n` rounded down to a multiple of `2 ^ (k - j)`. -/
def dyTrunc (k n j : ℕ) : ℕ := 2 ^ (k - j) * (n / 2 ^ (k - j))

theorem dyTrunc_last (k n : ℕ) : dyTrunc k n k = n := by
  unfold dyTrunc
  simp

theorem dyTrunc_zero {k n : ℕ} (h1 : 2 ^ k ≤ n) (h2 : n < 2 ^ (k + 1)) :
    dyTrunc k n 0 = 2 ^ k := by
  unfold dyTrunc
  rw [Nat.sub_zero]
  have hdiv : n / 2 ^ k = 1 := by
    refine Nat.div_eq_of_lt_le ?_ ?_
    · simpa using h1
    · have h : (1 + 1) * 2 ^ k = 2 ^ (k + 1) := by ring
      omega
  rw [hdiv, mul_one]

theorem dyTrunc_le_self (k n j : ℕ) : dyTrunc k n j ≤ n :=
  Nat.mul_div_le n (2 ^ (k - j))

/-- The roundings increase with the index. -/
theorem dyTrunc_le_of_le (k n : ℕ) {j j' : ℕ} (h : j ≤ j') :
    dyTrunc k n j ≤ dyTrunc k n j' := by
  unfold dyTrunc
  have hab : k - j' ≤ k - j := Nat.sub_le_sub_left h k
  have hdvd : (2:ℕ) ^ (k - j') ∣ 2 ^ (k - j) := pow_dvd_pow 2 hab
  have hcn : 2 ^ (k - j) * (n / 2 ^ (k - j)) ≤ n := Nat.mul_div_le n (2 ^ (k - j))
  obtain ⟨t, ht⟩ := Dvd.dvd.mul_right hdvd (n / 2 ^ (k - j))
  have hpos : 0 < (2:ℕ) ^ (k - j') := pow_pos (by norm_num : 0 < 2) _
  have ht' : (2 ^ (k - j) * (n / 2 ^ (k - j))) / 2 ^ (k - j') = t := by
    rw [ht]; exact Nat.mul_div_cancel_left t hpos
  have hle : (2 ^ (k - j) * (n / 2 ^ (k - j))) / 2 ^ (k - j') ≤ n / 2 ^ (k - j') :=
    Nat.div_le_div_right hcn
  calc 2 ^ (k - j) * (n / 2 ^ (k - j)) = 2 ^ (k - j') * t := ht
    _ ≤ 2 ^ (k - j') * (n / 2 ^ (k - j')) := by
        refine Nat.mul_le_mul_left _ ?_
        rw [← ht']
        exact hle

theorem monotone_dyTrunc (k n : ℕ) : Monotone (dyTrunc k n) :=
  fun _ _ h => dyTrunc_le_of_le k n h

/-- Each step of the rounding sequence is empty or a dyadic interval of length
`2 ^ (k - j - 1)` whose index is below `2 ^ (j + 2)`. -/
theorem dyTrunc_step {k n j : ℕ} (hj : j < k) (h2 : n < 2 ^ (k + 1)) :
    dyTrunc k n (j + 1) = dyTrunc k n j ∨
      ∃ i : ℕ, i < 2 ^ (j + 2) ∧ dyTrunc k n j = i * 2 ^ (k - j - 1) ∧
        dyTrunc k n (j + 1) = (i + 1) * 2 ^ (k - j - 1) := by
  have hs : k - j = (k - j - 1) + 1 := by omega
  set s : ℕ := k - j - 1 with hsdef
  have hj1 : k - (j + 1) = s := by omega
  set q : ℕ := n / 2 ^ s with hq
  have hqval : dyTrunc k n (j + 1) = 2 ^ s * q := by
    unfold dyTrunc; rw [hj1]
  have hdiv2 : n / 2 ^ (s + 1) = q / 2 := by
    rw [hq, Nat.div_div_eq_div_mul, pow_succ]
  have hjval : dyTrunc k n j = 2 ^ (s + 1) * (q / 2) := by
    unfold dyTrunc; rw [hs, hdiv2]
  rcases Nat.even_or_odd q with he | ho
  · left
    obtain ⟨c, hc⟩ := he
    have hq2 : q / 2 = c := by omega
    rw [hqval, hjval, hq2, pow_succ, hc]
    ring
  · right
    obtain ⟨c, hc⟩ := ho
    have hq2 : q / 2 = c := by omega
    have hpow : 2 ^ s * 2 ^ (j + 2) = 2 ^ (k + 1) := by
      rw [← pow_add]; congr 1; omega
    have hle : 2 ^ s * q ≤ n := by rw [← hqval]; exact dyTrunc_le_self k n (j + 1)
    have hqlt : q < 2 ^ (j + 2) := by
      by_contra hcon
      rw [not_lt] at hcon
      have h6 : (2:ℕ) ^ (k + 1) ≤ 2 ^ s * q := by
        rw [← hpow]; exact Nat.mul_le_mul_left _ hcon
      exact absurd (lt_of_lt_of_le h2 (le_trans h6 hle)) (lt_irrefl n)
    refine ⟨2 * c, by omega, ?_, ?_⟩
    · rw [hjval, hq2, pow_succ]; ring
    · rw [hqval, hc]; ring

/-! ### The chaining decomposition of the fluctuation -/

/-- The increments over the steps of a monotone sequence of times telescope. -/
theorem fluctOn_sum_range (ξ : V → ℝ) (m : ℝ) (X : ℕ → V) (a : ℕ → ℕ)
    (ha : Monotone a) (J : ℕ) :
    ∑ j ∈ Finset.range J, fluctOn G ξ m (a j) (a (j + 1)) X
      = fluctOn G ξ m (a 0) (a J) X := by
  induction J with
  | zero =>
      simp only [Finset.range_zero, Finset.sum_empty]
      unfold fluctOn
      simp
  | succ J ih =>
      rw [Finset.sum_range_succ, ih]
      exact fluctOn_add ξ m (ha (Nat.zero_le J)) (ha (Nat.le_succ J)) X

/-- **The chaining decomposition**: the fluctuation at a time of the `k`-th
dyadic block is the increment over `[0,2^k)` plus the `k` increments over the
steps of the rounding sequence. -/
theorem fluctuation_eq_chain (ξ : V → ℝ) (m : ℝ) (X : ℕ → V) {k n : ℕ}
    (h1 : 2 ^ k ≤ n) (h2 : n < 2 ^ (k + 1)) :
    RWRS.fluctuation G ξ m n X
      = fluctOn G ξ m 0 (2 ^ k) X
        + ∑ j ∈ Finset.range k, fluctOn G ξ m (dyTrunc k n j) (dyTrunc k n (j + 1)) X := by
  rw [fluctuation_eq_fluctOn, fluctOn_sum_range ξ m X (dyTrunc k n) (monotone_dyTrunc k n) k,
    dyTrunc_zero h1 h2, dyTrunc_last]
  exact (fluctOn_add ξ m (Nat.zero_le _) h1 X).symm

/-- **The union bound of `eq:Mk-tail-Ak`, in its pathwise form**: if every one
of the `k+1` increments of the chaining decomposition is at most `u/(k+1)` in
absolute value, then the fluctuation at every time of the block is at most `u`. -/
theorem fluctuation_le_of_increments (ξ : V → ℝ) (m : ℝ) (X : ℕ → V) {k n : ℕ} {u : ℝ}
    (h1 : 2 ^ k ≤ n) (h2 : n < 2 ^ (k + 1))
    (hbase : |fluctOn G ξ m 0 (2 ^ k) X| ≤ u / ((k : ℝ) + 1))
    (hsteps : ∀ j ∈ Finset.range k,
      |fluctOn G ξ m (dyTrunc k n j) (dyTrunc k n (j + 1)) X| ≤ u / ((k : ℝ) + 1)) :
    RWRS.fluctuation G ξ m n X ≤ u := by
  have hk1 : (0:ℝ) < (k : ℝ) + 1 := by positivity
  have hsum : ∑ j ∈ Finset.range k,
      fluctOn G ξ m (dyTrunc k n j) (dyTrunc k n (j + 1)) X ≤ (k : ℝ) * (u / ((k : ℝ) + 1)) := by
    calc ∑ j ∈ Finset.range k, fluctOn G ξ m (dyTrunc k n j) (dyTrunc k n (j + 1)) X
        ≤ ∑ _j ∈ Finset.range k, u / ((k : ℝ) + 1) :=
          Finset.sum_le_sum fun j hj => le_trans (le_abs_self _) (hsteps j hj)
      _ = (k : ℝ) * (u / ((k : ℝ) + 1)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hb : fluctOn G ξ m 0 (2 ^ k) X ≤ u / ((k : ℝ) + 1) :=
    le_trans (le_abs_self _) hbase
  rw [fluctuation_eq_chain ξ m X h1 h2]
  have : fluctOn G ξ m 0 (2 ^ k) X
      + ∑ j ∈ Finset.range k, fluctOn G ξ m (dyTrunc k n j) (dyTrunc k n (j + 1)) X
      ≤ ((k : ℝ) + 1) * (u / ((k : ℝ) + 1)) := by linarith
  rwa [mul_div_cancel₀ u (ne_of_gt hk1)] at this

end RWRS.Support
