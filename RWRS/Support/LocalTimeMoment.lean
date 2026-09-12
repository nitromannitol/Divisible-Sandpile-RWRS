/-
The moments of the local time under the spectral dimension bound.

The `q`-th moment of the local time at the starting vertex is bounded by
`q!` times the `q`-th power of the clock, by induction on `⌈q⌉`: the pathwise
inequality turns the `q`-th moment into a sum over the visits of the
`(q-1)`-st moment of the remaining local time, the Markov property restarts the
average at each visit at the cost of the diagonal heat kernel, and the diagonal
heat kernel sums to the clock.  Below the first integer the bound is Jensen's
inequality for a concave power.
-/
import RWRS.Support.LocalTimeClock
import RWRS.Support.Sensitivity

namespace RWRS.Support

open scoped Classical

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

/-- The local time as a sum of indicators. -/
theorem localTime_eq_sum (n : ℕ) (v : V) (X : ℕ → V) :
    ((RWRS.localTime n v X : ℕ) : ℝ)
      = ∑ k ∈ Finset.range n, (if X k = v then (1 : ℝ) else 0) := by
  classical
  rw [RWRS.localTime, Finset.card_filter]
  push_cast
  rfl

/-- The diagonal heat kernel is at most the clock term. -/
theorem heat_diag_le_clockTerm {d_s A : ℝ} (_hds : 0 < d_s)
    (hsp : RWRS.SpectralDimensionBound G d_s A) (k : ℕ) (v : V) :
    heat G k v v ≤ max A 1 * clockTerm (d_s / 2) k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have h0 : heat G 0 v v = 1 := by simp [heat]
    have hc : clockTerm (d_s / 2) 0 = 1 := by simp [clockTerm]
    rw [h0, hc, mul_one]
    exact le_max_right _ _
  · have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hc : clockTerm (d_s / 2) k = (k : ℝ) ^ (-(d_s / 2)) := by
      rw [clockTerm, max_eq_left hk1]
    have hcpos : (0 : ℝ) < (k : ℝ) ^ (-(d_s / 2)) :=
      Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hk1) _
    have hbound := hsp v k hk
    rw [show (-d_s / 2 : ℝ) = -(d_s / 2) by ring] at hbound
    rw [hc]
    refine le_trans hbound ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hcpos.le

/-- The clock of the section. -/
noncomputable def clockH (A d_s : ℝ) (n : ℕ) : ℝ := max A 1 * clockSum (d_s / 2) n

theorem one_le_clockH (A d_s : ℝ) {n : ℕ} (hn : 1 ≤ n) : 1 ≤ clockH A d_s n := by
  have h1 : (1 : ℝ) ≤ max A 1 := le_max_right _ _
  have h2 : (1 : ℝ) ≤ clockSum (d_s / 2) n := one_le_clockSum hn
  rw [clockH]
  nlinarith

theorem clockH_pos (A d_s : ℝ) {n : ℕ} (hn : 1 ≤ n) : 0 < clockH A d_s n :=
  lt_of_lt_of_le zero_lt_one (one_le_clockH A d_s hn)

theorem clockH_mono (A d_s : ℝ) {a b : ℕ} (hab : a ≤ b) : clockH A d_s a ≤ clockH A d_s b := by
  refine mul_le_mul_of_nonneg_left (clockSum_mono _ hab) ?_
  exact le_trans zero_le_one (le_max_right _ _)

/-- The diagonal heat kernel sums to the clock. -/
theorem sum_heat_diag_le {d_s A : ℝ} (hds : 0 < d_s)
    (hsp : RWRS.SpectralDimensionBound G d_s A) (n : ℕ) (v : V) :
    ∑ k ∈ Finset.range n, heat G k v v ≤ clockH A d_s n := by
  rw [clockH, clockSum, Finset.mul_sum]
  exact Finset.sum_le_sum fun k _ => heat_diag_le_clockTerm hds hsp k v

/-- The mean local time at the starting vertex. -/
theorem walkExp_localTime_eq [Infinite V] (hG : G.Connected) (n : ℕ) (v : V) :
    walkExp G n v (fun X => ((RWRS.localTime n v X : ℕ) : ℝ))
      = ∑ k ∈ Finset.range n, heat G k v v := by
  classical
  rw [show (fun X : ℕ → V => ((RWRS.localTime n v X : ℕ) : ℝ))
      = fun X => ∑ k ∈ Finset.range n, (if X k = v then (1 : ℝ) else 0) from
    funext fun X => localTime_eq_sum n v X]
  rw [walkExp_finsetSum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := le_of_lt (Finset.mem_range.1 hk)
  have := walkExp_markov (G := G) v (fun _ => (1 : ℝ)) k n v hkn
  rw [walkExp_const hG _ v (1 : ℝ), mul_one] at this
  rw [← this]
  exact walkExp_congr fun X _ => by rw [mul_one]

/-- **Jensen's inequality for a concave power.** -/
theorem walkExp_rpow_le_of_le_one [Infinite V] (hG : G.Connected) {q : ℝ} (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1) {n : ℕ} {x : V} {Φ : (ℕ → V) → ℝ} (hΦ : ∀ X, 0 ≤ Φ X)
    (ha : 0 < walkExp G n x Φ) :
    walkExp G n x (fun X => (Φ X) ^ q) ≤ (walkExp G n x Φ) ^ q := by
  set a : ℝ := walkExp G n x Φ with hadef
  have hkey : ∀ X, (Φ X) ^ q ≤ (q * Φ X + (1 - q) * a) * a ^ (q - 1) := by
    intro X
    have hgm := Real.geom_mean_le_arith_mean2_weighted hq0 (by linarith : (0:ℝ) ≤ 1 - q)
      (hΦ X) ha.le (by ring)
    have hap : (0 : ℝ) < a ^ (q - 1) := Real.rpow_pos_of_pos ha _
    have hmul := mul_le_mul_of_nonneg_right hgm hap.le
    have hcollapse : (Φ X) ^ q * a ^ (1 - q) * a ^ (q - 1) = (Φ X) ^ q := by
      rw [mul_assoc, ← Real.rpow_add ha]
      norm_num
    rw [hcollapse] at hmul
    exact hmul
  refine le_trans (walkExp_mono hkey) ?_
  have hlin : walkExp G n x (fun X => (q * Φ X + (1 - q) * a) * a ^ (q - 1))
      = (q * a + (1 - q) * a) * a ^ (q - 1) := by
    rw [show (fun X : ℕ → V => (q * Φ X + (1 - q) * a) * a ^ (q - 1))
        = fun X => a ^ (q - 1) * (q * Φ X + (1 - q) * a) from funext fun X => by ring]
    have h2 : walkExp G n x (fun _ : ℕ → V => (1 - q) * a) = (1 - q) * a :=
      walkExp_const hG n x _
    have hinner : walkExp G n x (fun X => q * Φ X + (1 - q) * a) = q * a + (1 - q) * a := by
      rw [walkExp_add, walkExp_const_mul, h2, ← hadef]
    rw [walkExp_const_mul, hinner]
    ring
  rw [hlin]
  have hcollapse : (q * a + (1 - q) * a) * a ^ (q - 1) = a ^ q := by
    have : q * a + (1 - q) * a = a := by ring
    rw [this]
    nth_rewrite 1 [show a = a ^ (1 : ℝ) from (Real.rpow_one a).symm]
    rw [← Real.rpow_add ha]
    norm_num
  rw [hcollapse]

/-- The constant of the induction, `(j+1)!`. -/
noncomputable def momConst (j : ℕ) : ℝ := (Nat.factorial (j + 1) : ℝ)

theorem momConst_pos (j : ℕ) : 0 < momConst j := by
  rw [momConst]
  exact_mod_cast Nat.factorial_pos _

theorem momConst_mono (j : ℕ) : momConst j ≤ momConst (j + 1) := by
  rw [momConst, momConst]
  exact_mod_cast Nat.factorial_le (by omega)

theorem momConst_succ (j : ℕ) : momConst (j + 1) = ((j : ℝ) + 2) * momConst j := by
  rw [momConst, momConst, show j + 1 + 1 = (j + 1) + 1 from rfl, Nat.factorial_succ]
  push_cast
  ring

/-- **The moments of the local time at the starting vertex.** -/
theorem walkExp_localTime_rpow_le [Infinite V] (hG : G.Connected) {d_s A : ℝ}
    (hds : 0 < d_s) (hsp : RWRS.SpectralDimensionBound G d_s A) :
    ∀ (j : ℕ) (q : ℝ), 0 ≤ q → q ≤ (j : ℝ) + 1 → ∀ (n : ℕ), 1 ≤ n → ∀ v : V,
      walkExp G n v (fun X => ((RWRS.localTime n v X : ℕ) : ℝ) ^ q)
        ≤ momConst j * clockH A d_s n ^ q := by
  intro j
  induction j with
  | zero =>
      intro q hq0 hq1 n hn v
      have hmean := walkExp_localTime_eq hG n v
      have hpos : 0 < walkExp G n v (fun X => ((RWRS.localTime n v X : ℕ) : ℝ)) := by
        rw [hmean]
        refine lt_of_lt_of_le zero_lt_one ?_
        have h0 : heat G 0 v v = 1 := by simp [heat]
        rw [← h0]
        refine Finset.single_le_sum (f := fun k => heat G k v v)
          (fun k _ => heat_nonneg k v v) (Finset.mem_range.2 (by omega))
      have hjen := walkExp_rpow_le_of_le_one hG hq0 (by simpa using hq1)
        (Φ := fun X => ((RWRS.localTime n v X : ℕ) : ℝ))
        (fun X => Nat.cast_nonneg _) hpos
      refine le_trans hjen ?_
      have hle : walkExp G n v (fun X => ((RWRS.localTime n v X : ℕ) : ℝ)) ≤ clockH A d_s n := by
        rw [hmean]
        exact sum_heat_diag_le hds hsp n v
      have hmono : walkExp G n v (fun X => ((RWRS.localTime n v X : ℕ) : ℝ)) ^ q
          ≤ clockH A d_s n ^ q := Real.rpow_le_rpow hpos.le hle hq0
      have hm : momConst 0 = 1 := by rw [momConst]; norm_num
      rw [hm, one_mul]
      exact hmono
  | succ j ih =>
      intro q hq0 hq1 n hn v
      rcases le_or_gt q ((j : ℝ) + 1) with hq | hq
      · refine le_trans (ih q hq0 hq n hn v) ?_
        have hpow : (0 : ℝ) ≤ clockH A d_s n ^ q :=
          (Real.rpow_pos_of_pos (clockH_pos A d_s hn) q).le
        exact mul_le_mul_of_nonneg_right (momConst_mono j) hpow
      · -- the descent
        have hq1' : (1 : ℝ) ≤ q := by
          have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
          linarith
        have hpath : ∀ X : ℕ → V, ((RWRS.localTime n v X : ℕ) : ℝ) ^ q
            ≤ q * ∑ k ∈ Finset.range n, (if X k = v then (1 : ℝ) else 0)
                * ((tailTime k n v X : ℕ) : ℝ) ^ (q - 1) :=
          fun X => localTime_rpow_le hq1' n v X
        refine le_trans (walkExp_mono hpath) ?_
        rw [walkExp_const_mul, walkExp_finsetSum]
        have hterm : ∀ k ∈ Finset.range n,
            walkExp G n v (fun X => (if X k = v then (1 : ℝ) else 0)
                * ((tailTime k n v X : ℕ) : ℝ) ^ (q - 1))
              ≤ heat G k v v * (momConst j * clockH A d_s n ^ (q - 1)) := by
          intro k hk
          have hklt : k < n := Finset.mem_range.1 hk
          have hkn : k ≤ n := le_of_lt hklt
          have hrw : walkExp G n v (fun X => (if X k = v then (1 : ℝ) else 0)
              * ((tailTime k n v X : ℕ) : ℝ) ^ (q - 1))
              = heat G k v v * walkExp G (n - k) v
                  (fun Y => ((RWRS.localTime (n - k) v Y : ℕ) : ℝ) ^ (q - 1)) := by
            rw [← walkExp_markov (G := G) v
              (fun Y => ((RWRS.localTime (n - k) v Y : ℕ) : ℝ) ^ (q - 1)) k n v hkn]
            refine walkExp_congr fun X _ => ?_
            rw [tailTime_eq_localTime]
          rw [hrw]
          have hnk : 1 ≤ n - k := by omega
          have hq1c : q ≤ (j : ℝ) + 2 := by push_cast at hq1; linarith
          have hsub := ih (q - 1) (by linarith) (by linarith) (n - k) hnk v
          have hchain : walkExp G (n - k) v
              (fun Y => ((RWRS.localTime (n - k) v Y : ℕ) : ℝ) ^ (q - 1))
              ≤ momConst j * clockH A d_s n ^ (q - 1) := by
            refine le_trans hsub ?_
            have hmono : clockH A d_s (n - k) ^ (q - 1) ≤ clockH A d_s n ^ (q - 1) :=
              Real.rpow_le_rpow (clockH_pos A d_s hnk).le (clockH_mono A d_s (by omega))
                (by linarith)
            exact mul_le_mul_of_nonneg_left hmono (momConst_pos j).le
          exact mul_le_mul_of_nonneg_left hchain (heat_nonneg k v v)
        refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (by linarith)) ?_
        rw [← Finset.sum_mul]
        have hsum := sum_heat_diag_le hds hsp n v
        have hC : (0 : ℝ) ≤ momConst j * clockH A d_s n ^ (q - 1) := by
          have := (Real.rpow_pos_of_pos (clockH_pos A d_s hn) (q - 1)).le
          have := (momConst_pos j).le
          positivity
        have hstep : q * ((∑ k ∈ Finset.range n, heat G k v v)
            * (momConst j * clockH A d_s n ^ (q - 1)))
            ≤ q * (clockH A d_s n * (momConst j * clockH A d_s n ^ (q - 1))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by linarith)
          exact mul_le_mul_of_nonneg_right hsum hC
        refine le_trans hstep ?_
        have hcollapse : clockH A d_s n * clockH A d_s n ^ (q - 1) = clockH A d_s n ^ q := by
          nth_rewrite 1 [show clockH A d_s n = clockH A d_s n ^ (1 : ℝ) from
            (Real.rpow_one _).symm]
          rw [← Real.rpow_add (clockH_pos A d_s hn)]
          norm_num
        have heq : q * (clockH A d_s n * (momConst j * clockH A d_s n ^ (q - 1)))
            = q * momConst j * clockH A d_s n ^ q := by
          rw [← hcollapse]; ring
        rw [heq, momConst_succ]
        have hpow : (0 : ℝ) ≤ clockH A d_s n ^ q :=
          (Real.rpow_pos_of_pos (clockH_pos A d_s hn) q).le
        refine mul_le_mul_of_nonneg_right ?_ hpow
        have : q ≤ (j : ℝ) + 2 := by push_cast at hq1; linarith
        nlinarith [momConst_pos j, this]

end RWRS.Support
