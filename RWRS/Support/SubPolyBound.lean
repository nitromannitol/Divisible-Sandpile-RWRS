/-
The deterministic bounds of Steps 4 and 5 of `prop:poly-growth`.

The recentred coordinate at a site is bounded by that site's level plus the
lower truncation level, so the increment of the recentred field over a discrete
interval is bounded by the length of the interval times the largest level among
the sites it visits, and so is the block variable `Y_k`.  That is the estimate
`Y_k ≤ CNR_N^β` on the good-walk event and `Y_k ≤ CN^{1+β}` off it; which of the
two is in force depends only on how far the trajectory has travelled.  The
weights of an increment and their squares are controlled on the good-walk event
by `lem:good-walk`, exactly as in `prop:subcritical`.
-/
import RWRS.Support.SubPolyWalk

namespace RWRS.Support

open MeasureTheory
open scoped ENNReal Classical

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite] {ρ : Measure ℝ}

/-- **The increment of the recentred field over an interval is bounded by the
length of the interval times the largest level it visits.** -/
theorem abs_fluctOn_zetaField_le [IsProbabilityMeasure ρ] {M m : ℝ} {t : V → ℝ}
    (ht : ∀ v : V, -M ≤ t v) (hdeg : ∀ v : V, 1 ≤ G.degree v) (ξ : V → ℝ) (a b : ℕ)
    (X : ℕ → V) {T : ℝ} (_hTM : 0 ≤ T + M)
    (hT : ∀ j : ℕ, a ≤ j → j < b → t (X j) ≤ T) :
    |fluctOn G (zetaField ρ M m t ξ) m a b X| ≤ ((b - a : ℕ) : ℝ) * (T + M) := by
  have hterm : ∀ j ∈ Finset.Ico a b,
      |(zetaField ρ M m t ξ (X j) - m) / (G.degree (X j) : ℝ)| ≤ T + M := by
    intro j hj
    rw [Finset.mem_Ico] at hj
    have hd : (1:ℝ) ≤ (G.degree (X j) : ℝ) := by exact_mod_cast hdeg (X j)
    have hnum : |zetaField ρ M m t ξ (X j) - m| ≤ t (X j) + M :=
      abs_siteShift_sub_le ρ (ht (X j)) (ξ (X j))
    have hlev : t (X j) + M ≤ T + M := by linarith [hT j hj.1 hj.2]
    rw [abs_div, abs_of_nonneg (by linarith : (0:ℝ) ≤ (G.degree (X j) : ℝ))]
    calc |zetaField ρ M m t ξ (X j) - m| / (G.degree (X j) : ℝ)
        ≤ |zetaField ρ M m t ξ (X j) - m| := div_le_self (abs_nonneg _) hd
      _ ≤ T + M := le_trans hnum hlev
  calc |fluctOn G (zetaField ρ M m t ξ) m a b X|
      ≤ ∑ j ∈ Finset.Ico a b, |(zetaField ρ M m t ξ (X j) - m) / (G.degree (X j) : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.Ico a b, (T + M) := Finset.sum_le_sum hterm
    _ = ((b - a : ℕ) : ℝ) * (T + M) := by
        rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]

/-- **The block variable of the recentred field is bounded by the length of the
block times the largest level it visits.** -/
theorem dyadicY_zetaField_le [IsProbabilityMeasure ρ] {M m : ℝ} {t : V → ℝ}
    (ht : ∀ v : V, -M ≤ t v) (hdeg : ∀ v : V, 1 ≤ G.degree v) (ξ : V → ℝ) (d k : ℕ)
    (X : ℕ → V) {T : ℝ} (hTM : 0 ≤ T + M)
    (hT : ∀ j : ℕ, j < 2 ^ (k + 1) → t (X j) ≤ T) :
    RWRS.dyadicY G (zetaField ρ M m t ξ) m d k X ≤ (2 ^ (k + 1) : ℝ) * (T + M) := by
  classical
  set B : ℝ := (2 ^ (k + 1) : ℝ) * (T + M) with hBdef
  have hB0 : 0 ≤ B := by rw [hBdef]; positivity
  have hc : (0:ℝ) ≤ |m| / (d : ℝ) * 2 ^ k := by positivity
  have hblock : ∀ n ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)),
      RWRS.fluctuation G (zetaField ρ M m t ξ) m n X ≤ B := by
    intro n hn
    rw [Finset.mem_Ico] at hn
    have hstep := abs_fluctOn_zetaField_le (ρ := ρ) (m := m) ht hdeg ξ 0 n X hTM
      (fun j _ hjn => hT j (lt_trans hjn hn.2))
    have hle : RWRS.fluctuation G (zetaField ρ M m t ξ) m n X
        ≤ ((n - 0 : ℕ) : ℝ) * (T + M) := by
      rw [fluctuation_eq_fluctOn]
      exact le_trans (le_abs_self _) hstep
    have hn' : ((n - 0 : ℕ) : ℝ) ≤ (2 ^ (k + 1) : ℝ) := by
      have : ((n : ℕ) : ℝ) ≤ ((2 ^ (k + 1) : ℕ) : ℝ) := by exact_mod_cast hn.2.le
      simpa using this
    have hTM' : 0 ≤ T + M := hTM
    calc RWRS.fluctuation G (zetaField ρ M m t ξ) m n X ≤ ((n - 0 : ℕ) : ℝ) * (T + M) := hle
      _ ≤ (2 ^ (k + 1) : ℝ) * (T + M) := mul_le_mul_of_nonneg_right hn' hTM'
  rw [RWRS.dyadicY, iSup_mem_finset_real _ (block_nonempty k) (block_compl k)]
  refine max_le ?_ hB0
  have hsup : (Finset.Ico (2 ^ k) (2 ^ (k + 1))).sup' (block_nonempty k)
      (fun n => RWRS.fluctuation G (zetaField ρ M m t ξ) m n X) ≤ B :=
    Finset.sup'_le _ _ hblock
  have hmax : max ((Finset.Ico (2 ^ k) (2 ^ (k + 1))).sup' (block_nonempty k)
      (fun n => RWRS.fluctuation G (zetaField ρ M m t ξ) m n X)) 0 ≤ B := max_le hsup hB0
  linarith

/-- On the good-walk event the weight of a site inside the block is at most
`N^{α+δ}`. -/
theorem incWeight_le_of_good (hdeg : ∀ v : V, 1 ≤ G.degree v) {α δ : ℝ} {k a b : ℕ}
    (hb : b ≤ 2 ^ (k + 1)) {X : ℕ → V} (hX : X ∈ RWRS.goodWalk (V := V) α δ k) (v : V) :
    incWeight G a b X v ≤ (2 ^ (k + 1) : ℝ) ^ (α + δ) := by
  refine le_trans (incWeight_le_localTimeOn hdeg a b X v) ?_
  refine le_trans ?_ (hX v)
  exact_mod_cast localTimeOn_le_localTime a b (2 ^ (k + 1)) hb v X

/-- **The variance of an increment on the good-walk event**, with the per-site
variances bounded uniformly. -/
theorem sum_incWeight_sq_var_le [IsProbabilityMeasure ρ] (hdeg : ∀ v : V, 1 ≤ G.degree v)
    {M m : ℝ} {t : V → ℝ} {α δ S : ℝ} {k a b : ℕ} (hb : b ≤ 2 ^ (k + 1)) {X : ℕ → V}
    (hX : X ∈ RWRS.goodWalk (V := V) α δ k) (hS : 0 ≤ S)
    (hvar : ∀ v : V, (∫ z, (siteShift ρ M m (t v) z - m) ^ 2 ∂ρ) ≤ S) :
    ∑ v ∈ walkSites a b X, incWeight G a b X v ^ 2
        * ∫ z, (siteShift ρ M m (t v) z - m) ^ 2 ∂ρ
      ≤ S * ((2 ^ (k + 1) : ℝ) ^ (α + δ) * ((b - a : ℕ) : ℝ)) := by
  have hterm : ∀ v ∈ walkSites a b X,
      incWeight G a b X v ^ 2 * ∫ z, (siteShift ρ M m (t v) z - m) ^ 2 ∂ρ
        ≤ S * incWeight G a b X v ^ 2 := by
    intro v _
    have h0 : (0:ℝ) ≤ incWeight G a b X v ^ 2 := by positivity
    have := hvar v
    nlinarith
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (sum_incWeight_sq_le_of_good hdeg hb hX) hS

end RWRS.Support
