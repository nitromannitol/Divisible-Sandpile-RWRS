/-
The total inverse-degree time of the spherically symmetric tree with `(n+2)^3`
children at depth `n` is finite: the tail sums of `1/(n+2)^3` form a
superharmonic function whose Laplacian dominates the inverse degree.
-/
import RWRS.Support.Tree
import RWRS.Support.KernelSum
import RWRS.Support.HeatBasic
import Mathlib.Analysis.PSeries

open scoped ENNReal

namespace RWRS.Support

open scoped Classical

/-- The number of children at depth `n`. -/
def bTree (n : ℕ) : ℕ := (n + 2) ^ 3

theorem bTree_pos (n : ℕ) : 0 < bTree n := by
  rw [bTree]; positivity

theorem bTree_ge (n : ℕ) : 8 ≤ bTree n := by
  have : 2 ^ 3 ≤ (n + 2) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  simpa [bTree] using this

theorem summable_invB : Summable fun m : ℕ => (1 : ℝ) / bTree m := by
  have hs : Summable fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 3 :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have h2 := (summable_nat_add_iff 2).mpr hs
  refine h2.congr fun m => ?_
  rw [bTree]
  push_cast
  ring

/-- The tail sum `φ_n = ∑_{m ≥ n} 1/b_m`. -/
noncomputable def phiTail (n : ℕ) : ℝ := ∑' m : ℕ, (1 : ℝ) / bTree (n + m)

theorem summable_shift (n : ℕ) : Summable fun m : ℕ => (1 : ℝ) / bTree (n + m) := by
  have h := (summable_nat_add_iff n).mpr summable_invB
  refine h.congr fun m => ?_
  rw [Nat.add_comm]

theorem phiTail_nonneg (n : ℕ) : 0 ≤ phiTail n :=
  tsum_nonneg fun m => by positivity

theorem phiTail_succ (n : ℕ) : phiTail n = 1 / bTree n + phiTail (n + 1) := by
  rw [phiTail, phiTail, (summable_shift n).tsum_eq_zero_add]
  simp only [Nat.add_zero]
  congr 1
  refine tsum_congr fun m => ?_
  have hm : n + (m + 1) = n + 1 + m := by omega
  rw [hm]

theorem phiTail_sub (n : ℕ) : phiTail n - phiTail (n + 1) = 1 / bTree n := by
  rw [phiTail_succ n]; ring

/-! ### The iterate of the averaging operator is monotone and additive -/

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

theorem walkOp_iterate_mono {f g : V → ℝ} (h : ∀ v, f v ≤ g v) :
    ∀ (k : ℕ) (x : V), (walkOp G)^[k] f x ≤ (walkOp G)^[k] g x := by
  intro k
  induction k with
  | zero => intro x; exact h x
  | succ k ih =>
      intro x
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact walkOp_mono ih x

theorem walkOp_iterate_sub (f g : V → ℝ) :
    ∀ (k : ℕ) (x : V),
      (walkOp G)^[k] (fun v => f v - g v) x = (walkOp G)^[k] f x - (walkOp G)^[k] g x := by
  intro k
  induction k with
  | zero => intro x; rfl
  | succ k ih =>
      intro x
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        Function.iterate_succ_apply']
      rw [show ((walkOp G)^[k] fun v => f v - g v)
          = fun v => (walkOp G)^[k] f v - (walkOp G)^[k] g v from funext ih]
      simp only [walkOp, Finset.sum_sub_distrib, sub_div]

theorem walkOp_iterate_smul (c : ℝ) (f : V → ℝ) :
    ∀ (k : ℕ) (x : V), (walkOp G)^[k] (fun v => c * f v) x = c * (walkOp G)^[k] f x := by
  intro k
  induction k with
  | zero => intro x; rfl
  | succ k ih =>
      intro x
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      rw [show ((walkOp G)^[k] fun v => c * f v)
          = fun v => c * (walkOp G)^[k] f v from funext ih]
      simp only [walkOp, ← Finset.mul_sum, mul_div_assoc]

theorem walkOp_iterate_nonneg {f : V → ℝ} (h : ∀ v, 0 ≤ f v) (k : ℕ) (x : V) :
    0 ≤ (walkOp G)^[k] f x := by
  have hz : ∀ (m : ℕ) (y : V), (walkOp G)^[m] (fun _ => (0 : ℝ)) y = 0 := by
    intro m
    induction m with
    | zero => intro y; rfl
    | succ m ih =>
        intro y
        rw [Function.iterate_succ_apply']
        rw [show ((walkOp G)^[m] fun _ => (0 : ℝ)) = fun _ => (0 : ℝ) from funext ih]
        simp [walkOp]
  have := walkOp_iterate_mono (G := G) (f := fun _ => (0 : ℝ)) (g := f) h k x
  rwa [hz k x] at this

/-! ### The potential dominates the inverse degree -/

noncomputable def phiV (v : TreeV bTree) : ℝ := phiTail v.1.length

theorem superharmonic (v : TreeV bTree) :
    (1 : ℝ) / 2 ≤ ((treeGraph bTree).degree v : ℝ) * phiV v
      - ∑ y ∈ (treeGraph bTree).neighborFinset v, phiV y := by
  have hsum : ∑ y ∈ (treeGraph bTree).neighborFinset v, phiV y
      = bTree v.1.length * phiTail (v.1.length + 1)
        + (if v.1 = [] then 0 else phiTail (v.1.length - 1)) :=
    sum_over_neighbors bTree v phiTail
  rw [hsum, degree_eq, phiV]
  set n := v.1.length with hn
  have h1 : phiTail n - phiTail (n + 1) = 1 / bTree n := phiTail_sub n
  have hbpos : (0 : ℝ) < bTree n := by exact_mod_cast bTree_pos n
  have hmul : (bTree n : ℝ) * (1 / bTree n) = 1 := by field_simp
  by_cases hv : v.1 = []
  · rw [if_pos hv, if_pos hv]
    push_cast
    have hz : (bTree n : ℝ) * phiTail n - bTree n * phiTail (n + 1) = 1 := by
      rw [← mul_sub, h1, hmul]
    linarith
  · rw [if_neg hv, if_neg hv]
    have hn1 : 1 ≤ n := by
      rcases Nat.eq_zero_or_pos n with h | h
      · exact absurd (List.eq_nil_of_length_eq_zero h) hv
      · exact h
    have h2 : phiTail (n - 1) - phiTail n = 1 / bTree (n - 1) := by
      have h := phiTail_sub (n - 1)
      rwa [show n - 1 + 1 = n from by omega] at h
    have hb8 : (8 : ℝ) ≤ (bTree (n - 1) : ℝ) := by exact_mod_cast bTree_ge (n - 1)
    have hinv : 1 / ((bTree (n - 1) : ℝ)) ≤ 1 / 8 := by
      apply one_div_le_one_div_of_le (by norm_num) hb8
    push_cast
    have hexp : ((bTree n : ℝ) + 1) * phiTail n
        - ((bTree n : ℝ) * phiTail (n + 1) + phiTail (n - 1))
        = (bTree n : ℝ) * (phiTail n - phiTail (n + 1)) - (phiTail (n - 1) - phiTail n) := by
      ring
    rw [hexp, h1, h2, hmul]
    linarith

theorem invDeg_le_potential (v : TreeV bTree) :
    invDeg (treeGraph bTree) v ≤ 2 * (phiV v - walkOp (treeGraph bTree) phiV v) := by
  have hd : (0 : ℝ) < ((treeGraph bTree).degree v : ℝ) := by
    rw [degree_eq]
    have := bTree_pos v.1.length
    push_cast
    positivity
  have hs := superharmonic v
  set S := ∑ y ∈ (treeGraph bTree).neighborFinset v, phiV y with hS
  have key : (1 : ℝ) ≤ 2 * (((treeGraph bTree).degree v : ℝ) * phiV v - S) := by linarith
  have hrw : 2 * (phiV v - S / ((treeGraph bTree).degree v : ℝ))
      = (2 * (((treeGraph bTree).degree v : ℝ) * phiV v - S))
        / ((treeGraph bTree).degree v : ℝ) := by
    field_simp
  rw [invDeg, walkOp, ← hS, hrw]
  exact div_le_div_of_nonneg_right key hd.le

theorem clock_le (x : TreeV bTree) (n : ℕ) :
    ∑ k ∈ Finset.range n,
        (walkOp (treeGraph bTree))^[k] (invDeg (treeGraph bTree)) x ≤ 2 * phiV x := by
  have key : ∀ (m : ℕ) (y : TreeV bTree),
      ∑ k ∈ Finset.range m, (walkOp (treeGraph bTree))^[k] (invDeg (treeGraph bTree)) y
        ≤ 2 * (phiV y - (walkOp (treeGraph bTree))^[m] phiV y) := by
    intro m
    induction m with
    | zero => intro y; simp
    | succ m ih =>
        intro y
        rw [Finset.sum_range_succ]
        have h1 := ih y
        have hmono := walkOp_iterate_mono (G := treeGraph bTree)
          (f := invDeg (treeGraph bTree))
          (g := fun v => 2 * (phiV v - walkOp (treeGraph bTree) phiV v))
          invDeg_le_potential m y
        rw [walkOp_iterate_smul, walkOp_iterate_sub,
          show (walkOp (treeGraph bTree))^[m] (walkOp (treeGraph bTree) phiV) y
            = (walkOp (treeGraph bTree))^[m + 1] phiV y from by
            rw [Function.iterate_succ_apply]] at hmono
        linarith
  refine (key n x).trans ?_
  have hnn := walkOp_iterate_nonneg (G := treeGraph bTree) (f := phiV)
    (fun v => phiTail_nonneg _) n x
  linarith

theorem tsum_green_ne_top (x : TreeV bTree) :
    (∑' v : TreeV bTree, green (treeGraph bTree) x v) ≠ ⊤ := by
  classical
  have hdegpos : ∀ v : TreeV bTree, (0 : ℝ) < ((treeGraph bTree).degree v : ℝ) := by
    intro v
    have h : 0 < (treeGraph bTree).degree v := by
      rw [degree_eq]; have := bTree_pos v.1.length; omega
    exact_mod_cast h
  have hinvnn : ∀ v : TreeV bTree, 0 ≤ invDeg (treeGraph bTree) v := fun v => by
    rw [invDeg]; positivity
  have hlayer : ∀ k : ℕ,
      (∑' v : TreeV bTree,
          ENNReal.ofReal (heat (treeGraph bTree) k x v)
            / ((treeGraph bTree).degree v : ℝ≥0∞))
        = ENNReal.ofReal ((walkOp (treeGraph bTree))^[k] (invDeg (treeGraph bTree)) x) := by
    intro k
    have hsupp : ∀ v : TreeV bTree, v ∉ reach (treeGraph bTree) x k →
        ENNReal.ofReal (heat (treeGraph bTree) k x v)
          / ((treeGraph bTree).degree v : ℝ≥0∞) = 0 := by
      intro v hv
      rw [heat_eq_zero_of_notMem_reach k x v hv]
      simp
    rw [tsum_eq_sum hsupp, walkOp_iterate_eq_sum,
      ENNReal.ofReal_sum_of_nonneg (fun v _ =>
        mul_nonneg (heat_nonneg k x v) (hinvnn v))]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [invDeg, ENNReal.ofReal_mul (heat_nonneg k x v), one_div,
      ENNReal.ofReal_inv_of_pos (hdegpos v), ENNReal.ofReal_natCast, div_eq_mul_inv]
  have hswap : (∑' v : TreeV bTree, green (treeGraph bTree) x v)
      = ∑' k : ℕ, ENNReal.ofReal ((walkOp (treeGraph bTree))^[k] (invDeg (treeGraph bTree)) x) := by
    have hgreen : ∀ v : TreeV bTree, green (treeGraph bTree) x v
        = ∑' k : ℕ, ENNReal.ofReal (heat (treeGraph bTree) k x v)
            / ((treeGraph bTree).degree v : ℝ≥0∞) := by
      intro v
      rw [green, div_eq_mul_inv, ← ENNReal.tsum_mul_right]
      exact tsum_congr fun k => (div_eq_mul_inv _ _).symm
    rw [tsum_congr hgreen, ENNReal.tsum_comm]
    exact tsum_congr hlayer
  rw [hswap]
  refine ne_top_of_le_ne_top (b := ENNReal.ofReal (2 * phiV x)) ENNReal.ofReal_ne_top ?_
  rw [ENNReal.tsum_eq_iSup_nat]
  refine iSup_le fun n => ?_
  rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ =>
    walkOp_iterate_nonneg (G := treeGraph bTree) hinvnn k x)]
  exact ENNReal.ofReal_le_ofReal (clock_le x n)

end RWRS.Support
