/-
The variance of an increment on the good-walk event, for `prop:subcritical`.

`rwrs.tex:1183`: "On `A_k`, since `L_I(v) ≤ L_N(v) ≤ N^{α+δ}` and `∑_v L_I(v) = m`,
the variance bound `∑_v L_I(v)^2 ≤ N^{α+δ} m` holds."  That is the pathwise
input to part (b) of `lem:fuk-nagaev`.
-/
import RWRS.Support.SubIncrement

namespace RWRS.Support

open scoped ENNReal Classical

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

/-- The local time over a sub-interval of `[0,n)` is at most the local time over
`[0,n)`. -/
theorem localTimeOn_le_localTime (a b n : ℕ) (hb : b ≤ n) (v : V) (X : ℕ → V) :
    localTimeOn a b v X ≤ RWRS.localTime n v X := by
  unfold localTimeOn RWRS.localTime
  refine Finset.card_le_card ?_
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_range] at hj ⊢
  exact ⟨by omega, hj.2⟩

/-- **The variance bound on the good-walk event.**  The squared weights of an
increment inside `[0,N)` sum to at most `N^{α+δ}` times the length of the
interval. -/
theorem sum_incWeight_sq_le_of_good (hdeg : ∀ v : V, 1 ≤ G.degree v) {α δ : ℝ} {k : ℕ}
    {a b : ℕ} (hb : b ≤ 2 ^ (k + 1)) {X : ℕ → V}
    (hX : X ∈ RWRS.goodWalk (V := V) α δ k) :
    ∑ v ∈ walkSites a b X, incWeight G a b X v ^ 2
      ≤ (2 ^ (k + 1) : ℝ) ^ (α + δ) * ((b - a : ℕ) : ℝ) := by
  have hB0 : (0:ℝ) ≤ (2 ^ (k + 1) : ℝ) ^ (α + δ) := Real.rpow_nonneg (by positivity) _
  have key : ∀ v ∈ walkSites a b X, incWeight G a b X v ^ 2
      ≤ (2 ^ (k + 1) : ℝ) ^ (α + δ) * ((localTimeOn a b v X : ℕ) : ℝ) := by
    intro v _
    have h0 : 0 ≤ incWeight G a b X v := incWeight_nonneg a b X v
    have h1 : incWeight G a b X v ≤ ((localTimeOn a b v X : ℕ) : ℝ) :=
      incWeight_le_localTimeOn hdeg a b X v
    have h2 : ((localTimeOn a b v X : ℕ) : ℝ) ≤ (2 ^ (k + 1) : ℝ) ^ (α + δ) := by
      refine le_trans ?_ (hX v)
      exact_mod_cast localTimeOn_le_localTime a b (2 ^ (k + 1)) hb v X
    calc incWeight G a b X v ^ 2 = incWeight G a b X v * incWeight G a b X v := sq _
      _ ≤ (2 ^ (k + 1) : ℝ) ^ (α + δ) * ((localTimeOn a b v X : ℕ) : ℝ) :=
          mul_le_mul (le_trans h1 h2) h1 h0 hB0
  refine le_trans (Finset.sum_le_sum key) ?_
  rw [← Finset.mul_sum]
  have hreal : ∑ v ∈ walkSites a b X, ((localTimeOn a b v X : ℕ) : ℝ) = ((b - a : ℕ) : ℝ) := by
    rw [← Nat.cast_sum]
    exact_mod_cast congrArg (fun j : ℕ => (j : ℝ)) (sum_localTimeOn_eq a b X)
  rw [hreal]

end RWRS.Support
