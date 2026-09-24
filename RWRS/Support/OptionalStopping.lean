/-
Optional stopping for the finite-horizon walk average: for a nonnegative
potential `f`, the payoff of the scenery `-Δf` stopped at a bounded stopping
time is `f(x) - E_x[f(X_τ)]`.  This is what makes the odometer insensitive to a
coboundary, and it is the mechanism behind the transposition bound of the
zero-one law.
-/
import RWRS.Support.Representation

namespace RWRS.Support

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite] [Infinite V]

theorem walkExp_optional (hG : G.Connected) (f : V → ℝ) :
    ∀ (n : ℕ) (x : V) (τ : (ℕ → V) → ℕ), IsStopping τ → (∀ X, τ X ≤ n) →
      walkExp G n x (fun X =>
        payoff G (fun v => -laplacian G f v) (τ X) X + f (X (τ X))) = f x := by
  intro n
  induction n with
  | zero =>
      intro x τ _ hle
      have h0 : τ (fun _ : ℕ => x) = 0 := Nat.le_zero.mp (hle _)
      show payoff G (fun v => -laplacian G f v) (τ (fun _ => x)) (fun _ => x)
          + f ((fun _ : ℕ => x) (τ (fun _ => x))) = f x
      rw [h0]
      simp [payoff]
  | succ n ih =>
      intro x τ hτ hle
      by_cases h0 : τ (fun _ : ℕ => x) = 0
      · have hcong : walkExp G (n + 1) x (fun X =>
              payoff G (fun v => -laplacian G f v) (τ X) X + f (X (τ X)))
            = walkExp G (n + 1) x (fun _ => f x) := by
          refine walkExp_congr fun X hX => ?_
          rw [stopping_of_zero hτ hX h0, hX]
          simp [payoff]
        rw [hcong, walkExp_const hG]
      · have hne : ∀ X : ℕ → V, X 0 = x → τ X ≠ 0 := fun X hX =>
          stopping_ne_zero hτ hX h0
        have hd : (G.degree x : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (degree_pos hG x).ne'
        have hstep : ∀ y ∈ G.neighborFinset x,
            walkExp G n y (fun X' =>
              payoff G (fun v => -laplacian G f v) (τ (cons x X')) (cons x X')
                + f ((cons x X') (τ (cons x X'))))
              = -laplacian G f x / (G.degree x : ℝ) + f y := by
          intro y _
          have hrw : walkExp G n y (fun X' =>
                payoff G (fun v => -laplacian G f v) (τ (cons x X')) (cons x X')
                  + f ((cons x X') (τ (cons x X'))))
              = walkExp G n y (fun X' =>
                -laplacian G f x / (G.degree x : ℝ)
                  + (payoff G (fun v => -laplacian G f v) (τ (cons x X') - 1) X'
                      + f (X' (τ (cons x X') - 1)))) := by
            refine walkExp_congr fun X' _ => ?_
            obtain ⟨m, hm⟩ : ∃ m, τ (cons x X') = m + 1 :=
              ⟨τ (cons x X') - 1, by have := hne (cons x X') rfl; omega⟩
            rw [hm, payoff_cons]
            simp [cons]
            ring
          rw [hrw, walkExp_add, walkExp_const hG]
          congr 1
          exact ih y (fun X' => τ (cons x X') - 1) (isStopping_shift hτ x hne)
            (fun X' => by have := hle (cons x X'); omega)
        rw [walkExp_succ, Finset.sum_congr rfl hstep, Finset.sum_add_distrib,
          Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree, nsmul_eq_mul]
        have hlap : laplacian G f x
            = (∑ y ∈ G.neighborFinset x, f y) - (G.degree x : ℝ) * f x := by
          simp only [laplacian, Finset.sum_sub_distrib, Finset.sum_const,
            SimpleGraph.card_neighborFinset_eq_degree, nsmul_eq_mul]
        field_simp
        linarith [hlap]

end RWRS.Support
