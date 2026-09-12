/-
The Markov property for the finite-horizon walk average, in the form the
local-time moments of `lem:local-time` need.

`walkExp` is a finite average over the trajectories of a given length, so the
Markov property at a fixed time is an induction on that time: conditioning on
the position at time `k` costs the heat kernel and restarts the average at that
position with the remaining horizon.
-/
import RWRS.Support.Walk
import RWRS.Support.Green

namespace RWRS.Support

open scoped Classical

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

/-- The walk average of the zero functional. -/
theorem walkExp_zero_fun : ∀ (n : ℕ) (x : V), walkExp G n x (fun _ => (0 : ℝ)) = 0 := by
  intro n
  induction n with
  | zero => intro x; rfl
  | succ n ih =>
      intro x
      rw [walkExp_succ]
      simp only [ih]
      simp

/-- The walk average of a nonnegative functional is nonnegative. -/
theorem walkExp_nonneg {n : ℕ} {x : V} {F : (ℕ → V) → ℝ} (hF : ∀ X, 0 ≤ F X) :
    0 ≤ walkExp G n x F := by
  have := walkExp_mono (G := G) (n := n) (x := x) (F := fun _ => (0 : ℝ)) (F' := F) hF
  rwa [walkExp_zero_fun] at this

/-- The walk average of a finite sum. -/
theorem walkExp_finsetSum {ι : Type*} (s : Finset ι) (n : ℕ) (x : V)
    (F : ι → (ℕ → V) → ℝ) :
    walkExp G n x (fun X => ∑ i ∈ s, F i X) = ∑ i ∈ s, walkExp G n x (F i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using walkExp_zero_fun (G := G) n x
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, ← ih, ← walkExp_add]
      exact walkExp_congr fun X _ => by rw [Finset.sum_insert ha]

/-- **The Markov property at a fixed time.**  Conditioning the walk average on
being at `v` at time `k` costs the heat kernel and restarts the average at `v`
with the remaining horizon. -/
theorem walkExp_markov (v : V) (F : (ℕ → V) → ℝ) :
    ∀ (k n : ℕ) (x : V), k ≤ n →
      walkExp G n x (fun X => (if X k = v then (1 : ℝ) else 0) * F (fun j => X (k + j)))
        = heat G k x v * walkExp G (n - k) v F := by
  intro k
  induction k with
  | zero =>
      intro n x _
      have hshift : ∀ X : ℕ → V, (fun j => X (0 + j)) = X := by
        intro X; funext j; rw [Nat.zero_add]
      by_cases hxv : x = v
      · subst hxv
        have h1 : walkExp G n x (fun X => (if X 0 = x then (1 : ℝ) else 0)
            * F (fun j => X (0 + j))) = walkExp G n x F := by
          refine walkExp_congr fun X hX => ?_
          rw [hX, if_pos rfl, one_mul, hshift]
        rw [h1]
        simp [heat]
      · have h1 : walkExp G n x (fun X => (if X 0 = v then (1 : ℝ) else 0)
            * F (fun j => X (0 + j))) = 0 := by
          rw [show walkExp G n x (fun X => (if X 0 = v then (1 : ℝ) else 0)
              * F (fun j => X (0 + j))) = walkExp G n x (fun _ => (0 : ℝ)) from
            walkExp_congr fun X hX => by rw [hX, if_neg hxv, zero_mul]]
          exact walkExp_zero_fun n x
        rw [h1]
        simp [heat, hxv]
  | succ k ih =>
      intro n x hk
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      have hk' : k ≤ n' := by omega
      rw [walkExp_succ]
      have hterm : ∀ y ∈ G.neighborFinset x,
          walkExp G n' y (fun X => (if (cons x X) (k + 1) = v then (1 : ℝ) else 0)
              * F (fun j => (cons x X) (k + 1 + j)))
            = heat G k y v * walkExp G (n' - k) v F := by
        intro y _
        rw [← ih n' y hk']
        refine walkExp_congr fun X _ => ?_
        simp only [cons_succ]
        congr 2
        funext j
        rw [show k + 1 + j = (k + j) + 1 by omega]
        rfl
      rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul]
      rw [show n' + 1 - (k + 1) = n' - k by omega]
      rw [show heat G (k + 1) x v = (∑ y ∈ G.neighborFinset x, heat G k y v) / G.degree x
        from rfl]
      ring

/-- The heat kernel is a sub-probability on every finite set of targets. -/
theorem sum_heat_le_one (hdeg : ∀ v : V, 0 < G.degree v) :
    ∀ (k : ℕ) (x : V) (S : Finset V), ∑ v ∈ S, heat G k x v ≤ 1 := by
  classical
  intro k
  induction k with
  | zero =>
      intro x S
      simp only [heat]
      by_cases hx : x ∈ S
      · rw [Finset.sum_eq_single x (fun b _ hb => if_neg (Ne.symm hb)) (fun h => absurd hx h),
          if_pos rfl]
      · refine le_trans (le_of_eq (Finset.sum_eq_zero fun b hb => ?_)) zero_le_one
        refine if_neg fun hc => hx ?_
        rw [hc]; exact hb
  | succ k ih =>
      intro x S
      have h1 : ∀ w : V, heat G (k + 1) x w
          = (∑ y ∈ G.neighborFinset x, heat G k y w) / G.degree x := fun _ => rfl
      have hrw : ∑ v ∈ S, heat G (k + 1) x v
          = (∑ y ∈ G.neighborFinset x, ∑ v ∈ S, heat G k y v) / G.degree x := by
        rw [Finset.sum_congr rfl (fun v _ => h1 v), ← Finset.sum_div, Finset.sum_comm]
      rw [hrw]
      have hle : ∑ y ∈ G.neighborFinset x, ∑ v ∈ S, heat G k y v
          ≤ (G.degree x : ℝ) := by
        refine le_trans (Finset.sum_le_sum fun y _ => ih y S) ?_
        rw [Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree, nsmul_eq_mul,
          mul_one]
      have hdx : (0 : ℝ) < G.degree x := Nat.cast_pos.2 (hdeg x)
      rw [div_le_one hdx]
      exact hle

end RWRS.Support
