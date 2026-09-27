/-
The dichotomy at a vertex, and the first-visit comparison behind the two
no-dominance lemmas of `sec:supercritical` and `sec:critical`.

`escapeProb G o k x` is `P_x(T_o > k)`, defined by its own first-step
recursion.  The defect of the expected local time at `o`,
`E_o[L_n(o)] - E_x[L_n(o)]`, is the convolution of the return kernel with this
survival probability (`meanLocalTime_eq_add_defect`).  Two consequences follow.
The defect is at least `escapeLimit(x)` times `E_o[L_n(o)]`, so if the escape
limit is positive at a neighbour of `o` then `E_o[L_n(o)]` is bounded; hence
when it is unbounded the escape limit vanishes at every vertex, by
connectedness.  And the defect is at most `J + escapeProb J x · E_o[L_n(o)]`,
so a vanishing escape limit makes `E_x[L_n(o)]/E_o[L_n(o)] → 1`.
-/
import RWRS.Support.LibraryBridge

namespace RWRS.Support

open Filter Topology
open scoped ENNReal

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

/-! ### The kernel is a probability -/

/-- The heat kernel `heat G k x y`, the `k`-step transition probability, never
exceeds `1`, by induction on `k`. -/
theorem heat_le_one [Infinite V] (hG : G.Connected) :
    ∀ (k : ℕ) (x y : V), heat G k x y ≤ 1 := by
  classical
  intro k
  induction k with
  | zero => intro x y; rw [show heat G 0 x y = if x = y then 1 else 0 from rfl]; split <;> norm_num
  | succ k ih =>
      intro x y
      rw [heat_succ, walkOp, div_le_one (by exact_mod_cast degree_pos hG x)]
      calc ∑ z ∈ G.neighborFinset x, heat G k z y
          ≤ ∑ _z ∈ G.neighborFinset x, (1 : ℝ) := Finset.sum_le_sum fun z _ => ih z y
        _ = (G.degree x : ℝ) := by
            rw [Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree, nsmul_eq_mul, mul_one]

/-- `walkOp` fixes the constants: the one-step average of a constant function
over the neighbours returns that constant. -/
theorem walkOp_const [Infinite V] (hG : G.Connected) (c : ℝ) (x : V) :
    walkOp G (fun _ => c) x = c := by
  have hd : (0 : ℝ) < (G.degree x : ℝ) := by exact_mod_cast degree_pos hG x
  rw [walkOp, Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree, nsmul_eq_mul]
  field_simp

/-! ### The survival probability -/

open scoped Classical in
/-- `escapeProb G o k x = P_x(T_o > k)`, the probability that the walk from `x`
has not visited `o` by time `k`. -/
noncomputable def escapeProb (G : SimpleGraph V) [G.LocallyFinite] (o : V) : ℕ → V → ℝ
  | 0 => fun x => if x = o then 0 else 1
  | k + 1 => fun x => if x = o then 0 else walkOp G (escapeProb G o k) x

open scoped Classical in
/-- At time `0`, `escapeProb` unfolds to its defining case split: `0` at `o`
and `1` elsewhere. -/
theorem escapeProb_zero (o x : V) : escapeProb G o 0 x = if x = o then 0 else 1 := rfl

open scoped Classical in
/-- At time `k + 1`, `escapeProb` unfolds to its defining recursion: `0` at `o`
and the one-step average `walkOp` elsewhere. -/
theorem escapeProb_succ (o : V) (k : ℕ) (x : V) :
    escapeProb G o (k + 1) x = if x = o then 0 else walkOp G (escapeProb G o k) x := rfl

/-- `escapeProb` vanishes at `o` itself, at every time `k`. -/
theorem escapeProb_self (o : V) : ∀ k : ℕ, escapeProb G o k o = 0
  | 0 => by classical rw [escapeProb_zero, if_pos rfl]
  | _ + 1 => by classical rw [escapeProb_succ, if_pos rfl]

/-- Away from `o`, `escapeProb` at time `k + 1` is the one-step average
`walkOp` of `escapeProb` at time `k`. -/
theorem escapeProb_succ_of_ne {o x : V} (hx : x ≠ o) (k : ℕ) :
    escapeProb G o (k + 1) x = walkOp G (escapeProb G o k) x := by
  classical rw [escapeProb_succ, if_neg hx]

/-- `escapeProb` is nonnegative, by induction on the time using nonnegativity
of `walkOp`'s averaging sum. -/
theorem escapeProb_nonneg (o : V) : ∀ (k : ℕ) (x : V), 0 ≤ escapeProb G o k x := by
  classical
  intro k
  induction k with
  | zero => intro x; rw [escapeProb_zero]; split <;> norm_num
  | succ k ih =>
      intro x
      rw [escapeProb_succ]
      split
      · exact le_rfl
      · exact div_nonneg (Finset.sum_nonneg fun z _ => ih z) (Nat.cast_nonneg _)

/-- `escapeProb` is bounded above by `1`, by induction on the time, averaging
values already at most `1`. -/
theorem escapeProb_le_one [Infinite V] (hG : G.Connected) (o : V) :
    ∀ (k : ℕ) (x : V), escapeProb G o k x ≤ 1 := by
  classical
  intro k
  induction k with
  | zero => intro x; rw [escapeProb_zero]; split <;> norm_num
  | succ k ih =>
      intro x
      rw [escapeProb_succ]
      split
      · norm_num
      · rw [walkOp, div_le_one (by exact_mod_cast degree_pos hG x)]
        calc ∑ z ∈ G.neighborFinset x, escapeProb G o k z
            ≤ ∑ _z ∈ G.neighborFinset x, (1 : ℝ) := Finset.sum_le_sum fun z _ => ih z
          _ = (G.degree x : ℝ) := by
              rw [Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree, nsmul_eq_mul,
                mul_one]

/-- `escapeProb G o k x` is nonincreasing in `k`: surviving longer without
hitting `o` is only harder. -/
theorem escapeProb_antitone [Infinite V] (hG : G.Connected) (o : V) :
    ∀ (k : ℕ) (x : V), escapeProb G o (k + 1) x ≤ escapeProb G o k x := by
  classical
  intro k
  induction k with
  | zero =>
      intro x
      by_cases hx : x = o
      · rw [hx, escapeProb_self, escapeProb_self]
      · rw [escapeProb_zero, if_neg hx]
        exact escapeProb_le_one hG o 1 x
  | succ k ih =>
      intro x
      by_cases hx : x = o
      · rw [hx, escapeProb_self, escapeProb_self]
      · rw [escapeProb_succ_of_ne hx, escapeProb_succ_of_ne hx, walkOp, walkOp]
        exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun z _ => ih z)
          (Nat.cast_nonneg _)

/-- `escapeProb G o · x` is antitone over all pairs of times, obtained from
the one-step antitonicity `escapeProb_antitone` by induction. -/
theorem escapeProb_le_of_le [Infinite V] (hG : G.Connected) (o : V) {j J : ℕ} (hjJ : J ≤ j)
    (x : V) : escapeProb G o j x ≤ escapeProb G o J x := by
  induction j with
  | zero => rw [Nat.le_zero.mp hjJ]
  | succ j ih =>
      rcases Nat.lt_or_ge J (j + 1) with h | h
      · exact le_trans (escapeProb_antitone hG o j x) (ih (Nat.lt_succ_iff.mp h))
      · rw [Nat.le_antisymm hjJ h]

/-! ### The defect of the expected local time -/

/-- `∑_{j<n} P_x(T_o > j) p_{n-1-j}(o,o)`, the defect of the expected local
time at `o` for the walk started at `x`. -/
noncomputable def defect (G : SimpleGraph V) [G.LocallyFinite] (o : V) (n : ℕ) (x : V) : ℝ :=
  ∑ j ∈ Finset.range n, escapeProb G o j x * heat G (n - 1 - j) o o

/-- The defect vanishes at time `0`, its defining sum being empty. -/
theorem defect_zero (o : V) (x : V) : defect G o 0 x = 0 := by simp [defect]

/-- The defect vanishes when evaluated at `o` itself, since `escapeProb`
already vanishes there. -/
theorem defect_self (o : V) (n : ℕ) : defect G o n o = 0 := by
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [escapeProb_self, zero_mul]

/-- The defect is nonnegative, as a sum of products of the nonnegative
`escapeProb` and `heat`. -/
theorem defect_nonneg (o : V) (n : ℕ) (x : V) : 0 ≤ defect G o n x :=
  Finset.sum_nonneg fun j _ =>
    mul_nonneg (escapeProb_nonneg o j x) (heat_nonneg _ o o)

/-- Away from `o`, the defect at time `n + 1` splits off its first term
`heat G n o o` and averages the rest by `walkOp`. -/
theorem defect_succ_of_ne {o x : V} (hx : x ≠ o) (n : ℕ) :
    defect G o (n + 1) x = heat G n o o + walkOp G (fun z => defect G o n z) x := by
  rw [defect, Finset.sum_range_succ' (fun j => escapeProb G o j x * heat G (n + 1 - 1 - j) o o) n]
  have h0 : escapeProb G o 0 x * heat G (n + 1 - 1 - 0) o o = heat G n o o := by
    classical
    rw [escapeProb_zero, if_neg hx, one_mul]
    norm_num
  have hstep : ∀ i ∈ Finset.range n,
      escapeProb G o (i + 1) x * heat G (n + 1 - 1 - (i + 1)) o o
        = (∑ z ∈ G.neighborFinset x, escapeProb G o i z * heat G (n - 1 - i) o o)
            / (G.degree x : ℝ) := by
    intro i _
    have hidx : n + 1 - 1 - (i + 1) = n - 1 - i := by omega
    rw [hidx, escapeProb_succ_of_ne hx, walkOp, div_mul_eq_mul_div, ← Finset.sum_mul]
  rw [Finset.sum_congr rfl hstep, h0, ← Finset.sum_div, Finset.sum_comm, walkOp]
  simp only [defect]
  ring

/-- **The expected local time at `o` from `o` equals the expected local time
from `x` plus the defect.**  Proved by induction on the time using the
first-step recursions for `meanLocalTime` and for `defect`. -/
theorem meanLocalTime_eq_add_defect [Infinite V] (hG : G.Connected) (o : V) :
    ∀ (n : ℕ) (x : V), meanLocalTime G n o o = meanLocalTime G n x o + defect G o n x := by
  intro n
  induction n with
  | zero => intro x; simp [meanLocalTime, defect]
  | succ n ih =>
      intro x
      by_cases hx : x = o
      · rw [hx, defect_self, add_zero]
      · classical
        have hU : meanLocalTime G (n + 1) o o = meanLocalTime G n o o + heat G n o o := by
          rw [meanLocalTime, meanLocalTime, Finset.sum_range_succ]
        have hT : meanLocalTime G (n + 1) x o
            = walkOp G (fun z => meanLocalTime G n z o) x := by
          rw [meanLocalTime_succ, if_neg hx, zero_add]
        have hcomb : walkOp G (fun z => meanLocalTime G n z o) x
            + walkOp G (fun z => defect G o n z) x = meanLocalTime G n o o := by
          rw [walkOp, walkOp, ← add_div, ← Finset.sum_add_distrib,
            Finset.sum_congr rfl (fun z (_ : z ∈ G.neighborFinset x) => (ih z).symm)]
          exact walkOp_const hG _ x
        rw [hU, hT, defect_succ_of_ne hx, ← hcomb]
        ring


/-! ### The escape limit -/

/-- `lim_k P_x(T_o > k)`, the probability that the walk from `x` never visits
`o`. -/
noncomputable def escapeLimit (G : SimpleGraph V) [G.LocallyFinite] (o x : V) : ℝ :=
  ⨅ k : ℕ, escapeProb G o k x

/-- The sequence `k ↦ escapeProb G o k x` is bounded below by `0`. -/
theorem escapeProb_bddBelow (o x : V) : BddBelow (Set.range fun k => escapeProb G o k x) :=
  ⟨0, by rintro _ ⟨k, rfl⟩; exact escapeProb_nonneg o k x⟩

/-- `escapeLimit` is nonnegative, as an infimum of the nonnegative
`escapeProb`. -/
theorem escapeLimit_nonneg (o x : V) : 0 ≤ escapeLimit G o x :=
  le_ciInf fun k => escapeProb_nonneg o k x

/-- `escapeLimit` is bounded by every term `escapeProb G o k x` of the
sequence it is the infimum of. -/
theorem escapeLimit_le (o x : V) (k : ℕ) : escapeLimit G o x ≤ escapeProb G o k x :=
  ciInf_le (escapeProb_bddBelow o x) k

/-- `escapeProb G o k x` converges, as `k → ∞`, to `escapeLimit G o x`, being
a bounded antitone sequence converging to its infimum. -/
theorem tendsto_escapeProb [Infinite V] (hG : G.Connected) (o x : V) :
    Tendsto (fun k => escapeProb G o k x) atTop (𝓝 (escapeLimit G o x)) :=
  tendsto_atTop_ciInf (antitone_nat_of_succ_le fun k => escapeProb_antitone hG o k x)
    (escapeProb_bddBelow o x)

/-- `escapeLimit` vanishes at `o` itself, sandwiched between `0` and the
vanishing `escapeProb G o 0 o`. -/
theorem escapeLimit_self (o : V) : escapeLimit G o o = 0 :=
  le_antisymm (by simpa [escapeProb_self] using escapeLimit_le (G := G) o o 0)
    (escapeLimit_nonneg o o)

/-- Away from `o`, `escapeLimit` is harmonic: it equals the one-step average
`walkOp` of itself, obtained by passing to the limit in the recursion for
`escapeProb`. -/
theorem escapeLimit_harmonic [Infinite V] (hG : G.Connected) {o x : V} (hx : x ≠ o) :
    escapeLimit G o x = walkOp G (escapeLimit G o) x := by
  refine tendsto_nhds_unique ((tendsto_escapeProb hG o x).comp (tendsto_add_atTop_nat 1)) ?_
  have hcong : (fun k => escapeProb G o (k + 1) x)
      = fun k => (∑ z ∈ G.neighborFinset x, escapeProb G o k z) / (G.degree x : ℝ) := by
    funext k; rw [escapeProb_succ_of_ne hx, walkOp]
  simp only [Function.comp_def, hcong]
  rw [walkOp]
  exact ((tendsto_finsetSum _ fun z _ => tendsto_escapeProb hG o z).div_const _)

/-! ### The two bounds on the defect -/

/-- Reflecting the summation index turns the sum of `heat G (n - 1 - j) o o`
over `j < n` into `meanLocalTime G n o o`. -/
theorem sum_heat_reflect (o : V) (n : ℕ) :
    ∑ j ∈ Finset.range n, heat G (n - 1 - j) o o = meanLocalTime G n o o := by
  rw [meanLocalTime]
  exact Finset.sum_range_reflect (fun j => heat G j o o) n

/-- **A lower bound for the defect**: it is at least `escapeLimit G o x` times
`meanLocalTime G n o o`, bounding `escapeProb` below by `escapeLimit` term by
term. -/
theorem defect_ge (o : V) (n : ℕ) (x : V) :
    escapeLimit G o x * meanLocalTime G n o o ≤ defect G o n x := by
  rw [← sum_heat_reflect (G := G) o n, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  exact mul_le_mul_of_nonneg_right (escapeLimit_le o x j) (heat_nonneg _ o o)

/-- **An upper bound for the defect**: it is at most `J` plus
`escapeProb G o J x` times `meanLocalTime G n o o`, splitting the sum at time
`J` and bounding the early terms by `1` and the late ones by `escapeProb G o J x`. -/
theorem defect_le [Infinite V] (hG : G.Connected) (o : V) (J n : ℕ) (x : V) :
    defect G o n x ≤ (J : ℝ) + escapeProb G o J x * meanLocalTime G n o o := by
  classical
  have hsplit : ∀ j ∈ Finset.range n,
      escapeProb G o j x * heat G (n - 1 - j) o o
        ≤ (if j < J then (1 : ℝ) else 0) * heat G (n - 1 - j) o o
          + escapeProb G o J x * heat G (n - 1 - j) o o := by
    intro j _
    rw [← add_mul]
    refine mul_le_mul_of_nonneg_right ?_ (heat_nonneg (G := G) (n - 1 - j) o o)
    by_cases h : j < J
    · rw [if_pos h]
      linarith [escapeProb_le_one hG o j x, escapeProb_nonneg (G := G) o J x]
    · rw [if_neg h, zero_add]
      exact escapeProb_le_of_le hG o (Nat.not_lt.mp h) x
  have hbound : ∑ j ∈ Finset.range n, (if j < J then (1 : ℝ) else 0) * heat G (n - 1 - j) o o
      ≤ (J : ℝ) := by
    have h1 : ∑ j ∈ Finset.range n, (if j < J then (1 : ℝ) else 0) * heat G (n - 1 - j) o o
        ≤ ∑ j ∈ Finset.range n, (if j < J then (1 : ℝ) else 0) := by
      refine Finset.sum_le_sum fun j _ => ?_
      by_cases h : j < J
      · rw [if_pos h, one_mul]; exact heat_le_one (G := G) hG (n - 1 - j) o o
      · rw [if_neg h, zero_mul]
    have h2 : ∑ j ∈ Finset.range n, (if j < J then (1 : ℝ) else 0) ≤ (J : ℝ) := by
      rw [Finset.sum_boole]
      have hsub : (Finset.range n).filter (fun j => j < J) ⊆ Finset.range J := by
        intro j hj
        exact Finset.mem_range.mpr (Finset.mem_filter.mp hj).2
      have hc := Finset.card_le_card hsub
      rw [Finset.card_range] at hc
      exact_mod_cast hc
    linarith
  refine le_trans (Finset.sum_le_sum hsplit) ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_heat_reflect]
  linarith

/-! ### The dichotomy -/

/-- The expected local time from `x` is at most `1 - escapeLimit G o x` times
the expected local time from `o`, combining `meanLocalTime_eq_add_defect` with
the lower bound `defect_ge`. -/
theorem meanLocalTime_le_of_escapeLimit [Infinite V] (hG : G.Connected) (o : V) (n : ℕ) (x : V) :
    meanLocalTime G n x o ≤ (1 - escapeLimit G o x) * meanLocalTime G n o o := by
  have h := meanLocalTime_eq_add_defect hG o n x
  have h2 := defect_ge (G := G) o n x
  nlinarith [h, h2]

/-- **The dichotomy.**  If the expected local time at `o` is unbounded, then the
walk from any vertex reaches `o` almost surely. -/
theorem escapeLimit_eq_zero [Infinite V] (hG : G.Connected) (o : V)
    (hU : ∀ M : ℝ, ∃ n : ℕ, M < meanLocalTime G n o o) (x : V) : escapeLimit G o x = 0 := by
  classical
  -- the escape limit averages to zero over the neighbours of `o`
  have hrho : walkOp G (escapeLimit G o) o = 0 := by
    have hnn : 0 ≤ walkOp G (escapeLimit G o) o :=
      div_nonneg (Finset.sum_nonneg fun z _ => escapeLimit_nonneg o z) (Nat.cast_nonneg _)
    rcases eq_or_lt_of_le hnn with h | h
    · exact h.symm
    · exfalso
      obtain ⟨n, hn⟩ := hU (1 / walkOp G (escapeLimit G o) o)
      have hd : (0 : ℝ) < (G.degree o : ℝ) := by exact_mod_cast degree_pos hG o
      have hcast : ∑ _z ∈ G.neighborFinset o, (1 : ℝ) = (G.degree o : ℝ) := by
        rw [Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree, nsmul_eq_mul, mul_one]
      have hkey : walkOp G (fun z => meanLocalTime G n z o) o
          ≤ meanLocalTime G n o o * (1 - walkOp G (escapeLimit G o) o) := by
        rw [walkOp, div_le_iff₀ hd]
        calc ∑ z ∈ G.neighborFinset o, meanLocalTime G n z o
            ≤ ∑ z ∈ G.neighborFinset o, (1 - escapeLimit G o z) * meanLocalTime G n o o :=
              Finset.sum_le_sum fun z _ => meanLocalTime_le_of_escapeLimit hG o n z
          _ = meanLocalTime G n o o
                * ((G.degree o : ℝ) - ∑ z ∈ G.neighborFinset o, escapeLimit G o z) := by
              rw [← Finset.sum_mul, Finset.sum_sub_distrib, hcast]; ring
          _ = meanLocalTime G n o o * (1 - walkOp G (escapeLimit G o) o)
                * (G.degree o : ℝ) := by
              rw [walkOp]; field_simp
      have hstep : meanLocalTime G (n + 1) o o
          ≤ 1 + meanLocalTime G n o o * (1 - walkOp G (escapeLimit G o) o) := by
        rw [meanLocalTime_succ, if_pos rfl]
        linarith
      have hmono := meanLocalTime_mono (G := G) n o o
      rw [div_lt_iff₀ h] at hn
      nlinarith
  -- so it vanishes at every neighbour of `o`, and then everywhere by connectedness
  have hnbr : ∀ z : V, G.Adj o z → escapeLimit G o z = 0 := by
    intro z hz
    have hsum : ∑ w ∈ G.neighborFinset o, escapeLimit G o w = 0 := by
      have hd : (0 : ℝ) < (G.degree o : ℝ) := by exact_mod_cast degree_pos hG o
      rw [walkOp, div_eq_zero_iff] at hrho
      rcases hrho with h | h
      · exact h
      · exact absurd h hd.ne'
    refine le_antisymm ?_ (escapeLimit_nonneg o z)
    have := (Finset.sum_eq_zero_iff_of_nonneg
      (fun w _ => escapeLimit_nonneg (G := G) o w)).mp hsum z
        ((SimpleGraph.mem_neighborFinset _ _ _).mpr hz)
    exact le_of_eq this
  have hprop : ∀ u z : V, escapeLimit G o u = 0 → G.Adj u z → escapeLimit G o z = 0 := by
    intro u z hu huz
    by_cases hue : u = o
    · exact hnbr z (hue ▸ huz)
    · have hharm := escapeLimit_harmonic hG hue
      rw [hu, walkOp, eq_comm, div_eq_zero_iff] at hharm
      have hd : (0 : ℝ) < (G.degree u : ℝ) := by exact_mod_cast degree_pos hG u
      have hsum : ∑ w ∈ G.neighborFinset u, escapeLimit G o w = 0 := by
        rcases hharm with h | h
        · exact h
        · exact absurd h hd.ne'
      refine le_antisymm ?_ (escapeLimit_nonneg o z)
      exact le_of_eq ((Finset.sum_eq_zero_iff_of_nonneg
        (fun w _ => escapeLimit_nonneg (G := G) o w)).mp hsum z
          ((SimpleGraph.mem_neighborFinset _ _ _).mpr huz))
  have hwalk : ∀ (u : V) (p : G.Walk u x), escapeLimit G o u = 0 → escapeLimit G o x = 0 := by
    intro u p
    induction p with
    | nil => exact fun h => h
    | cons hadj q ih => exact fun h => ih (hprop _ _ h hadj)
  obtain ⟨p⟩ := hG.preconnected o x
  exact hwalk o p (escapeLimit_self o)


/-! ### The transient and the recurrent alternative -/

/-- The expected local time `meanLocalTime G n o o` is monotone in `n`. -/
theorem meanLocalTime_monotone (o : V) : Monotone (fun n => meanLocalTime G n o o) :=
  monotone_nat_of_le_succ fun n => meanLocalTime_mono n o o

/-- The expected local time at time `n` is bounded by the total heat sum
`∑' k, heat G k o o`, coerced into `ℝ≥0∞`. -/
theorem ofReal_meanLocalTime_le_tsum (o : V) (n : ℕ) :
    ENNReal.ofReal (meanLocalTime G n o o) ≤ ∑' k : ℕ, ENNReal.ofReal (heat G k o o) := by
  rw [meanLocalTime, ENNReal.ofReal_sum_of_nonneg fun k _ => heat_nonneg (G := G) k o o]
  exact ENNReal.sum_le_tsum _

/-- **A transient vertex has bounded expected local time.**  If the Green's
function at `o` is finite, `meanLocalTime G n o o` is bounded uniformly in `n`
by the total heat sum. -/
theorem meanLocalTime_bddAbove_of_transient [Infinite V] (hG : G.Connected) (o : V)
    (h : green G o o ≠ ⊤) : ∃ M : ℝ, ∀ n : ℕ, meanLocalTime G n o o ≤ M := by
  have hs := (green_ne_top_iff hG o o).mp h
  refine ⟨(∑' k : ℕ, ENNReal.ofReal (heat G k o o)).toReal, fun n => ?_⟩
  exact (ENNReal.ofReal_le_iff_le_toReal hs).mp (ofReal_meanLocalTime_le_tsum (G := G) o n)

/-- **A recurrent vertex has unbounded expected local time.**  If the Green's
function at `o` is infinite, `meanLocalTime G n o o` exceeds any bound `M` for
some `n`, else the total heat sum would be finite. -/
theorem meanLocalTime_unbounded_of_recurrent [Infinite V] (hG : G.Connected) (o : V)
    (h : green G o o = ⊤) : ∀ M : ℝ, ∃ n : ℕ, M < meanLocalTime G n o o := by
  intro M
  by_contra hcon
  have hcon' : ∀ n : ℕ, meanLocalTime G n o o ≤ M := fun n => not_lt.mp fun hlt => hcon ⟨n, hlt⟩
  have hbd : ∀ n : ℕ, ENNReal.ofReal (meanLocalTime G n o o) ≤ ENNReal.ofReal M := fun n =>
    ENNReal.ofReal_le_ofReal (hcon' n)
  have hsum : (∑' k : ℕ, ENNReal.ofReal (heat G k o o)) ≤ ENNReal.ofReal M := by
    rw [ENNReal.tsum_eq_iSup_nat]
    refine iSup_le fun n => ?_
    rw [← ENNReal.ofReal_sum_of_nonneg fun k _ => heat_nonneg (G := G) k o o]
    exact hbd n
  exact ((green_ne_top_iff hG o o).mpr (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hsum)) h

/-- At a recurrent vertex, `meanLocalTime G n o o` tends to infinity, via the
unbounded monotone sequence of `meanLocalTime_unbounded_of_recurrent`. -/
theorem tendsto_meanLocalTime_of_recurrent [Infinite V] (hG : G.Connected) (o : V)
    (h : green G o o = ⊤) :
    Tendsto (fun n : ℕ => meanLocalTime G n o o) atTop atTop := by
  refine tendsto_atTop.2 fun M => ?_
  obtain ⟨N, hN⟩ := meanLocalTime_unbounded_of_recurrent hG o h M
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  exact le_trans hN.le (meanLocalTime_monotone (G := G) o hn)

/-- **The first-visit comparison.**  When the walk is recurrent at `o`, the
expected local time at `o` for the walk started at any vertex is asymptotically
the one for the walk started at `o`. -/
theorem eventually_meanLocalTime_ge [Infinite V] (hG : G.Connected) (o x : V)
    (hrec : green G o o = ⊤) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, (1 - ε) * meanLocalTime G n o o ≤ meanLocalTime G n x o := by
  have hunb := meanLocalTime_unbounded_of_recurrent hG o hrec
  have hzero := escapeLimit_eq_zero hG o hunb x
  have htend := tendsto_escapeProb hG o x
  rw [hzero] at htend
  obtain ⟨J, hJ⟩ : ∃ J : ℕ, escapeProb G o J x < ε / 2 :=
    (htend.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 2 by linarith))).exists
  have hU := tendsto_meanLocalTime_of_recurrent hG o hrec
  filter_upwards [hU.eventually_ge_atTop (2 * (J : ℝ) / ε)] with n hn
  have hUnn : 0 ≤ meanLocalTime G n o o := meanLocalTime_nonneg n o o
  have hdef := meanLocalTime_eq_add_defect hG o n x
  have hle := defect_le hG o J n x
  have henn : 0 ≤ escapeProb G o J x := escapeProb_nonneg (G := G) o J x
  rw [div_le_iff₀ hε] at hn
  nlinarith [mul_le_mul_of_nonneg_right hJ.le hUnn]

end RWRS.Support
