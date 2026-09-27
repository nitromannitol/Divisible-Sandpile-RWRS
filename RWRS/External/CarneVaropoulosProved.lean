import RWRS.External.CarneVaropoulos
import RWRS.Support.SubPolyWalk
import RWRS.Support.Transience
import LatticeProb.Graph.ExitTime
import LatticeProb.Graph.Nash
import LatticeProb.Graph.Reach
import LatticeProb.Walk.SRWTail

set_option linter.unusedSimpArgs false

/-!
This file records the parts of the Carne--Varopoulos argument which are
available from the current graph-walk API.  The first lemma is the bridge from
the path-space law used by RWRS to the heat kernel used by the shared library.
The second is the finite-propagation fact for the heat kernel itself.

The remaining operator-theoretic step requires a spectral-calculus theorem for
the self-adjoint transition operator on the weighted `ell^2` space of an
arbitrary locally finite graph; no such theorem is currently exposed by the
library.  A sufficient missing library statement, in mathematical form, is:

  If `H` is a real or complex Hilbert space, `A : H → H` is bounded and
  self-adjoint, and `‖A‖ ≤ 1`, then for every real polynomial `p`,

    `‖p(A)‖ ≤ sup {‖p(t)‖ | t ∈ Set.Icc (-1 : ℝ) 1}`.

Here `p(A)` must be the continuous-operator polynomial evaluation.  The
library also needs the standard coefficient bridge for the graph operator:
the weighted `ell^2` transition operator `P f(v) = deg(v)⁻¹ ∑ w∼v f(w)`
must be available as a bounded self-adjoint operator, and its matrix
coefficient between weighted point masses must be identified with
`heat G n x y / deg(y)`.  With those declarations, the Chebyshev recurrence
and finite propagation complete the missing off-diagonal argument.
-/

open MeasureTheory
open scoped Classical

namespace RWRS.External

/-- **Bridge from the path-space law to the shared library's heat kernel.**
The probability, under `RWRS.walkLaw`, that the walk from `x` is at `y` at
time `n` equals `heat G n x y`, by relating the trajectory to the library's
killed walk law on the closed ball of radius `n` around `x`. -/
theorem carne_walkLaw_eq_heat {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]
    [MeasurableSpace V] [MeasurableSingletonClass V] [Nontrivial V]
    (hG : G.Connected) (x y : V) (n : ℕ) :
    RWRS.walkLaw G x {X : ℕ → V | X n = y} =
      ENNReal.ofReal (RWRS.heat G n x y) := by
  classical
  letI : Countable V := RWRS.Support.countable_of_connected hG
  have hdeg : ∀ v : V, 0 < G.degree v := by
    intro v
    rw [SimpleGraph.degree_pos_iff_exists_adj]
    obtain ⟨u, hu⟩ := exists_ne v
    obtain ⟨p⟩ := hG.preconnected v u
    rcases p with _ | ⟨hadj, q⟩
    · exact absurd rfl hu
    · exact ⟨_, hadj⟩
  let C : Set V := RWRS.closedBall G x n
  have hC : RWRS.closedBall G x n ⊆ C := by
    intro z hz
    exact hz
  have hae : ∀ᵐ X ∂ RWRS.walkLaw G x,
      X ∈ LatticeProb.Graph.stayIn C n := by
    have hpath := RWRS.Support.ae_edist_le hdeg x
    filter_upwards [hpath] with X hX
    change ∀ k ≤ n, G.edist (X k) x ≤ (n : ℕ∞)
    intro k hk
    exact (hX k).trans (by exact_mod_cast hk)
  have hmeasure : RWRS.walkLaw G x {X : ℕ → V | X n = y} =
      RWRS.walkLaw G x ({X : ℕ → V | X n = y} ∩ LatticeProb.Graph.stayIn C n) := by
    apply MeasureTheory.measure_congr
    filter_upwards [hae] with X hX
    apply propext
    constructor
    · intro h
      exact ⟨h, hX⟩
    · intro h
      exact h.1
  calc
    RWRS.walkLaw G x {X : ℕ → V | X n = y} =
        RWRS.walkLaw G x ({X : ℕ → V | X n = y} ∩ LatticeProb.Graph.stayIn C n) :=
      hmeasure
    _ = LatticeProb.Graph.walkLaw G x
          ({X : ℕ → V | X n = y} ∩ LatticeProb.Graph.stayIn C n) := by
      rw [RWRS.Support.walkLaw_eq_lib x]
    _ = ENNReal.ofReal (LatticeProb.Graph.killedHeat G C n x y) :=
      LatticeProb.Graph.walkLaw_stayIn_eq hdeg C n x y
    _ = ENNReal.ofReal (RWRS.heat G n x y) := by
      rw [← RWRS.Support.killedHeat_eq_lib C n x y,
        RWRS.Support.killedHeat_eq_heat_of_ball C n x hC y]

/-- The heat kernel vanishes below the graph distance: `heat G n x y = 0`
whenever `n < dist x y`, no walk of `n` steps can bridge a farther gap. -/
theorem carne_heat_zero_of_dist_lt {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]
    {x y : V} {n : ℕ} (h : n < G.dist x y) : RWRS.heat G n x y = 0 := by
  rw [RWRS.Support.heat_eq_lib]
  exact LatticeProb.Graph.heat_eq_zero_of_lt_dist h

/-- A Cauchy–Schwarz bound on the walk average: `(walkOp G f v) ^ 2` is at
most the mean square of `f` over `v`'s neighbours. -/
theorem carne_walkOp_sq_le {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]
    (hdeg : ∀ v : V, 0 < G.degree v) (f : V → ℝ) (v : V) :
    (RWRS.walkOp G f v) ^ 2 ≤
      (∑ z ∈ G.neighborFinset v, f z ^ 2) / (G.degree v : ℝ) := by
  have hcard := sq_sum_le_card_mul_sum_sq (s := G.neighborFinset v) (f := f)
  rw [SimpleGraph.card_neighborFinset_eq_degree] at hcard
  have hd : (0 : ℝ) < G.degree v := by exact_mod_cast hdeg v
  rw [RWRS.walkOp]
  rw [div_pow]
  calc
    (∑ x ∈ G.neighborFinset v, f x) ^ 2 / (G.degree v : ℝ) ^ 2
        ≤ ((G.degree v : ℝ) * ∑ x ∈ G.neighborFinset v, f x ^ 2) /
            (G.degree v : ℝ) ^ 2 := by
          exact div_le_div_of_nonneg_right hcard (sq_nonneg _)
    _ = (∑ x ∈ G.neighborFinset v, f x ^ 2) / (G.degree v : ℝ) := by
          field_simp

/-- **`walkOp` is a contraction for the degree-weighted `ℓ²` norm.** Over any
finite set `T` containing the support of `f` and its neighbours, the
degree-weighted sum of `(walkOp G f) ^ 2` is at most that of `f ^ 2`, via
`carne_walkOp_sq_le` and the edge-counting identity `sum_neighbor_sum`. -/
theorem carne_walkOp_weighted_sq_sum_le {V : Type*} {G : SimpleGraph V}
    [G.LocallyFinite] (hdeg : ∀ v : V, 0 < G.degree v) (f : V → ℝ) (T : Finset V)
    (hT : ∀ y, f y ≠ 0 → y ∈ T)
    (hTN : ∀ y z, f y ≠ 0 → G.Adj y z → z ∈ T) :
    ∑ y ∈ T, (G.degree y : ℝ) * (RWRS.walkOp G f y) ^ 2 ≤
      ∑ y ∈ T, (G.degree y : ℝ) * f y ^ 2 := by
  calc
    ∑ y ∈ T, (G.degree y : ℝ) * (RWRS.walkOp G f y) ^ 2
        ≤ ∑ y ∈ T, (G.degree y : ℝ) *
            ((∑ z ∈ G.neighborFinset y, f z ^ 2) / (G.degree y : ℝ)) := by
      gcongr with y hy
      exact carne_walkOp_sq_le hdeg f y
    _ = ∑ y ∈ T, ∑ z ∈ G.neighborFinset y, f z ^ 2 := by
      apply Finset.sum_congr rfl
      intro y hy
      have hdy : (G.degree y : ℝ) ≠ 0 := by
        exact_mod_cast (hdeg y).ne'
      field_simp
    _ = ∑ y ∈ T, (G.degree y : ℝ) * f y ^ 2 := by
      exact LatticeProb.Graph.sum_neighbor_sum (fun z => f z ^ 2) T
        (fun y hy => hT y (by
          intro hzero
          exact hy (by rw [hzero]; norm_num)))
        (fun y z hy hadj => hTN y z (by
          intro hzero
          exact hy (by rw [hzero]; norm_num)) hadj)

/-- The Chebyshev polynomial of the first kind `T_n` applied to `walkOp G`,
computed on `f` directly by the recursion `T_{n+2} = 2 P T_{n+1} - T_n`
rather than through the operator itself. -/
noncomputable def carne_chebApply {V : Type*} (G : SimpleGraph V)
    [G.LocallyFinite] (f : V → ℝ) : ℕ → V → ℝ
  | 0 => f
  | 1 => RWRS.walkOp G f
  | n + 2 => fun v =>
      2 * RWRS.walkOp G (carne_chebApply G f (n + 1)) v
        - carne_chebApply G f n v

/-- The Chebyshev polynomial of the second kind `U_n` applied to `walkOp G`,
computed on `f` directly by the recursion `U_{n+2} = 2 P U_{n+1} - U_n` with
initial value `U_1 = 2P`. -/
noncomputable def carne_chebSecondApply {V : Type*} (G : SimpleGraph V)
    [G.LocallyFinite] (f : V → ℝ) : ℕ → V → ℝ
  | 0 => f
  | 1 => fun v => 2 * RWRS.walkOp G f v
  | n + 2 => fun v =>
      2 * RWRS.walkOp G (carne_chebSecondApply G f (n + 1)) v
        - carne_chebSecondApply G f n v

/-- `walkOp G` packaged as an `ℝ`-linear endomorphism of `V → ℝ`, so that a
Chebyshev polynomial can be applied to it via `Polynomial.smeval`. -/
noncomputable def carne_walkOpLinear {V : Type*} (G : SimpleGraph V)
    [G.LocallyFinite] : Module.End ℝ (V → ℝ) :=
  { toFun := RWRS.walkOp G
    map_add' := by
      intro f g
      funext v
      change (∑ y ∈ G.neighborFinset v, (f y + g y)) / (G.degree v : ℝ) =
        ((∑ y ∈ G.neighborFinset v, f y) / G.degree v) +
          ((∑ y ∈ G.neighborFinset v, g y) / G.degree v)
      rw [Finset.sum_add_distrib, add_div]
    map_smul' := by
      intro c f
      funext v
      change (∑ y ∈ G.neighborFinset v, c * f y) / (G.degree v : ℝ) =
        c * ((∑ y ∈ G.neighborFinset v, f y) / G.degree v)
      rw [← Finset.mul_sum, mul_div_assoc] }

/-- The Chebyshev polynomials of the first kind, `T_n`, by the standard
three-term recursion `T_{n+2} = 2X T_{n+1} - T_n`. -/
noncomputable def carne_chebPoly : ℕ → Polynomial ℝ
  | 0 => 1
  | 1 => Polynomial.X
  | n + 2 => 2 * Polynomial.X * carne_chebPoly (n + 1)
      - carne_chebPoly n

/-- The Chebyshev polynomials of the second kind, `U_n`, by the standard
three-term recursion `U_{n+2} = 2X U_{n+1} - U_n` with `U_1 = 2X`. -/
noncomputable def carne_chebSecondPoly : ℕ → Polynomial ℝ
  | 0 => 1
  | 1 => 2 * Polynomial.X
  | n + 2 => 2 * Polynomial.X * carne_chebSecondPoly (n + 1)
      - carne_chebSecondPoly n

/-- The constant polynomial `2` evaluated at `carne_walkOpLinear G` via
`smeval` is the scalar endomorphism `2 • 1`. -/
theorem carne_smeval_two {V : Type*} (G : SimpleGraph V)
    [G.LocallyFinite] :
    (2 : Polynomial ℝ).smeval (carne_walkOpLinear G) =
      (2 : ℝ) • (1 : Module.End ℝ (V → ℝ)) := by
  rw [← Polynomial.C_ofNat 2, Polynomial.smeval_C]
  simp [Module.End.one_apply]

/-- **`carne_chebApply` is the Chebyshev polynomial `T_k` of `walkOp G`
applied to `f`.** Proved by two-step induction, matching the recursion on
`carne_chebApply` against the polynomial recursion on `carne_chebPoly` via
`smeval`. -/
theorem carne_chebApply_eq_poly {V : Type*} (G : SimpleGraph V)
    [G.LocallyFinite] (f : V → ℝ) (k : ℕ) :
    carne_chebApply G f k =
      (carne_chebPoly k).smeval (carne_walkOpLinear G) f := by
  induction k using Nat.twoStepInduction with
  | zero =>
      funext v
      simp [carne_chebApply, carne_chebPoly, carne_walkOpLinear]
  | one =>
      funext v
      simp [carne_chebApply, carne_chebPoly, carne_walkOpLinear]
  | more k ihk ihsk =>
      funext v
      simp only [carne_chebApply, carne_chebPoly, Polynomial.smeval_sub,
        Polynomial.smeval_add, Polynomial.smeval_mul, Polynomial.smeval_smul,
        Polynomial.smeval_X, Polynomial.smeval_natCast, Module.End.mul_apply,
        map_sub, map_add, map_mul,
        smul_eq_mul, one_mul, pow_one]
      rw [ihsk, ihk]
      rw [carne_smeval_two]
      simp [carne_walkOpLinear]

/-- **`carne_chebSecondApply` is the Chebyshev polynomial `U_k` of `walkOp G`
applied to `f`.** Proved as `carne_chebApply_eq_poly`, by two-step induction
matching the two recursions. -/
theorem carne_chebSecondApply_eq_poly {V : Type*} (G : SimpleGraph V)
    [G.LocallyFinite] (f : V → ℝ) (k : ℕ) :
    carne_chebSecondApply G f k =
      (carne_chebSecondPoly k).smeval (carne_walkOpLinear G) f := by
  induction k using Nat.twoStepInduction with
  | zero =>
      funext v
      simp [carne_chebSecondApply, carne_chebSecondPoly,
        carne_walkOpLinear]
  | one =>
      funext v
      rw [carne_chebSecondApply, carne_chebSecondPoly,
        Polynomial.smeval_mul, carne_smeval_two,
        Polynomial.smeval_X]
      simp [carne_walkOpLinear]
  | more k ihk ihsk =>
      funext v
      simp only [carne_chebSecondApply, carne_chebSecondPoly,
        Polynomial.smeval_sub, Polynomial.smeval_add, Polynomial.smeval_mul,
        Polynomial.smeval_smul, Polynomial.smeval_X, Polynomial.smeval_natCast,
        Module.End.mul_apply,
        map_sub, map_add, map_mul, smul_eq_mul, one_mul, pow_one]
      rw [ihsk, ihk]
      rw [carne_smeval_two]
      simp [carne_walkOpLinear]

/-- **The classical identity `T_{k+1} = U_{k+1} - X U_k`** between Chebyshev
polynomials of the first and second kind, by induction on `k` using the
shared recursion. -/
theorem carne_chebPoly_eq_second_sub (k : ℕ) :
    carne_chebPoly (k + 1) =
      carne_chebSecondPoly (k + 1) - Polynomial.X * carne_chebSecondPoly k := by
  induction k using Nat.twoStepInduction with
  | zero =>
      simp [carne_chebPoly, carne_chebSecondPoly]
      ring
  | one =>
      simp [carne_chebPoly, carne_chebSecondPoly]
      ring
  | more k ihk ihsk =>
      have hT : carne_chebPoly (k + 2 + 1) =
          2 * Polynomial.X * carne_chebPoly (k + 2) -
            carne_chebPoly (k + 1) := by
        rw [show k + 2 + 1 = (k + 1) + 2 by omega]
        rfl
      have hU : carne_chebSecondPoly (k + 2 + 1) =
          2 * Polynomial.X * carne_chebSecondPoly (k + 2) -
            carne_chebSecondPoly (k + 1) := by
        rw [show k + 2 + 1 = (k + 1) + 2 by omega]
        rfl
      rw [hT, hU, ihsk, ihk]
      rw [show k + 1 + 1 = k + 2 by omega]
      have hU2 : carne_chebSecondPoly (k + 2) =
          2 * Polynomial.X * carne_chebSecondPoly (k + 1) -
            carne_chebSecondPoly k := by rfl
      rw [hU2]
      ring

/-- **The Pell-type identity `T_{k+1}^2 - (X^2-1) U_k^2 = 1`** for Chebyshev
polynomials, the polynomial analogue of `cos^2 + sin^2 = 1`, proved by
induction on `k` via `carne_chebPoly_eq_second_sub`. -/
theorem carne_chebPellPoly (k : ℕ) :
    carne_chebPoly (k + 1) ^ 2 -
        (Polynomial.X ^ 2 - 1) * carne_chebSecondPoly k ^ 2 = 1 := by
  rw [carne_chebPoly_eq_second_sub]
  induction k with
  | zero =>
      simp [carne_chebSecondPoly]
      ring
  | succ k ih =>
      simp only [carne_chebSecondPoly]
      calc
        (2 * Polynomial.X * carne_chebSecondPoly (k + 1) -
            carne_chebSecondPoly k - Polynomial.X *
              carne_chebSecondPoly (k + 1)) ^ 2 -
            (Polynomial.X ^ 2 - 1) *
              (carne_chebSecondPoly (k + 1)) ^ 2 =
            (carne_chebSecondPoly (k + 1) - Polynomial.X *
              carne_chebSecondPoly k) ^ 2 -
            (Polynomial.X ^ 2 - 1) *
              (carne_chebSecondPoly k) ^ 2 := by ring
        _ = 1 := ih

/-- The operator-level instance of `carne_chebPellPoly` applied to `f`: the
Chebyshev Pell identity evaluated at `carne_walkOpLinear G` recovers `f`. -/
theorem carne_chebPellApply {V : Type*} (G : SimpleGraph V)
    [G.LocallyFinite] (f : V → ℝ) (k : ℕ) :
    carne_chebApply G (carne_chebApply G f (k + 1)) (k + 1) -
        (RWRS.walkOp G (RWRS.walkOp G
          (carne_chebSecondApply G
            (carne_chebSecondApply G f k) k))) +
        carne_chebSecondApply G
          (carne_chebSecondApply G f k) k = f := by
  have hp := congrArg (fun p : Polynomial ℝ =>
    p.smeval (carne_walkOpLinear G)) (carne_chebPellPoly k)
  funext v
  have hp' := congrArg (fun q => q f) hp
  have h := congrFun hp' v
  simp [Polynomial.smeval_sub, Polynomial.smeval_add,
    Polynomial.smeval_mul, Polynomial.smeval_pow, Polynomial.smeval_smul,
    Polynomial.smeval_X, Polynomial.smeval_one, Module.End.mul_apply,
    LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply, smul_eq_mul, one_mul, pow_one, pow_two,
    sub_sub_eq_add_sub, carne_walkOpLinear,
    carne_chebApply_eq_poly, carne_chebSecondApply_eq_poly] at h ⊢
  linarith

/-- **Discrete integration by parts across an edge sum.** For `f` and `g`
supported on a common finite set `T`, summing `f`'s neighbour-total against
`g` equals summing `f` against `g`'s neighbour-total, by re-indexing the
double sum over edges of `T`. -/
theorem carne_edge_inner_swap {V : Type*} {G : SimpleGraph V}
    [G.LocallyFinite] (T : Finset V) (f g : V → ℝ)
    (hf : ∀ z, f z ≠ 0 → z ∈ T) (hg : ∀ z, g z ≠ 0 → z ∈ T) :
    (∑ y ∈ T, (∑ z ∈ G.neighborFinset y, f z) * g y) =
      ∑ y ∈ T, f y * (∑ z ∈ G.neighborFinset y, g z) := by
  classical
  have hleft :
      (∑ y ∈ T, (∑ z ∈ G.neighborFinset y, f z) * g y) =
        ∑ y ∈ T, ∑ z ∈ G.neighborFinset y ∩ T, f z * g y := by
    apply Finset.sum_congr rfl
    intro y hy
    calc
      (∑ z ∈ G.neighborFinset y, f z) * g y =
          ∑ z ∈ G.neighborFinset y, f z * g y := by rw [Finset.sum_mul]
      _ = ∑ z ∈ G.neighborFinset y ∩ T, f z * g y := by
        refine (Finset.sum_subset (s₁ := G.neighborFinset y ∩ T)
          (s₂ := G.neighborFinset y) (f := fun z => f z * g y)
          Finset.inter_subset_left ?_).symm
        intro z hz hzt
        have hfz : f z = 0 := by
          by_contra hfz
          exact hzt (Finset.mem_inter.mpr ⟨hz, hf z hfz⟩)
        simp [hfz]
  have hswap :
      (∑ y ∈ T, ∑ z ∈ G.neighborFinset y ∩ T, f z * g y) =
        ∑ z ∈ T, ∑ y ∈ G.neighborFinset z ∩ T, f z * g y := by
    refine Finset.sum_comm' ?_
    intro y z
    constructor
    · rintro ⟨hy, hz⟩
      rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at hz
      exact ⟨Finset.mem_inter.mpr ⟨
        (SimpleGraph.mem_neighborFinset _ _ _).2 hz.1.symm, hy⟩, hz.2⟩
    · rintro ⟨hy, hz⟩
      rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at hy
      exact ⟨hy.2, Finset.mem_inter.mpr ⟨
        (SimpleGraph.mem_neighborFinset _ _ _).2 hy.1.symm, hz⟩⟩
  have hright :
      (∑ z ∈ T, f z * (∑ y ∈ G.neighborFinset z, g y)) =
        ∑ z ∈ T, ∑ y ∈ G.neighborFinset z ∩ T, f z * g y := by
    apply Finset.sum_congr rfl
    intro z hz
    rw [Finset.mul_sum]
    refine (Finset.sum_subset (s₁ := G.neighborFinset z ∩ T)
      (s₂ := G.neighborFinset z) (f := fun y => f z * g y)
      Finset.inter_subset_left ?_).symm
    intro y hy hyt
    have hgy : g y = 0 := by
      by_contra hgy
      exact hyt (Finset.mem_inter.mpr ⟨hy, hg y hgy⟩)
    simp [hgy]
  exact hleft.trans (hswap.trans hright.symm)

/-- **`walkOp` is self-adjoint for the degree-weighted inner product**, on
functions `f, g` supported in a common finite set `T`: rewriting each side of
`carne_edge_inner_swap` via `walkOp`'s definition. This is the combinatorial
substitute for the missing Hilbert-space self-adjointness statement. -/
theorem carne_weighted_walkOp_inner_comm {V : Type*} {G : SimpleGraph V}
    [G.LocallyFinite] (hdeg : ∀ v : V, 0 < G.degree v) (T : Finset V)
    (f g : V → ℝ) (hf : ∀ z, f z ≠ 0 → z ∈ T)
    (hg : ∀ z, g z ≠ 0 → z ∈ T) :
    (∑ y ∈ T, (G.degree y : ℝ) * (RWRS.walkOp G f y) * g y) =
      ∑ y ∈ T, (G.degree y : ℝ) * f y * (RWRS.walkOp G g y) := by
  have hdeg' : ∀ y ∈ T, (G.degree y : ℝ) ≠ 0 := by
    intro y hy
    exact_mod_cast (hdeg y).ne'
  have hstep : ∀ y ∈ T,
      (G.degree y : ℝ) * (RWRS.walkOp G f y) * g y =
        (∑ z ∈ G.neighborFinset y, f z) * g y := by
    intro y hy
    rw [RWRS.walkOp]
    field_simp [hdeg' y hy]
  have hstep' : ∀ y ∈ T,
      (G.degree y : ℝ) * f y * (RWRS.walkOp G g y) =
        f y * (∑ z ∈ G.neighborFinset y, g z) := by
    intro y hy
    rw [RWRS.walkOp]
    field_simp [hdeg' y hy]
  rw [Finset.sum_congr rfl hstep, Finset.sum_congr rfl hstep']
  exact carne_edge_inner_swap T f g hf hg

/-- **Finite propagation speed for `walkOp`.** If `f` vanishes outside the
ball of radius `r` about `x`, then `walkOp G f` vanishes outside the ball of
radius `r + 1`, since a nonzero value at `y` forces some neighbour of `y` to
carry a nonzero `f`. -/
theorem carne_walkOp_supported_dist {V : Type*} {G : SimpleGraph V}
    [G.LocallyFinite] (hG : G.Connected) (x : V) (f : V → ℝ) (r : ℕ)
    (hf : ∀ z, f z ≠ 0 → G.dist x z ≤ r) (y : V)
    (hy : RWRS.walkOp G f y ≠ 0) : G.dist x y ≤ r + 1 := by
  classical
  rw [RWRS.walkOp] at hy
  have hsum : ∑ z ∈ G.neighborFinset y, f z ≠ 0 := by
    intro hz
    exact hy (by rw [hz, zero_div])
  have hex : ∃ z ∈ G.neighborFinset y, f z ≠ 0 := by
    by_contra hnone
    push Not at hnone
    exact hsum (Finset.sum_eq_zero fun z hz => hnone z hz)
  obtain ⟨z, hz, hfz⟩ := hex
  have hadj : G.Adj y z := (SimpleGraph.mem_neighborFinset _ _ _).1 hz
  have hdist : G.dist x z ≤ r := hf z hfz
  have htri : G.dist x y ≤ G.dist x z + G.dist z y := hG.dist_triangle
  have hzy : G.dist z y = 1 :=
    SimpleGraph.dist_eq_one_iff_adj.mpr hadj.symm
  omega

/-- Iterating `carne_walkOp_supported_dist` through the Chebyshev recursion:
if `f` is supported within `r` of `x`, then `carne_chebApply G f k` is
supported within `r + k` of `x`. -/
theorem carne_chebApply_supported_dist {V : Type*} {G : SimpleGraph V}
    [G.LocallyFinite] (hG : G.Connected) (x : V) (f : V → ℝ) (r : ℕ)
    (hf : ∀ z, f z ≠ 0 → G.dist x z ≤ r) :
    ∀ k y, carne_chebApply G f k y ≠ 0 → G.dist x y ≤ r + k := by
  classical
  intro k
  induction k using Nat.twoStepInduction with
  | zero =>
      intro y hy
      exact hf y hy
  | one =>
      intro y hy
      rw [carne_chebApply] at hy
      exact carne_walkOp_supported_dist hG x f r hf y hy
  | more k ihk ihsk =>
      intro y hy
      change 2 * RWRS.walkOp G
          (carne_chebApply G f (k + 1)) y -
          carne_chebApply G f k y ≠ 0 at hy
      by_contra hnot
      have hwalk : RWRS.walkOp G (carne_chebApply G f (k + 1)) y = 0 := by
        by_contra hne
        have hdist := carne_walkOp_supported_dist hG x
          (carne_chebApply G f (k + 1)) (r + (k + 1))
          (fun z hz => ihsk z hz) y hne
        omega
      have hprev : carne_chebApply G f k y = 0 := by
        by_contra hne
        have hdist := ihk y hne
        omega
      have hzero : (0 : ℝ) ≠ 0 := by
        norm_num [hwalk, hprev] at hy
      exact hzero rfl

/-- `walkOp` commutes with `carne_chebApply`: applying `walkOp G` after the
`k`-th Chebyshev step on `f` agrees with applying it first, by induction on
the shared recursion. -/
theorem carne_walkOp_cheb_comm {V : Type*} {G : SimpleGraph V}
    [G.LocallyFinite] (f : V → ℝ) : ∀ k,
      RWRS.walkOp G (carne_chebApply G f k) =
        carne_chebApply G (RWRS.walkOp G f) k := by
  intro k
  induction k using Nat.twoStepInduction with
  | zero => rfl
  | one =>
      funext v
      rfl
  | more k ihk ihsk =>
      funext v
      change RWRS.walkOp G
          (fun w => 2 * RWRS.walkOp G
            (carne_chebApply G f (k + 1)) w -
            carne_chebApply G f k w) v = _
      rw [show (fun w => 2 * RWRS.walkOp G
          (carne_chebApply G f (k + 1)) w -
          carne_chebApply G f k w) =
          (2 : ℝ) • carne_walkOpLinear G
              (carne_chebApply G f (k + 1)) -
            carne_chebApply G f k by
        funext w
        simp [carne_walkOpLinear]]
      change (carne_walkOpLinear G
        ((2 : ℝ) • carne_walkOpLinear G
          (carne_chebApply G f (k + 1)) -
          carne_chebApply G f k)) v = _
      rw [map_sub, map_smul]
      rw [show carne_walkOpLinear G
          (carne_chebApply G f (k + 1)) =
            RWRS.walkOp G (carne_chebApply G f (k + 1)) by rfl,
        show carne_walkOpLinear G (carne_chebApply G f k) =
            RWRS.walkOp G (carne_chebApply G f k) by rfl]
      rw [carne_chebApply, ihsk, ihk]
      simp [carne_walkOpLinear]

/-- **`carne_chebApply` is self-adjoint for the degree-weighted inner
product**, on a ball large enough to contain the propagation of both `f` and
`g`: combining `carne_weighted_walkOp_inner_comm` with the finite-propagation
bounds by induction on the Chebyshev step `k`. -/
theorem carne_cheb_inner_comm {V : Type*} {G : SimpleGraph V}
    [G.LocallyFinite] (hG : G.Connected) (hdeg : ∀ v : V, 0 < G.degree v)
    (x : V) (r R : ℕ) (f g : V → ℝ) : ∀ k,
    (∀ z, f z ≠ 0 → G.dist x z ≤ r) →
    (∀ z, g z ≠ 0 → G.dist x z ≤ r) →
    r + 2 * k ≤ R →
    (∑ y ∈ LatticeProb.Graph.ballFinset G x R,
        (G.degree y : ℝ) * (carne_chebApply G f k y) * g y) =
      ∑ y ∈ LatticeProb.Graph.ballFinset G x R,
        (G.degree y : ℝ) * f y * (carne_chebApply G g k y) := by
  intro k
  induction k using Nat.twoStepInduction generalizing r R f g with
  | zero =>
      intro hf hg hR
      apply Finset.sum_congr rfl
      intro y hy
      simp [carne_chebApply]
  | one =>
      intro hf hg hR
      exact carne_weighted_walkOp_inner_comm hdeg _ _ _
        (fun z hz => LatticeProb.Graph.mem_ballFinset_of_dist_le hG
          ((hf z hz).trans (by omega)))
        (fun z hz => LatticeProb.Graph.mem_ballFinset_of_dist_le hG
          ((hg z hz).trans (by omega)))
  | more k ihk ihsk =>
      intro hf hg hR
      have hRk : r + k ≤ R := by omega
      have hRsk : r + (k + 1) ≤ R := by omega
      have hTf : ∀ z, carne_chebApply G f (k + 1) z ≠ 0 →
          z ∈ LatticeProb.Graph.ballFinset G x R := by
        intro z hz
        apply LatticeProb.Graph.mem_ballFinset_of_dist_le hG
        exact (carne_chebApply_supported_dist hG x f r hf (k + 1) z hz).trans
          (by omega)
      have hTfk : ∀ z, carne_chebApply G f k z ≠ 0 →
          z ∈ LatticeProb.Graph.ballFinset G x R := by
        intro z hz
        apply LatticeProb.Graph.mem_ballFinset_of_dist_le hG
        exact (carne_chebApply_supported_dist hG x f r hf k z hz).trans
          (by omega)
      have hTg : ∀ z, carne_chebApply G g k z ≠ 0 →
          z ∈ LatticeProb.Graph.ballFinset G x R := by
        intro z hz
        apply LatticeProb.Graph.mem_ballFinset_of_dist_le hG
        exact (carne_chebApply_supported_dist hG x g r hg k z hz).trans
          (by omega)
      have hPgt : ∀ z, RWRS.walkOp G g z ≠ 0 →
          G.dist x z ≤ r + 1 :=
        carne_walkOp_supported_dist hG x g r hg
      have hPg : ∀ z, RWRS.walkOp G g z ≠ 0 →
          z ∈ LatticeProb.Graph.ballFinset G x R := by
        intro z hz
        apply LatticeProb.Graph.mem_ballFinset_of_dist_le hG
        exact (hPgt z hz).trans (by omega)
      have hPgj : ∀ z, carne_chebApply G (RWRS.walkOp G g) (k + 1) z ≠ 0 →
          z ∈ LatticeProb.Graph.ballFinset G x R := by
        intro z hz
        apply LatticeProb.Graph.mem_ballFinset_of_dist_le hG
        exact (carne_chebApply_supported_dist hG x (RWRS.walkOp G g)
          (r + 1) hPgt (k + 1) z hz).trans (by omega)
      calc
        (∑ y ∈ LatticeProb.Graph.ballFinset G x R,
            (G.degree y : ℝ) *
              (carne_chebApply G f (k + 2) y) * g y) =
            ∑ y ∈ LatticeProb.Graph.ballFinset G x R,
              (2 * ((G.degree y : ℝ) *
                (RWRS.walkOp G (carne_chebApply G f (k + 1)) y) * g y) -
                (G.degree y : ℝ) *
                  (carne_chebApply G f k y) * g y) := by
          apply Finset.sum_congr rfl
          intro y hy
          rw [carne_chebApply]
          ring
        _ = 2 * (∑ y ∈ LatticeProb.Graph.ballFinset G x R,
              (G.degree y : ℝ) *
                (RWRS.walkOp G (carne_chebApply G f (k + 1)) y) * g y) -
              ∑ y ∈ LatticeProb.Graph.ballFinset G x R,
                (G.degree y : ℝ) *
                  (carne_chebApply G f k y) * g y := by
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
        _ = 2 * (∑ y ∈ LatticeProb.Graph.ballFinset G x R,
              (G.degree y : ℝ) *
                (carne_chebApply G f (k + 1) y) *
                (RWRS.walkOp G g y)) -
              ∑ y ∈ LatticeProb.Graph.ballFinset G x R,
                (G.degree y : ℝ) *
                  (carne_chebApply G f k y) * g y := by
          have hswap := carne_weighted_walkOp_inner_comm hdeg
            (LatticeProb.Graph.ballFinset G x R)
            (carne_chebApply G f (k + 1)) g hTf
            (fun z hz => LatticeProb.Graph.mem_ballFinset_of_dist_le hG
              ((hg z hz).trans (by omega)))
          rw [hswap]
        _ = 2 * (∑ y ∈ LatticeProb.Graph.ballFinset G x R,
              (G.degree y : ℝ) * f y *
                (carne_chebApply G (RWRS.walkOp G g) (k + 1) y)) -
              ∑ y ∈ LatticeProb.Graph.ballFinset G x R,
                (G.degree y : ℝ) * f y *
                  (carne_chebApply G g k y) := by
          have hfr : ∀ z, f z ≠ 0 → G.dist x z ≤ r + 1 := by
            intro z hz
            exact (hf z hz).trans (by omega)
          rw [ihsk (r + 1) R f (RWRS.walkOp G g) hfr hPgt (by omega),
            ihk r R f g hf hg (by omega)]
        _ = ∑ y ∈ LatticeProb.Graph.ballFinset G x R,
              (G.degree y : ℝ) * f y *
                (carne_chebApply G g (k + 2) y) := by
          calc
            _ = ∑ y ∈ LatticeProb.Graph.ballFinset G x R,
                (2 * ((G.degree y : ℝ) * f y *
                  (carne_chebApply G (RWRS.walkOp G g) (k + 1) y)) -
                  (G.degree y : ℝ) * f y *
                    (carne_chebApply G g k y)) := by
              rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
            _ = _ := by
              apply Finset.sum_congr rfl
              intro y hy
              rw [carne_chebApply, ← carne_walkOp_cheb_comm]
              ring

/-- The `k`-step Chebyshev image of the point mass at `x` vanishes at any `y`
farther than `k` steps away, by two-step induction paralleling
`carne_walkOp_supported_dist`. -/
theorem carne_chebApply_delta_zero_of_dist_lt {V : Type*} {G : SimpleGraph V}
    [G.LocallyFinite] (hG : G.Connected) (x y : V) :
    ∀ k, k < G.dist x y →
      carne_chebApply G (fun z => if z = x then 1 else 0) k y = 0 := by
  classical
  intro k
  induction k using Nat.twoStepInduction generalizing y with
  | zero =>
      intro h
      have hxy : x ≠ y := by
        intro hxy
        subst y
        simp at h
      have hyx : y ≠ x := hxy.symm
      simp [carne_chebApply, hyx]
  | one =>
      intro h
      rw [carne_chebApply, RWRS.walkOp]
      have hsum : ∑ z ∈ G.neighborFinset y,
          (if z = x then (1 : ℝ) else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro z hz
        have hadj : G.Adj y z := (SimpleGraph.mem_neighborFinset _ _ _).1 hz
        have hzx : z ≠ x := by
          intro hzx
          subst z
          have hone : G.dist x y = 1 :=
            SimpleGraph.dist_eq_one_iff_adj.mpr hadj.symm
          omega
        simp [hzx]
      change (∑ z ∈ G.neighborFinset y, (if z = x then 1 else 0)) /
          (G.degree y : ℝ) = 0
      exact (congrArg (fun q : ℝ => q / (G.degree y : ℝ)) hsum).trans (zero_div _)
  | more k ihk ihsk =>
      intro h
      rw [carne_chebApply]
      have hwalk : RWRS.walkOp G
          (carne_chebApply G (fun z => if z = x then 1 else 0) (k + 1)) y = 0 := by
        rw [RWRS.walkOp]
        have hsum : ∑ z ∈ G.neighborFinset y,
            carne_chebApply G (fun z => if z = x then 1 else 0) (k + 1) z = 0 := by
          apply Finset.sum_eq_zero
          intro z hz
          have hadj : G.Adj y z := (SimpleGraph.mem_neighborFinset _ _ _).1 hz
          apply ihsk z
          have htri : G.dist x y ≤ G.dist x z + G.dist z y :=
            hG.dist_triangle
          have hzy : G.dist z y = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hadj.symm
          omega
        rw [hsum, zero_div]
      change 2 * RWRS.walkOp G
          (carne_chebApply G (fun z => if z = x then 1 else 0) (k + 1)) y -
          carne_chebApply G (fun z => if z = x then 1 else 0) k y = 0
      rw [hwalk, ihk y (by omega)]
      ring

/-- `walkOp` commutes with `carne_chebSecondApply`, as `carne_walkOp_cheb_comm`
does for the first kind, by induction on the shared recursion. -/
theorem carne_walkOp_chebSecond_comm {V : Type*} {G : SimpleGraph V}
    [G.LocallyFinite] (f : V → ℝ) : ∀ k,
      RWRS.walkOp G (carne_chebSecondApply G f k) =
        carne_chebSecondApply G (RWRS.walkOp G f) k := by
  intro k
  induction k using Nat.twoStepInduction with
  | zero => rfl
  | one =>
      funext v
      change (carne_walkOpLinear G
        ((2 : ℝ) • carne_walkOpLinear G f)) v = _
      rw [map_smul]
      rw [carne_chebSecondApply]
      simp [carne_walkOpLinear]
  | more k ihk ihsk =>
      funext v
      change RWRS.walkOp G
          (fun w => 2 * RWRS.walkOp G
            (carne_chebSecondApply G f (k + 1)) w -
            carne_chebSecondApply G f k w) v = _
      rw [show (fun w => 2 * RWRS.walkOp G
          (carne_chebSecondApply G f (k + 1)) w -
          carne_chebSecondApply G f k w) =
          (2 : ℝ) • carne_walkOpLinear G
              (carne_chebSecondApply G f (k + 1)) -
            carne_chebSecondApply G f k by
        funext w
        simp [carne_walkOpLinear]]
      change (carne_walkOpLinear G
        ((2 : ℝ) • carne_walkOpLinear G
          (carne_chebSecondApply G f (k + 1)) -
          carne_chebSecondApply G f k)) v = _
      rw [map_sub, map_smul]
      rw [show carne_walkOpLinear G
          (carne_chebSecondApply G f (k + 1)) =
            RWRS.walkOp G (carne_chebSecondApply G f (k + 1)) by rfl,
        show carne_walkOpLinear G (carne_chebSecondApply G f k) =
            RWRS.walkOp G (carne_chebSecondApply G f k) by rfl]
      rw [carne_chebSecondApply, ihsk, ihk]
      simp [carne_walkOpLinear]

/-- Finite propagation for the second-kind Chebyshev application: if `f` is
supported within `r` of `x`, then `carne_chebSecondApply G f k` is supported
within `r + k`, as `carne_chebApply_supported_dist` for the first kind. -/
theorem carne_chebSecondApply_supported_dist {V : Type*} {G : SimpleGraph V}
    [G.LocallyFinite] (hG : G.Connected) (x : V) (f : V → ℝ) (r : ℕ)
    (hf : ∀ z, f z ≠ 0 → G.dist x z ≤ r) : ∀ k y,
      carne_chebSecondApply G f k y ≠ 0 → G.dist x y ≤ r + k := by
  intro k
  induction k using Nat.twoStepInduction with
  | zero =>
      intro y hy
      exact hf y hy
  | one =>
      intro y hy
      have hwalk : RWRS.walkOp G f y ≠ 0 := by
        intro hzero
        apply hy
        simp [carne_chebSecondApply, hzero]
      exact carne_walkOp_supported_dist hG x f r hf y hwalk
  | more k ihk ihsk =>
      intro y hy
      rw [carne_chebSecondApply] at hy
      have hnext : ∀ z, carne_chebSecondApply G f (k + 1) z ≠ 0 →
          G.dist x z ≤ r + (k + 1) := by
        intro z hz
        exact ihsk z hz
      have hwalk : ∀ z, RWRS.walkOp G
          (carne_chebSecondApply G f (k + 1)) z ≠ 0 →
          G.dist x z ≤ r + (k + 1) + 1 := by
        intro z hz
        exact carne_walkOp_supported_dist hG x
          (carne_chebSecondApply G f (k + 1)) (r + (k + 1)) hnext z hz
      have hprev : ∀ z, carne_chebSecondApply G f k z ≠ 0 →
          G.dist x z ≤ r + k := by
        intro z hz
        exact ihk z hz
      by_contra hdist
      have hwalkzero : RWRS.walkOp G
          (carne_chebSecondApply G f (k + 1)) y = 0 := by
        by_contra hzero
        have hle := hwalk y hzero
        omega
      have hprevzero : carne_chebSecondApply G f k y = 0 := by
        by_contra hzero
        have hle := hprev y hzero
        omega
      have hzero : (0 : ℝ) ≠ 0 := by
        change 2 * RWRS.walkOp G
            (carne_chebSecondApply G f (k + 1)) y -
          carne_chebSecondApply G f k y ≠ 0 at hy
        norm_num [hwalkzero, hprevzero] at hy
      exact hzero rfl

/-- **`carne_chebSecondApply` is self-adjoint for the degree-weighted inner
product**, on a large enough ball, as `carne_cheb_inner_comm` for the first
kind. -/
theorem carne_chebSecond_inner_comm {V : Type*} {G : SimpleGraph V}
    [G.LocallyFinite] (hG : G.Connected) (hdeg : ∀ v : V, 0 < G.degree v)
    (x : V) (r R : ℕ) (f g : V → ℝ) : ∀ k,
    (∀ z, f z ≠ 0 → G.dist x z ≤ r) →
    (∀ z, g z ≠ 0 → G.dist x z ≤ r) →
    r + 2 * k ≤ R →
    (∑ y ∈ LatticeProb.Graph.ballFinset G x R,
        (G.degree y : ℝ) * (carne_chebSecondApply G f k y) * g y) =
      ∑ y ∈ LatticeProb.Graph.ballFinset G x R,
        (G.degree y : ℝ) * f y * (carne_chebSecondApply G g k y) := by
  intro k
  induction k using Nat.twoStepInduction generalizing r R f g with
  | zero =>
      intro hf hg hR
      apply Finset.sum_congr rfl
      intro y hy
      simp [carne_chebSecondApply]
  | one =>
      intro hf hg hR
      have hswap := carne_weighted_walkOp_inner_comm hdeg
        (LatticeProb.Graph.ballFinset G x R) f g
        (fun z hz => LatticeProb.Graph.mem_ballFinset_of_dist_le hG
          ((hf z hz).trans (by omega)))
        (fun z hz => LatticeProb.Graph.mem_ballFinset_of_dist_le hG
          ((hg z hz).trans (by omega)))
      calc
        (∑ y ∈ LatticeProb.Graph.ballFinset G x R,
            (G.degree y : ℝ) * (carne_chebSecondApply G f 1 y) * g y) =
            ∑ y ∈ LatticeProb.Graph.ballFinset G x R,
              2 * ((G.degree y : ℝ) * (RWRS.walkOp G f y) * g y) := by
          apply Finset.sum_congr rfl
          intro y hy
          rw [carne_chebSecondApply]
          ring
        _ = 2 * (∑ y ∈ LatticeProb.Graph.ballFinset G x R,
              (G.degree y : ℝ) * (RWRS.walkOp G f y) * g y) := by
          rw [Finset.mul_sum]
        _ = 2 * (∑ y ∈ LatticeProb.Graph.ballFinset G x R,
              (G.degree y : ℝ) * f y * (RWRS.walkOp G g y)) := by
          rw [hswap]
        _ = ∑ y ∈ LatticeProb.Graph.ballFinset G x R,
              (G.degree y : ℝ) * f y *
                (carne_chebSecondApply G g 1 y) := by
          calc
            _ = ∑ y ∈ LatticeProb.Graph.ballFinset G x R,
                2 * ((G.degree y : ℝ) * f y * (RWRS.walkOp G g y)) := by
              rw [Finset.mul_sum]
            _ = _ := by
              apply Finset.sum_congr rfl
              intro y hy
              rw [carne_chebSecondApply]
              ring
  | more k ihk ihsk =>
      intro hf hg hR
      have hTf : ∀ z, carne_chebSecondApply G f (k + 1) z ≠ 0 →
          z ∈ LatticeProb.Graph.ballFinset G x R := by
        intro z hz
        apply LatticeProb.Graph.mem_ballFinset_of_dist_le hG
        exact (carne_chebSecondApply_supported_dist hG x f r hf
          (k + 1) z hz).trans (by omega)
      have hPgt : ∀ z, RWRS.walkOp G g z ≠ 0 →
          G.dist x z ≤ r + 1 :=
        carne_walkOp_supported_dist hG x g r hg
      have hfr : ∀ z, f z ≠ 0 → G.dist x z ≤ r + 1 := by
        intro z hz
        exact (hf z hz).trans (by omega)
      calc
        (∑ y ∈ LatticeProb.Graph.ballFinset G x R,
            (G.degree y : ℝ) *
              (carne_chebSecondApply G f (k + 2) y) * g y) =
            ∑ y ∈ LatticeProb.Graph.ballFinset G x R,
              (2 * ((G.degree y : ℝ) *
                (RWRS.walkOp G (carne_chebSecondApply G f (k + 1)) y) * g y) -
                (G.degree y : ℝ) *
                  (carne_chebSecondApply G f k y) * g y) := by
          apply Finset.sum_congr rfl
          intro y hy
          rw [carne_chebSecondApply]
          ring
        _ = 2 * (∑ y ∈ LatticeProb.Graph.ballFinset G x R,
              (G.degree y : ℝ) *
                (RWRS.walkOp G (carne_chebSecondApply G f (k + 1)) y) * g y) -
              ∑ y ∈ LatticeProb.Graph.ballFinset G x R,
                (G.degree y : ℝ) *
                  (carne_chebSecondApply G f k y) * g y := by
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
        _ = 2 * (∑ y ∈ LatticeProb.Graph.ballFinset G x R,
              (G.degree y : ℝ) *
                (carne_chebSecondApply G f (k + 1) y) *
                (RWRS.walkOp G g y)) -
              ∑ y ∈ LatticeProb.Graph.ballFinset G x R,
                (G.degree y : ℝ) *
                  (carne_chebSecondApply G f k y) * g y := by
          have hswap := carne_weighted_walkOp_inner_comm hdeg
            (LatticeProb.Graph.ballFinset G x R)
            (carne_chebSecondApply G f (k + 1)) g hTf
            (fun z hz => LatticeProb.Graph.mem_ballFinset_of_dist_le hG
              ((hg z hz).trans (by omega)))
          rw [hswap]
        _ = 2 * (∑ y ∈ LatticeProb.Graph.ballFinset G x R,
              (G.degree y : ℝ) * f y *
                (carne_chebSecondApply G (RWRS.walkOp G g) (k + 1) y)) -
              ∑ y ∈ LatticeProb.Graph.ballFinset G x R,
                (G.degree y : ℝ) * f y *
                  (carne_chebSecondApply G g k y) := by
          rw [ihsk (r + 1) R f (RWRS.walkOp G g) hfr hPgt (by omega),
            ihk r R f g hf hg (by omega)]
        _ = ∑ y ∈ LatticeProb.Graph.ballFinset G x R,
              (G.degree y : ℝ) * f y *
                (carne_chebSecondApply G g (k + 2) y) := by
          calc
            _ = ∑ y ∈ LatticeProb.Graph.ballFinset G x R,
                (2 * ((G.degree y : ℝ) * f y *
                  (carne_chebSecondApply G (RWRS.walkOp G g) (k + 1) y)) -
                  (G.degree y : ℝ) * f y *
                    (carne_chebSecondApply G g k y)) := by
              rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
            _ = _ := by
              apply Finset.sum_congr rfl
              intro y hy
              rw [carne_chebSecondApply, ← carne_walkOp_chebSecond_comm]
              ring

/-- **The key `ℓ²` bound at the heart of the Carne–Varopoulos argument.** The
degree-weighted sum of `(T_n(P) δ_x) ^ 2` over a ball wide enough to contain
all the propagation is at most `deg(x)`, proved by strong induction via the
Pell identity `carne_chebPellApply` and the self-adjointness and contraction
lemmas above; this substitutes for `‖T_n(P)‖ ≤ 1` on the operator norm. -/
theorem carne_cheb_delta_sq_le {V : Type*} {G : SimpleGraph V}
    [G.LocallyFinite] (hG : G.Connected) (hdeg : ∀ v : V, 0 < G.degree v)
    (x : V) : ∀ n,
    ∑ y ∈ LatticeProb.Graph.ballFinset G x (4 * n + 4),
        (G.degree y : ℝ) *
          (carne_chebApply G (fun z => if z = x then 1 else 0) n y) ^ 2 ≤
      (G.degree x : ℝ) := by
  classical
  intro n
  let δ : V → ℝ := fun z => if z = x then 1 else 0
  let B : Finset V := LatticeProb.Graph.ballFinset G x (4 * n + 4)
  have hxB : x ∈ B := by
    apply LatticeProb.Graph.mem_ballFinset_of_dist_le hG
    simp
  have hδ : ∀ z, δ z ≠ 0 → G.dist x z ≤ 0 := by
    intro z hz
    by_cases hzx : z = x
    · subst z
      simp
    · simp [δ, hzx] at hz
  have hdelta_sum :
      (∑ y ∈ B, (G.degree y : ℝ) * δ y * δ y) = (G.degree x : ℝ) := by
    rw [Finset.sum_eq_single x]
    · simp [δ]
    · intro y hy hyx
      simp [δ, hyx]
    · exact fun hnot => (hnot hxB).elim
  cases n with
  | zero =>
      have hle := hdelta_sum.le
      simpa [δ, B, carne_chebApply] using hle
  | succ m =>
      let r : ℕ := 2 * m + 4
      let R : ℕ := 4 * (m + 1) + 4
      have hδ' : ∀ z, δ z ≠ 0 → G.dist x z ≤ r := by
        intro z hz
        exact (hδ z hz).trans (by dsimp [r]; omega)
      have hT : ∀ z, carne_chebApply G δ (m + 1) z ≠ 0 →
          G.dist x z ≤ r := by
        intro z hz
        have hz' := carne_chebApply_supported_dist hG x δ 0
          hδ (m + 1) z hz
        omega
      have hU : ∀ z, carne_chebSecondApply G δ m z ≠ 0 →
          G.dist x z ≤ m := by
        intro z hz
        simpa using carne_chebSecondApply_supported_dist hG x δ 0
          hδ m z hz
      have hPU : ∀ z, RWRS.walkOp G
          (carne_chebSecondApply G δ m) z ≠ 0 →
          G.dist x z ≤ m + 1 := by
        intro z hz
        exact carne_walkOp_supported_dist hG x
          (carne_chebSecondApply G δ m) m hU z hz
      have hPPU : ∀ z, RWRS.walkOp G (RWRS.walkOp G
          (carne_chebSecondApply G δ m)) z ≠ 0 →
          G.dist x z ≤ m + 2 := by
        intro z hz
        exact carne_walkOp_supported_dist hG x
          (RWRS.walkOp G (carne_chebSecondApply G δ m)) (m + 1) hPU z hz
      have hUU : ∀ z, carne_chebSecondApply G
          (carne_chebSecondApply G δ m) m z ≠ 0 →
          G.dist x z ≤ 2 * m := by
        intro z hz
        have hz' := carne_chebSecondApply_supported_dist hG x
          (carne_chebSecondApply G δ m) m hU m z hz
        omega
      have hUr : ∀ z, carne_chebSecondApply G δ m z ≠ 0 →
          G.dist x z ≤ r := by
        intro z hz
        exact (hU z hz).trans (by dsimp [r]; omega)
      have hPPUr : ∀ z, RWRS.walkOp G (RWRS.walkOp G
          (carne_chebSecondApply G δ m)) z ≠ 0 →
          G.dist x z ≤ r := by
        intro z hz
        exact (hPPU z hz).trans (by dsimp [r]; omega)
      have hTcomm := carne_cheb_inner_comm hG hdeg x r R δ
        (carne_chebApply G δ (m + 1)) (m + 1) hδ' hT (by omega)
      have hUcomm := carne_chebSecond_inner_comm hG hdeg x r R δ
        (carne_chebSecondApply G δ m) m hδ' hUr (by omega)
      have hUUcomm := carne_chebSecond_inner_comm hG hdeg x r R δ
        (RWRS.walkOp G (RWRS.walkOp G (carne_chebSecondApply G δ m))) m
        hδ' hPPUr (by omega)
      have hPcomm := carne_weighted_walkOp_inner_comm hdeg B
        (carne_chebSecondApply G δ m)
        (RWRS.walkOp G (carne_chebSecondApply G δ m))
        (fun z hz => LatticeProb.Graph.mem_ballFinset_of_dist_le hG
          ((hU z hz).trans (by omega)))
        (fun z hz => LatticeProb.Graph.mem_ballFinset_of_dist_le hG
          ((hPU z hz).trans (by omega)))
      have hUcomm_fun :
          carne_chebSecondApply G
              (RWRS.walkOp G (RWRS.walkOp G
                (carne_chebSecondApply G δ m))) m =
            RWRS.walkOp G (RWRS.walkOp G
              (carne_chebSecondApply G
                (carne_chebSecondApply G δ m) m)) := by
        have h₁ := carne_walkOp_chebSecond_comm
          (G := G) (RWRS.walkOp G (carne_chebSecondApply G δ m)) m
        have h₂ := carne_walkOp_chebSecond_comm
          (G := G) (carne_chebSecondApply G δ m) m
        calc
          carne_chebSecondApply G
              (RWRS.walkOp G (RWRS.walkOp G
                (carne_chebSecondApply G δ m))) m =
              RWRS.walkOp G (carne_chebSecondApply G
                (RWRS.walkOp G (carne_chebSecondApply G δ m)) m) :=
            h₁.symm
          _ = RWRS.walkOp G (RWRS.walkOp G
              (carne_chebSecondApply G
                (carne_chebSecondApply G δ m) m)) := by
            rw [h₂]
      have hPUcomm :
          (∑ y ∈ B, (G.degree y : ℝ) *
            (RWRS.walkOp G (carne_chebSecondApply G δ m) y) ^ 2) =
            ∑ y ∈ B, (G.degree y : ℝ) * δ y *
              (RWRS.walkOp G (RWRS.walkOp G
                (carne_chebSecondApply G
                  (carne_chebSecondApply G δ m) m)) y) := by
        calc
          (∑ y ∈ B, (G.degree y : ℝ) *
              (RWRS.walkOp G (carne_chebSecondApply G δ m) y) ^ 2) =
              ∑ y ∈ B, (G.degree y : ℝ) *
                (carne_chebSecondApply G δ m y) *
                (RWRS.walkOp G (RWRS.walkOp G
                  (carne_chebSecondApply G δ m)) y) := by
            calc
              _ = ∑ y ∈ B, (G.degree y : ℝ) *
                  (RWRS.walkOp G (carne_chebSecondApply G δ m) y) *
                  (RWRS.walkOp G (carne_chebSecondApply G δ m) y) := by
                apply Finset.sum_congr rfl
                intro y hy
                ring
              _ = _ := hPcomm
          _ = ∑ y ∈ B, (G.degree y : ℝ) * δ y *
                (carne_chebSecondApply G
                  (RWRS.walkOp G (RWRS.walkOp G
                    (carne_chebSecondApply G δ m))) m y) := hUUcomm
          _ = _ := by rw [hUcomm_fun]
      have hUUcomm' :
          (∑ y ∈ B, (G.degree y : ℝ) *
            (carne_chebSecondApply G δ m y) ^ 2) =
            ∑ y ∈ B, (G.degree y : ℝ) * δ y *
              (carne_chebSecondApply G
                (carne_chebSecondApply G δ m) m y) := by
        calc
          _ = ∑ y ∈ B, (G.degree y : ℝ) *
                (carne_chebSecondApply G δ m y) *
                (carne_chebSecondApply G δ m y) := by
              apply Finset.sum_congr rfl
              intro y hy
              ring
          _ = _ := hUcomm
      have hTcomm' :
          (∑ y ∈ B, (G.degree y : ℝ) * δ y *
            (carne_chebApply G
              (carne_chebApply G δ (m + 1)) (m + 1) y)) =
            ∑ y ∈ B, (G.degree y : ℝ) *
              (carne_chebApply G δ (m + 1) y) ^ 2 := by
        calc
          _ = ∑ y ∈ B, (G.degree y : ℝ) *
                (carne_chebApply G δ (m + 1) y) *
                (carne_chebApply G δ (m + 1) y) := hTcomm.symm
          _ = _ := by
              apply Finset.sum_congr rfl
              intro y hy
              ring
      have hcontract := carne_walkOp_weighted_sq_sum_le hdeg
        (carne_chebSecondApply G δ m) B
        (fun y hy => LatticeProb.Graph.mem_ballFinset_of_dist_le hG
          ((hU y hy).trans (by omega)))
        (fun y z hy hadj => by
          apply LatticeProb.Graph.mem_ballFinset_of_dist_le hG
          have htri : G.dist x z ≤ G.dist x y + G.dist y z :=
            hG.dist_triangle
          have hyz : G.dist y z = 1 :=
            SimpleGraph.dist_eq_one_iff_adj.mpr hadj
          have hdy := hU y hy
          omega)
      have hpell := carne_chebPellApply G δ m
      have hsum_pell :
          (∑ y ∈ B, (G.degree y : ℝ) * δ y *
            (carne_chebApply G
                (carne_chebApply G δ (m + 1)) (m + 1) y -
              RWRS.walkOp G (RWRS.walkOp G
                (carne_chebSecondApply G
                  (carne_chebSecondApply G δ m) m)) y +
              carne_chebSecondApply G
                (carne_chebSecondApply G δ m) m y)) =
            ∑ y ∈ B, (G.degree y : ℝ) * δ y * δ y := by
        apply Finset.sum_congr rfl
        intro y hy
        have hpy := congrFun hpell y
        change (carne_chebApply G
            (carne_chebApply G δ (m + 1)) (m + 1) y -
          RWRS.walkOp G (RWRS.walkOp G
            (carne_chebSecondApply G
              (carne_chebSecondApply G δ m) m)) y +
          carne_chebSecondApply G
            (carne_chebSecondApply G δ m) m y) = δ y at hpy
        rw [hpy]
      simp_rw [mul_add, mul_sub] at hsum_pell
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib] at hsum_pell
      rw [hTcomm', ← hPUcomm, ← hUUcomm', hdelta_sum] at hsum_pell
      have hbound :
          (∑ y ∈ B, (G.degree y : ℝ) *
            (carne_chebApply G δ (m + 1) y) ^ 2) ≤
            (G.degree x : ℝ) := by
        linarith
      simpa [δ, B] using hbound

/-- The three-term recurrence for `carne_chebApply` reindexed over `ℤ` by
`natAbs`: `walkOp G (T_{|k|} f) = (T_{|k+1|} f + T_{|k-1|} f) / 2`, matching
the classical Chebyshev recurrence `2x T_k = T_{k+1} + T_{k-1}` at `x = P`. -/
theorem carne_walkOp_cheb_signed {V : Type*} {G : SimpleGraph V}
    [G.LocallyFinite] (f : V → ℝ) (k : ℤ) :
    RWRS.walkOp G (carne_chebApply G f k.natAbs) =
      (carne_chebApply G f (k + 1).natAbs +
        carne_chebApply G f (k - 1).natAbs) / 2 := by
  funext v
  cases k with
  | ofNat k =>
    cases k with
    | zero =>
      simp
      rw [carne_chebApply]
      rfl
    | succ j =>
      have h0 : (Int.ofNat (j + 1)).natAbs = j + 1 := by
        exact_mod_cast (Int.natAbs_of_nonneg (show (0 : ℤ) ≤ j + 1 by omega))
      have h1 : (Int.ofNat (j + 1) + 1).natAbs = j + 2 := by
        have h : Int.ofNat (j + 1) + 1 = Int.ofNat (j + 2) := by
          norm_num [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
          ring_nf
        rw [h]
        exact_mod_cast (Int.natAbs_of_nonneg (show (0 : ℤ) ≤ j + 2 by omega))
      have h2 : (Int.ofNat (j + 1) - 1).natAbs = j := by
        have h : Int.ofNat (j + 1) - 1 = Int.ofNat j := by
          norm_num [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
        rw [h]
        exact_mod_cast (Int.natAbs_of_nonneg (show (0 : ℤ) ≤ j by omega))
      rw [h0, h1, h2]
      change RWRS.walkOp G (carne_chebApply G f (j + 1)) v =
        (carne_chebApply G f (j + 2) v +
          carne_chebApply G f j v) / 2
      simp only [carne_chebApply]
      ring_nf
  | negSucc j =>
    cases j with
    | zero =>
      simp
      change RWRS.walkOp G (carne_chebApply G f 1) v =
        (f v + carne_chebApply G f 2 v) / 2
      simp only [carne_chebApply]
      ring_nf
    | succ j =>
      have h0 : (Int.negSucc (j + 1)).natAbs = j + 2 := by
        exact_mod_cast (Int.natAbs_of_nonneg (show (0 : ℤ) ≤ j + 2 by omega))
      have h1 : (Int.negSucc (j + 1) + 1).natAbs = j + 1 := by
        have h : Int.negSucc (j + 1) + 1 = Int.negSucc j := by omega
        rw [h]
        exact_mod_cast (Int.natAbs_of_nonneg (show (0 : ℤ) ≤ j + 1 by omega))
      have h2 : (Int.negSucc (j + 1) - 1).natAbs = j + 3 := by
        have h : Int.negSucc (j + 1) - 1 = Int.negSucc (j + 2) := by omega
        rw [h]
        exact_mod_cast (Int.natAbs_of_nonneg (show (0 : ℤ) ≤ j + 3 by omega))
      rw [h0, h1, h2]
      change RWRS.walkOp G (carne_chebApply G f (j + 2)) v =
        (carne_chebApply G f (j + 1) v +
          carne_chebApply G f (j + 1 + 2) v) / 2
      simp only [carne_chebApply]
      ring_nf

/-- A reindexing lemma for the expansion below: a sum of `p k • q (k + 1)`
over `Icc (-n) n` equals the shifted sum of `p (k - 1) • q k` over the
enlarged range `Icc (-(n+1)) (n+1)`, since `p` vanishes below `-n`. -/
theorem carne_sum_shift_add_one {V : Type*} (n : ℕ) (p : ℤ → ℝ)
    (q : ℤ → V → ℝ) (hp : ∀ k, k < -(n : ℤ) → p k = 0) :
    (∑ k ∈ Finset.Icc (-(n : ℤ)) (n : ℤ), p k • q (k + 1)) =
      ∑ k ∈ Finset.Icc (-((n + 1 : ℕ) : ℤ)) ((n + 1 : ℕ) : ℤ),
        p (k - 1) • q k := by
  have hmap :
      (∑ k ∈ Finset.Icc (-(n : ℤ)) (n : ℤ), p k • q (k + 1)) =
        ∑ k ∈ Finset.Icc (-(n : ℤ) + 1) ((n : ℤ) + 1),
          p (k - 1) • q k := by
    refine Finset.sum_nbij' (i := fun k : ℤ => k + 1)
      (j := fun k : ℤ => k - 1) ?_ ?_ ?_ ?_ ?_
    · intro k hk
      rw [Finset.mem_Icc] at hk ⊢
      omega
    · intro k hk
      rw [Finset.mem_Icc] at hk ⊢
      omega
    · intro k hk
      rw [Finset.mem_Icc] at hk
      omega
    · intro k hk
      rw [Finset.mem_Icc] at hk
      omega
    · intro k hk
      have hk' : k + 1 - 1 = k := by omega
      rw [hk']
  have hsub :
      Finset.Icc (-(n : ℤ) + 1) ((n : ℤ) + 1) ⊆
        Finset.Icc (-((n + 1 : ℕ) : ℤ)) ((n + 1 : ℕ) : ℤ) := by
    intro k hk
    rw [Finset.mem_Icc] at hk ⊢
    push_cast at *
    omega
  have hext :
      (∑ k ∈ Finset.Icc (-(n : ℤ) + 1) ((n : ℤ) + 1),
        p (k - 1) • q k) =
        ∑ k ∈ Finset.Icc (-((n + 1 : ℕ) : ℤ)) ((n + 1 : ℕ) : ℤ),
          p (k - 1) • q k := by
    refine (Finset.sum_subset (s₁ := Finset.Icc (-(n : ℤ) + 1) ((n : ℤ) + 1))
      (s₂ := Finset.Icc (-((n + 1 : ℕ) : ℤ)) ((n + 1 : ℕ) : ℤ))
      (f := fun k : ℤ => p (k - 1) • q k) hsub ?_)
    intro k hk hnot
    rw [Finset.mem_Icc] at hk hnot
    have hk' : k = -(n : ℤ) - 1 ∨ k = -(n : ℤ) := by
      push_cast at *
      omega
    rcases hk' with rfl | rfl
    · rw [hp _ (by omega), zero_smul]
    · rw [hp _ (by omega), zero_smul]
  exact hmap.trans hext

/-- The mirror of `carne_sum_shift_add_one` for `q (k - 1)`: a sum over
`Icc (-n) n` equals the shifted sum of `p (k + 1) • q k` over
`Icc (-(n+1)) (n+1)`, since `p` vanishes above `n`. -/
theorem carne_sum_shift_sub_one {V : Type*} (n : ℕ) (p : ℤ → ℝ)
    (q : ℤ → V → ℝ) (hp : ∀ k, (n : ℤ) < k → p k = 0) :
    (∑ k ∈ Finset.Icc (-(n : ℤ)) (n : ℤ), p k • q (k - 1)) =
      ∑ k ∈ Finset.Icc (-((n + 1 : ℕ) : ℤ)) ((n + 1 : ℕ) : ℤ),
        p (k + 1) • q k := by
  have hmap :
      (∑ k ∈ Finset.Icc (-(n : ℤ)) (n : ℤ), p k • q (k - 1)) =
        ∑ k ∈ Finset.Icc ((-(n : ℤ)) - 1) ((n : ℤ) - 1),
          p (k + 1) • q k := by
    refine Finset.sum_nbij' (i := fun k : ℤ => k - 1)
      (j := fun k : ℤ => k + 1) ?_ ?_ ?_ ?_ ?_
    · intro k hk
      rw [Finset.mem_Icc] at hk ⊢
      omega
    · intro k hk
      rw [Finset.mem_Icc] at hk ⊢
      omega
    · intro k hk
      rw [Finset.mem_Icc] at hk
      omega
    · intro k hk
      rw [Finset.mem_Icc] at hk
      omega
    · intro k hk
      have hk' : k - 1 + 1 = k := by omega
      rw [hk']
  have hsub :
      Finset.Icc ((-(n : ℤ)) - 1) ((n : ℤ) - 1) ⊆
        Finset.Icc (-((n + 1 : ℕ) : ℤ)) ((n + 1 : ℕ) : ℤ) := by
    intro k hk
    rw [Finset.mem_Icc] at hk ⊢
    push_cast at *
    omega
  have hext :
      (∑ k ∈ Finset.Icc ((-(n : ℤ)) - 1) ((n : ℤ) - 1),
        p (k + 1) • q k) =
        ∑ k ∈ Finset.Icc (-((n + 1 : ℕ) : ℤ)) ((n + 1 : ℕ) : ℤ),
          p (k + 1) • q k := by
    refine (Finset.sum_subset
      (s₁ := Finset.Icc ((-(n : ℤ)) - 1) ((n : ℤ) - 1))
      (s₂ := Finset.Icc (-((n + 1 : ℕ) : ℤ)) ((n + 1 : ℕ) : ℤ))
      (f := fun k : ℤ => p (k + 1) • q k) hsub ?_)
    intro k hk hnot
    rw [Finset.mem_Icc] at hk hnot
    have hk' : k = (n : ℤ) ∨ k = (n : ℤ) + 1 := by
      push_cast at *
      omega
    rcases hk' with rfl | rfl
    · rw [hp _ (by omega), zero_smul]
    · rw [hp _ (by omega), zero_smul]
  exact hmap.trans hext

/-- The `n`-step simple random walk's mass at a site `k` is zero once `k`
falls below `-n`, since the walk cannot travel farther than `n` steps. -/
theorem carne_srwHeat_left_zero (n : ℕ) {k : ℤ} (hk : k < -(n : ℤ)) :
    LatticeProb.srwHeat 1 n ![k] = 0 := by
  apply LatticeProb.srwHeat_one_eq_zero_of_abs_gt
  rw [abs_of_neg (by omega)]
  omega

/-- The mirror of `carne_srwHeat_left_zero`: the `n`-step simple random
walk's mass at a site `k` is zero once `k` exceeds `n`. -/
theorem carne_srwHeat_right_zero (n : ℕ) {k : ℤ} (hk : (n : ℤ) < k) :
    LatticeProb.srwHeat 1 n ![k] = 0 := by
  apply LatticeProb.srwHeat_one_eq_zero_of_abs_gt
  rw [abs_of_nonneg (by omega)]
  exact hk

/-- **The Carne–Varopoulos expansion of the `n`-step walk operator.** The
`n`-fold iterate `(walkOp G)^[n] f` equals the sum, over `k` in `Icc (-n) n`,
of the simple random walk's `n`-step mass at `k` weighted against
`carne_chebApply G f |k|`; proved by induction on `n` using the three-term
recurrence `carne_walkOp_cheb_signed` and the shift lemmas above. -/
theorem carne_cheb_signed_expansion {V : Type*} {G : SimpleGraph V}
    [G.LocallyFinite] (f : V → ℝ) (n : ℕ) :
    (RWRS.walkOp G)^[n] f =
      ∑ k ∈ Finset.Icc (-(n : ℤ)) (n : ℤ),
        LatticeProb.srwHeat 1 n ![k] •
          carne_chebApply G f k.natAbs := by
  induction n with
  | zero =>
      funext v
      simp only [Function.iterate_zero_apply, Nat.cast_zero, neg_zero]
      rw [show Finset.Icc (0 : ℤ) 0 = {0} by decide, Finset.sum_singleton]
      simp [LatticeProb.srwHeat_zero, carne_chebApply]
  | succ n ih =>
      funext v
      rw [Function.iterate_succ_apply', ih]
      let S : Finset ℤ := Finset.Icc (-(n : ℤ)) (n : ℤ)
      let p : ℤ → ℝ := fun k => LatticeProb.srwHeat 1 n ![k]
      let q : ℤ → V → ℝ := fun k => carne_chebApply G f k.natAbs
      have hlin :
          RWRS.walkOp G (∑ k ∈ S, p k • q k) =
            ∑ k ∈ S, p k • RWRS.walkOp G (q k) := by
        change carne_walkOpLinear G (∑ k ∈ S, p k • q k) = _
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro k hk
        rw [map_smul]
        rfl
      have hstep :
          (∑ k ∈ S, p k • RWRS.walkOp G (q k)) =
            ∑ k ∈ S, p k • ((q (k + 1) + q (k - 1)) / 2) := by
        apply Finset.sum_congr rfl
        intro k hk
        exact congrArg (fun h : V → ℝ => p k • h)
          (carne_walkOp_cheb_signed f k)
      have hsplit :
          (∑ k ∈ S, p k • ((q (k + 1) + q (k - 1)) / 2)) =
            ((1 : ℝ) / 2) • (∑ k ∈ S, p k • q (k + 1)) +
              ((1 : ℝ) / 2) • (∑ k ∈ S, p k • q (k - 1)) := by
        funext w
        simp only [Finset.sum_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
        change (∑ k ∈ S, p k *
            ((q (k + 1) w + q (k - 1) w) / (2 : ℝ))) =
          (1 / 2) * (∑ k ∈ S, p k * q (k + 1) w) +
            (1 / 2) * (∑ k ∈ S, p k * q (k - 1) w)
        calc
          _ = ∑ k ∈ S, (p k * q (k + 1) w / 2 +
              p k * q (k - 1) w / 2) := by
            apply Finset.sum_congr rfl
            intro k hk
            ring_nf
          _ = (∑ k ∈ S, p k * q (k + 1) w / 2) +
              ∑ k ∈ S, p k * q (k - 1) w / 2 := by
            rw [Finset.sum_add_distrib]
          _ = _ := by
            rw [← Finset.sum_div, ← Finset.sum_div]
            ring_nf
      have hleft := carne_sum_shift_add_one n p q
        (fun k hk => by exact carne_srwHeat_left_zero n hk)
      have hright := carne_sum_shift_sub_one n p q
        (fun k hk => by exact carne_srwHeat_right_zero n hk)
      rw [hlin, hstep, hsplit, hleft, hright]
      simp only [Finset.sum_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      rw [LatticeProb.srwHeat_one_succ]
      ring

/-- **The pointwise coefficient bound.** The degree-weighted `k`-step
Chebyshev image of the point mass at `x`, evaluated at `y`, is bounded by
`sqrt(deg(x) deg(y))`: either it vanishes by `carne_chebApply_delta_zero_of_dist_lt`,
or `carne_cheb_delta_sq_le` gives it via a single-term domination of the sum. -/
theorem carne_cheb_delta_coeff_le {V : Type*} {G : SimpleGraph V}
    [G.LocallyFinite] (hG : G.Connected) (hdeg : ∀ v : V, 0 < G.degree v)
    (x y : V) (k : ℕ) :
    |(G.degree y : ℝ) *
        carne_chebApply G (fun z => if z = x then 1 else 0) k y| ≤
      Real.sqrt ((G.degree x : ℝ) * G.degree y) := by
  by_cases hdist : k < G.dist x y
  · rw [carne_chebApply_delta_zero_of_dist_lt hG x y k hdist]
    simp
    positivity
  · have hyB : y ∈ LatticeProb.Graph.ballFinset G x (4 * k + 4) := by
      apply LatticeProb.Graph.mem_ballFinset_of_dist_le hG
      omega
    have hsum := carne_cheb_delta_sq_le hG hdeg x k
    have hterm :
        (G.degree y : ℝ) *
            (carne_chebApply G (fun z => if z = x then 1 else 0) k y) ^ 2 ≤
          (G.degree x : ℝ) := by
      calc
        _ ≤ ∑ z ∈ LatticeProb.Graph.ballFinset G x (4 * k + 4),
            (G.degree z : ℝ) *
              (carne_chebApply G (fun z => if z = x then 1 else 0) k z) ^ 2 := by
          exact Finset.single_le_sum
            (f := fun z => (G.degree z : ℝ) *
              (carne_chebApply G (fun z => if z = x then 1 else 0) k z) ^ 2)
            (fun z hz => mul_nonneg (by positivity) (sq_nonneg _)) hyB
        _ ≤ _ := hsum
    have hdy : (0 : ℝ) ≤ G.degree y := by exact_mod_cast (hdeg y).le
    have hsq :
        ((G.degree y : ℝ) *
            carne_chebApply G (fun z => if z = x then 1 else 0) k y) ^ 2 ≤
          (G.degree x : ℝ) * G.degree y := by
      calc
        _ = (G.degree y : ℝ) *
            ((G.degree y : ℝ) *
              (carne_chebApply G (fun z => if z = x then 1 else 0) k y) ^ 2) := by
          ring_nf
        _ ≤ (G.degree y : ℝ) * G.degree x :=
          mul_le_mul_of_nonneg_left hterm hdy
        _ = (G.degree x : ℝ) * G.degree y := by ring_nf
    exact Real.abs_le_sqrt hsq

/-- **A Chernoff-type Gaussian tail bound for the simple random walk.** The
one-sided tail mass beyond `D` after `n` steps is at most
`exp(-D² / (2n))`, obtained by exponential tilting and the moment-generating
function bound `cosh θ ≤ exp(θ² / 2)`. -/
theorem carne_srw_positive_tail (n D : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ Finset.Icc (D : ℤ) (n : ℤ), LatticeProb.srwHeat 1 n ![k] ≤
      Real.exp (-((D : ℝ) ^ 2) / (2 * n)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set θ : ℝ := (D : ℝ) / n with hθ
  have hθ0 : 0 ≤ θ := div_nonneg (by positivity) hn0.le
  have hchernoff :
      (∑ k ∈ Finset.Icc (D : ℤ) (n : ℤ), LatticeProb.srwHeat 1 n ![k]) ≤
        Real.exp (-(θ * (D : ℝ))) *
          LatticeProb.srwSum n (fun a => Real.exp (θ * a)) := by
    have hsub : Finset.Icc (D : ℤ) (n : ℤ) ⊆
        Finset.Icc (-(n : ℤ)) (n : ℤ) := by
      intro k hk
      rw [Finset.mem_Icc] at hk ⊢
      omega
    have hterm : ∀ k ∈ Finset.Icc (D : ℤ) (n : ℤ),
        LatticeProb.srwHeat 1 n ![k] ≤
          LatticeProb.srwHeat 1 n ![k] *
            Real.exp (θ * ((k : ℝ) - (D : ℝ))) := by
      intro k hk
      rw [Finset.mem_Icc] at hk
      have he : (1 : ℝ) ≤ Real.exp (θ * ((k : ℝ) - (D : ℝ))) := by
        apply Real.one_le_exp
        have hk' : (D : ℝ) ≤ k := by exact_mod_cast hk.1
        exact mul_nonneg hθ0 (sub_nonneg.mpr hk')
      calc
        LatticeProb.srwHeat 1 n ![k] =
            LatticeProb.srwHeat 1 n ![k] * 1 := by ring_nf
        _ ≤ _ := mul_le_mul_of_nonneg_left he
          (LatticeProb.srwHeat_nonneg n ![k])
    have hsum := Finset.sum_le_sum hterm
    have hbox :
        Real.exp (-(θ * (D : ℝ))) *
            LatticeProb.srwSum n (fun a => Real.exp (θ * a)) =
          ∑ k ∈ Finset.Icc (-(n : ℤ)) (n : ℤ),
            LatticeProb.srwHeat 1 n ![k] *
              Real.exp (θ * ((k : ℝ) - (D : ℝ))) := by
      rw [LatticeProb.srwSum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [← mul_assoc, mul_comm (Real.exp (-(θ * (D : ℝ)))),
        mul_assoc, ← Real.exp_add]
      congr 1
      ring_nf
    calc
      _ ≤ ∑ k ∈ Finset.Icc (D : ℤ) (n : ℤ),
          LatticeProb.srwHeat 1 n ![k] *
            Real.exp (θ * ((k : ℝ) - (D : ℝ))) := hsum
      _ ≤ ∑ k ∈ Finset.Icc (-(n : ℤ)) (n : ℤ),
          LatticeProb.srwHeat 1 n ![k] *
            Real.exp (θ * ((k : ℝ) - (D : ℝ))) := by
        exact Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun k hk _ => mul_nonneg (LatticeProb.srwHeat_nonneg n ![k])
            (Real.exp_nonneg _))
      _ = _ := hbox.symm
  have hmgf :
      LatticeProb.srwSum n (fun a => Real.exp (θ * a)) ≤
        Real.exp ((n : ℝ) * θ ^ 2 / 2) := by
    rw [LatticeProb.srwSum_exp]
    calc
      Real.cosh θ ^ n ≤ Real.exp (θ ^ 2 / 2) ^ n :=
        pow_le_pow_left₀ (le_of_lt (Real.cosh_pos θ))
          (Real.cosh_le_exp_half_sq θ) n
      _ = Real.exp ((n : ℝ) * θ ^ 2 / 2) := by
        rw [← Real.exp_nat_mul]
        ring_nf
  have hfinal :
      Real.exp (-(θ * (D : ℝ))) *
          Real.exp ((n : ℝ) * θ ^ 2 / 2) =
        Real.exp (-((D : ℝ) ^ 2) / (2 * n)) := by
    rw [← Real.exp_add]
    congr 1
    have hnne : (n : ℝ) ≠ 0 := ne_of_gt hn0
    rw [hθ]
    field_simp
    ring_nf
  calc
    _ ≤ Real.exp (-(θ * (D : ℝ))) *
        LatticeProb.srwSum n (fun a => Real.exp (θ * a)) := hchernoff
    _ ≤ Real.exp (-(θ * (D : ℝ))) *
        Real.exp ((n : ℝ) * θ ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left hmgf (Real.exp_nonneg _)
    _ = _ := hfinal

/-- The `n`-step simple random walk's mass is symmetric: `srwHeat` at `-k`
equals `srwHeat` at `k`, by induction on `n` using the reflection symmetry of
the one-step recursion. -/
theorem carne_srwHeat_neg (n : ℕ) (k : ℤ) :
    LatticeProb.srwHeat 1 n ![-k] = LatticeProb.srwHeat 1 n ![k] := by
  induction n generalizing k with
  | zero =>
      by_cases hk : k = 0
      · subst k
        simp [LatticeProb.srwHeat_zero]
      · have hnk : -k ≠ 0 := by omega
        simp [LatticeProb.srwHeat_zero, hk, hnk]
  | succ n ih =>
      rw [LatticeProb.srwHeat_one_succ, LatticeProb.srwHeat_one_succ]
      have h1 : (![(-k - 1)] : LatticeProb.Site 1) = ![-(k + 1)] := by
        funext i
        fin_cases i
        ring_nf
      have h2 : (![(-k + 1)] : LatticeProb.Site 1) = ![-(k - 1)] := by
        funext i
        fin_cases i
        ring_nf
      rw [h1, h2, ih (k + 1), ih (k - 1)]
      ring_nf

/-- **The two-sided tail bound.** The mass of the `n`-step simple random walk
at sites of absolute value at least `D` is at most `2 exp(-D² / (2n))`,
combining `carne_srw_positive_tail` with the reflection symmetry
`carne_srwHeat_neg` on the negative side. -/
theorem carne_srw_two_sided_tail (n D : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ (Finset.Icc (-(n : ℤ)) (n : ℤ)).filter
        (fun k => (D : ℤ) ≤ |k|), LatticeProb.srwHeat 1 n ![k] ≤
      2 * Real.exp (-((D : ℝ) ^ 2) / (2 * n)) := by
  by_cases hD : D = 0
  · subst D
    have hmass :
        ∑ k ∈ Finset.Icc (-(n : ℤ)) (n : ℤ), LatticeProb.srwHeat 1 n ![k] = 1 := by
      have hs := LatticeProb.srwSum_exp 0 n
      rw [LatticeProb.srwSum] at hs
      simpa using hs
    have hfilter :
        (Finset.Icc (-(n : ℤ)) (n : ℤ)).filter
            (fun k => (0 : ℤ) ≤ |k|) = Finset.Icc (-(n : ℤ)) (n : ℤ) := by
      ext k
      simp
    simp only [Nat.cast_zero]
    rw [hfilter, hmass]
    norm_num
  · have hDpos : 0 < D := Nat.pos_of_ne_zero hD
    let P : Finset ℤ := Finset.Icc (D : ℤ) (n : ℤ)
    let N : Finset ℤ := Finset.Icc (-(n : ℤ)) (-(D : ℤ))
    let T : Finset ℤ := (Finset.Icc (-(n : ℤ)) (n : ℤ)).filter
      (fun k => (D : ℤ) ≤ |k|)
    have hTN : T ⊆ P ∪ N := by
      intro k hk
      rw [Finset.mem_filter, Finset.mem_Icc] at hk
      rcases le_total 0 k with hk0 | hk0
      · apply Finset.mem_union_left
        rw [Finset.mem_Icc]
        rw [abs_of_nonneg hk0] at hk
        exact ⟨hk.2, hk.1.2⟩
      · apply Finset.mem_union_right
        rw [Finset.mem_Icc]
        exact ⟨hk.1.1, by
          rw [abs_of_nonpos hk0] at hk
          omega⟩
    have hdisj : Disjoint P N := by
      rw [Finset.disjoint_left]
      intro k hkP hkN
      rw [Finset.mem_Icc] at hkP hkN
      omega
    have hneg :
        (∑ k ∈ N, LatticeProb.srwHeat 1 n ![k]) =
          ∑ k ∈ P, LatticeProb.srwHeat 1 n ![k] := by
      refine Finset.sum_nbij' (i := fun k : ℤ => -k) (j := fun k : ℤ => -k)
        ?_ ?_ ?_ ?_ ?_
      · intro k hk
        rw [Finset.mem_Icc] at hk ⊢
        omega
      · intro k hk
        rw [Finset.mem_Icc] at hk ⊢
        omega
      · intro k hk
        omega
      · intro k hk
        omega
      · intro k hk
        have h := carne_srwHeat_neg n k
        simpa using h.symm
    have hP := carne_srw_positive_tail n D hn
    have hTNsum :
        (∑ k ∈ T, LatticeProb.srwHeat 1 n ![k]) ≤
          ∑ k ∈ P ∪ N, LatticeProb.srwHeat 1 n ![k] :=
      Finset.sum_le_sum_of_subset_of_nonneg hTN
        (fun k hk _ => LatticeProb.srwHeat_nonneg n ![k])
    rw [Finset.sum_union hdisj, hneg] at hTNsum
    linarith

/-- **The pointwise Carne–Varopoulos heat kernel bound.** Assembling the
signed expansion `carne_cheb_signed_expansion`, the coefficient bound
`carne_cheb_delta_coeff_le`, and the two-sided Gaussian tail
`carne_srw_two_sided_tail`: `heat G n x y ≤ 2 sqrt(deg(y)/deg(x))
exp(-dist(x,y)² / (2n))`. -/
theorem carne_heat_bound {V : Type*} {G : SimpleGraph V}
    [G.LocallyFinite] (hG : G.Connected) (hdeg : ∀ v : V, 0 < G.degree v)
    (x y : V) (n : ℕ) (hn : 1 ≤ n) :
    RWRS.heat G n x y ≤
      2 * Real.sqrt ((G.degree y : ℝ) / G.degree x) *
        Real.exp (-((G.dist x y : ℝ) ^ 2) / (2 * n)) := by
  let δ : V → ℝ := fun z => if z = x then 1 else 0
  let S : Finset ℤ := Finset.Icc (-(n : ℤ)) (n : ℤ)
  let T : Finset ℤ := S.filter (fun k => (G.dist x y : ℤ) ≤ |k|)
  let a : ℝ := Real.sqrt ((G.degree x : ℝ) * G.degree y)
  have hseries : RWRS.heat G n y x =
      ∑ k ∈ S, LatticeProb.srwHeat 1 n ![k] *
        carne_chebApply G δ k.natAbs y := by
    have hiter := RWRS.Support.walkOp_iterate_single (G := G) x 1 n y
    have hex := congrFun (carne_cheb_signed_expansion (G := G) δ n) y
    calc
      RWRS.heat G n y x = (RWRS.walkOp G)^[n] δ y := by
        simpa [δ] using hiter.symm
      _ = ∑ k ∈ S, LatticeProb.srwHeat 1 n ![k] *
          carne_chebApply G δ k.natAbs y := by
        simpa [S, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hex
  have hzero : ∀ k : ℤ, ¬ (G.dist x y : ℤ) ≤ |k| →
      carne_chebApply G δ k.natAbs y = 0 := by
    intro k hk
    apply carne_chebApply_delta_zero_of_dist_lt hG x y k.natAbs
    have hk' : |k| < (G.dist x y : ℤ) := by omega
    have hk'' : (k.natAbs : ℤ) < (G.dist x y : ℤ) := by
      rw [Int.natCast_natAbs]
      exact hk'
    exact_mod_cast hk''
  have hsum_abs :
      ∑ k ∈ S, |LatticeProb.srwHeat 1 n ![k] *
          ((G.degree y : ℝ) * carne_chebApply G δ k.natAbs y)| ≤
        ∑ k ∈ S, if (G.dist x y : ℤ) ≤ |k| then
          a * LatticeProb.srwHeat 1 n ![k] else 0 := by
    apply Finset.sum_le_sum
    intro k hk
    by_cases hgood : (G.dist x y : ℤ) ≤ |k|
    · simp only [if_pos hgood]
      rw [abs_mul, abs_of_nonneg (LatticeProb.srwHeat_nonneg n ![k])]
      calc
        LatticeProb.srwHeat 1 n ![k] *
              |(G.degree y : ℝ) * carne_chebApply G δ k.natAbs y| ≤
            LatticeProb.srwHeat 1 n ![k] * a :=
          mul_le_mul_of_nonneg_left
            (carne_cheb_delta_coeff_le hG hdeg x y k.natAbs)
            (LatticeProb.srwHeat_nonneg n ![k])
        _ = a * LatticeProb.srwHeat 1 n ![k] := by ring_nf
    · simp only [if_neg hgood]
      simp [hzero k hgood]
  have hfilter :
      (∑ k ∈ S, if (G.dist x y : ℤ) ≤ |k| then
          a * LatticeProb.srwHeat 1 n ![k] else 0) =
        a * ∑ k ∈ T, LatticeProb.srwHeat 1 n ![k] := by
    rw [Finset.sum_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hk' : (G.dist x y : ℤ) ≤ |k| <;> simp [hk']
  have htail := carne_srw_two_sided_tail n (G.dist x y) hn
  have hinner_series :
      (G.degree y : ℝ) * RWRS.heat G n y x =
        ∑ k ∈ S, LatticeProb.srwHeat 1 n ![k] *
          ((G.degree y : ℝ) * carne_chebApply G δ k.natAbs y) := by
    rw [hseries, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring_nf
  have habs :
      |(G.degree y : ℝ) * RWRS.heat G n y x| ≤
        a * (2 * Real.exp (-((G.dist x y : ℝ) ^ 2) / (2 * n))) := by
    calc
      |(G.degree y : ℝ) * RWRS.heat G n y x| =
          |∑ k ∈ S, LatticeProb.srwHeat 1 n ![k] *
            ((G.degree y : ℝ) * carne_chebApply G δ k.natAbs y)| := by
            rw [hinner_series]
      _ ≤ ∑ k ∈ S, |LatticeProb.srwHeat 1 n ![k] *
          ((G.degree y : ℝ) * carne_chebApply G δ k.natAbs y)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ S, if (G.dist x y : ℤ) ≤ |k| then
          a * LatticeProb.srwHeat 1 n ![k] else 0 := hsum_abs
      _ = a * ∑ k ∈ T, LatticeProb.srwHeat 1 n ![k] := hfilter
      _ ≤ a * (2 * Real.exp (-((G.dist x y : ℝ) ^ 2) / (2 * n))) := by
        exact mul_le_mul_of_nonneg_left htail (Real.sqrt_nonneg _)
  have hinner_nonneg :
      0 ≤ (G.degree y : ℝ) * RWRS.heat G n y x := by
    exact mul_nonneg (by positivity) (RWRS.Support.heat_nonneg n y x)
  have hprod :
      (G.degree x : ℝ) * RWRS.heat G n x y ≤
        a * (2 * Real.exp (-((G.dist x y : ℝ) ^ 2) / (2 * n))) := by
    rw [RWRS.Support.heat_reversible]
    rw [abs_of_nonneg hinner_nonneg] at habs
    exact habs
  have hdx : (0 : ℝ) < G.degree x := by exact_mod_cast hdeg x
  have hsqrt :
      a / G.degree x = Real.sqrt ((G.degree y : ℝ) / G.degree x) := by
    dsimp [a]
    rw [Real.sqrt_mul hdx.le, Real.sqrt_div (by positivity)]
    have hsx : 0 < Real.sqrt (G.degree x : ℝ) := Real.sqrt_pos.2 hdx
    have hsx2 : Real.sqrt (G.degree x : ℝ) ^ 2 = G.degree x :=
      Real.sq_sqrt hdx.le
    field_simp [ne_of_gt hdx, ne_of_gt hsx]
    rw [hsx2]
    ring_nf
  calc
    RWRS.heat G n x y ≤
        (a * (2 * Real.exp (-((G.dist x y : ℝ) ^ 2) / (2 * n)))) /
          G.degree x := by
      apply (le_div_iff₀ hdx).2
      nlinarith [hprod]
    _ = 2 * Real.sqrt ((G.degree y : ℝ) / G.degree x) *
        Real.exp (-((G.dist x y : ℝ) ^ 2) / (2 * n)) := by
      rw [← hsqrt]
      ring_nf

end RWRS.External

-- FROZEN-STATEMENT-BEGIN
/-- The pointwise Carne-Varopoulos bound, proved rather than assumed. -/
theorem RWRS.External.carneVaropoulos {V : Type*} (G : SimpleGraph V) [G.LocallyFinite]
    [MeasurableSpace V] : RWRS.External.CarneVaropoulos G
-- FROZEN-STATEMENT-END
:= by
  intro hmeas hnontriv hG x y n hn
  classical
  let hdeg : ∀ v : V, 0 < G.degree v := by
    intro v
    rw [SimpleGraph.degree_pos_iff_exists_adj]
    obtain ⟨u, hu⟩ := exists_ne v
    obtain ⟨p⟩ := hG.preconnected v u
    rcases p with _ | ⟨hadj, q⟩
    · exact absurd rfl hu
    · exact ⟨_, hadj⟩
  have hheat := carne_heat_bound hG hdeg x y n hn
  rw [carne_walkLaw_eq_heat hG x y n]
  exact ENNReal.ofReal_le_ofReal hheat
