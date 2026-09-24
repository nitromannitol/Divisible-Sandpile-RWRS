/-
Pointwise Gaussian transition estimates and first exits from a rooted ball.
-/
import RWRS.Support.SubPolyExit
import RWRS.Support.DTExitAux

namespace RWRS.Support

open MeasureTheory
open scoped ENNReal

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

omit [G.LocallyFinite] in
/-- Membership in a closed graph ball in terms of the natural distance. -/
theorem mem_closedBall_iff_dist_le (hG : G.Connected) (o v : V) (R : ℕ) :
    v ∈ RWRS.closedBall G o R ↔ G.dist o v ≤ R := by
  change G.edist v o ≤ (R : ℕ∞) ↔ _
  rw [← (hG.preconnected v o).coe_dist_eq_edist, ENat.coe_le_coe, SimpleGraph.dist_comm]

omit [G.LocallyFinite] in
/-- A nearest-neighbour path first exits a ball on its outer sphere. -/
theorem exists_exit_sphere (hG : G.Connected) {o : V} {X : ℕ → V}
    (hstart : X 0 = o) (hstep : ∀ k, G.Adj (X k) (X (k + 1))) {R N : ℕ}
    (hexit : RWRS.exitTime (RWRS.closedBall G o R) X ≤ (N : ℕ∞)) :
    ∃ k ∈ Finset.Icc 1 N, G.dist o (X k) = R + 1 := by
  classical
  rw [exitTime_eq_lib] at hexit
  have hne : LatticeProb.Graph.exitTime (RWRS.closedBall G o R) X ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) hexit
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hne
  have hkN : k ≤ N := by
    rw [← hk, ENat.coe_le_coe] at hexit
    exact hexit
  have hnot : X k ∉ RWRS.closedBall G o R := by
    simpa only [← hk, ENat.toNat_coe] using
      exitTime_notMem_at (RWRS.closedBall G o R) X hne
  have hfar : R < G.dist o (X k) := by
    simpa only [mem_closedBall_iff_dist_le hG, not_le] using hnot
  have hk1 : 1 ≤ k := by
    by_contra h
    have : k = 0 := by omega
    simp [this, hstart] at hfar
  have hprev : G.dist o (X (k - 1)) ≤ R := by
    apply (mem_closedBall_iff_dist_le hG _ _ _).1
    apply mem_of_lt_exitTime
    rw [← hk, ENat.coe_lt_coe]
    omega
  have hadj : G.Adj (X (k - 1)) (X k) := by
    simpa only [Nat.sub_add_cancel hk1] using hstep (k - 1)
  have htri : G.dist o (X k) ≤ G.dist o (X (k - 1)) + 1 := by
    have := hG.dist_triangle (u := o) (v := X (k - 1)) (w := X k)
    rwa [SimpleGraph.dist_eq_one_iff_adj.2 hadj] at this
  exact ⟨k, Finset.mem_Icc.2 ⟨hk1, hkN⟩, by omega⟩

variable [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]

/-- Almost every trajectory starts at its origin and takes adjacent steps. -/
theorem ae_walk_start_adj (hdeg : ∀ v : V, 0 < G.degree v) (o : V) :
    ∀ᵐ X ∂(RWRS.walkLaw G o), X 0 = o ∧ ∀ k, G.Adj (X k) (X (k + 1)) := by
  have hm (k : ℕ) : MeasurableSet {X : ℕ → V | G.Adj (X k) (X (k + 1))} := by
    change MeasurableSet ((fun X : ℕ → V => (X k, X (k + 1))) ⁻¹'
      {p : V × V | G.Adj p.1 p.2})
    exact ((measurable_pi_apply k).prodMk (measurable_pi_apply (k + 1)))
      (Set.to_countable {p : V × V | G.Adj p.1 p.2}).measurableSet
  have hmeas : MeasurableSet {X : ℕ → V | X 0 = o ∧ ∀ k, G.Adj (X k) (X (k + 1))} := by
    simp only [Set.setOf_and, Set.setOf_forall]
    exact (measurableSet_eq_fun (measurable_pi_apply 0) measurable_const).inter
      (MeasurableSet.iInter hm)
  rw [walkLaw_eq_lib o, LatticeProb.Graph.walkLaw, MeasureTheory.ae_map_iff
    (LatticeProb.Graph.measurable_walkPath (G := G) o).aemeasurable hmeas]
  filter_upwards [ae_driverLaw_mem_Ico] with ω hω
  constructor
  · rfl
  · intro k
    simp only [← walkPath_eq_lib]
    exact adj_stepTo (hdeg _) (hω k).1 (hω k).2

/-- The first-exit union bound from pointwise Gaussian transition probabilities
and polynomial volume growth at the starting vertex. -/
theorem walkLaw_exit_le_of_pointwise (hG : G.Connected)
    (hdeg : ∀ v : V, 0 < G.degree v) (d : ℕ) (hbd : RWRS.BoundedDegree G d)
    (o : V) {C_vol d_f : ℝ} (hC : 0 ≤ C_vol)
    (hvol : RWRS.VolumeGrowthUpper G o C_vol d_f)
    (hpoint : ∀ (y : V) (n : ℕ), 1 ≤ n →
      RWRS.walkLaw G o {X : ℕ → V | X n = y} ≤
        ENNReal.ofReal (2 * Real.sqrt ((G.degree y : ℝ) / G.degree o) *
          Real.exp (-((G.dist o y : ℝ) ^ 2) / (2 * n))))
    (R N : ℕ) :
    RWRS.walkLaw G o {X : ℕ → V |
        RWRS.exitTime (RWRS.closedBall G o R) X ≤ (N : ℕ∞)} ≤
      ENNReal.ofReal (2 * Real.sqrt (d : ℝ) * C_vol * N * ((R : ℝ) + 1) ^ d_f *
        Real.exp (-((R : ℝ) ^ 2) / (2 * N))) := by
  classical
  let B := (finite_closedBall (G := G) o (R + 1)).toFinset
  let S := B.filter (fun y => G.dist o y = R + 1)
  have hS (y : V) : y ∈ S ↔ G.dist o y = R + 1 := by
    simp only [S, B, Finset.mem_filter, Set.Finite.mem_toFinset,
      mem_closedBall_iff_dist_le hG]
    omega
  let K : ℝ := 2 * Real.sqrt (d : ℝ) * Real.exp (-((R : ℝ) ^ 2) / (2 * N))
  have hcover : RWRS.walkLaw G o {X : ℕ → V |
        RWRS.exitTime (RWRS.closedBall G o R) X ≤ (N : ℕ∞)} ≤
      RWRS.walkLaw G o (⋃ k ∈ Finset.Icc 1 N, ⋃ y ∈ S, {X : ℕ → V | X k = y}) := by
    apply measure_mono_ae
    filter_upwards [ae_walk_start_adj hdeg o] with X hX
    intro hexit
    obtain ⟨k, hk, hy⟩ := exists_exit_sphere hG hX.1 hX.2 hexit
    exact Set.mem_iUnion.2 ⟨k, Set.mem_iUnion.2 ⟨hk,
      Set.mem_iUnion.2 ⟨X k, Set.mem_iUnion.2 ⟨(hS _).2 hy, rfl⟩⟩⟩⟩
  have hterm : ∀ k ∈ Finset.Icc 1 N, ∀ y ∈ S,
      RWRS.walkLaw G o {X : ℕ → V | X k = y} ≤ ENNReal.ofReal K := by
    intro k hk y hy
    obtain ⟨hk1, hkN⟩ := Finset.mem_Icc.1 hk
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
    have hkN' : (k : ℝ) ≤ N := by exact_mod_cast hkN
    have hdeg1 : (1 : ℝ) ≤ G.degree o := by exact_mod_cast hdeg o
    have hratio : (G.degree y : ℝ) / G.degree o ≤ d :=
      (div_le_self (Nat.cast_nonneg _) hdeg1).trans (by exact_mod_cast hbd y)
    have hdist : (R : ℝ) ^ 2 ≤ (G.dist o y : ℝ) ^ 2 := by
      rw [(hS y).1 hy]
      push_cast
      nlinarith [Nat.cast_nonneg (α := ℝ) R]
    have hexp : Real.exp (-((G.dist o y : ℝ) ^ 2) / (2 * k)) ≤
        Real.exp (-((R : ℝ) ^ 2) / (2 * N)) := by
      apply Real.exp_le_exp.2
      have hdiv := div_le_div₀ (sq_nonneg (G.dist o y : ℝ)) hdist
        (by positivity : (0 : ℝ) < 2 * k) (by linarith : (2 : ℝ) * k ≤ 2 * N)
      simpa only [neg_div] using neg_le_neg hdiv
    refine (hpoint y k hk1).trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hratio) (by norm_num))
      hexp (Real.exp_nonneg _) (by positivity)
  have hcard : (S.card : ℝ≥0∞) ≤ ENNReal.ofReal (C_vol * ((R : ℝ) + 1) ^ d_f) := by
    have hcardB : S.card ≤ B.card := Finset.card_le_card (Finset.filter_subset _ _)
    have hball := hvol (R + 1) (by omega)
    rw [(finite_closedBall (G := G) o (R + 1)).encard_eq_coe_toFinset_card] at hball
    push_cast at hball
    exact (by exact_mod_cast hcardB : (S.card : ℝ≥0∞) ≤ B.card).trans hball
  calc RWRS.walkLaw G o {X : ℕ → V |
        RWRS.exitTime (RWRS.closedBall G o R) X ≤ (N : ℕ∞)}
      ≤ RWRS.walkLaw G o (⋃ k ∈ Finset.Icc 1 N, ⋃ y ∈ S, {X : ℕ → V | X k = y}) := hcover
    _ ≤ ∑ k ∈ Finset.Icc 1 N, RWRS.walkLaw G o (⋃ y ∈ S, {X : ℕ → V | X k = y}) :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ k ∈ Finset.Icc 1 N, ∑ y ∈ S, RWRS.walkLaw G o {X : ℕ → V | X k = y} :=
      Finset.sum_le_sum fun k _ => measure_biUnion_finset_le _ _
    _ ≤ ∑ _k ∈ Finset.Icc 1 N, ∑ _y ∈ S, ENNReal.ofReal K :=
      Finset.sum_le_sum fun k hk => Finset.sum_le_sum fun y hy => hterm k hk y hy
    _ = (N : ℝ≥0∞) * (S.card : ℝ≥0∞) * ENNReal.ofReal K := by
      simp [Nat.card_Icc, nsmul_eq_mul, mul_assoc]
    _ ≤ (N : ℝ≥0∞) * ENNReal.ofReal (C_vol * ((R : ℝ) + 1) ^ d_f) * ENNReal.ofReal K :=
      mul_le_mul' (mul_le_mul' le_rfl hcard) le_rfl
    _ = ENNReal.ofReal (2 * Real.sqrt (d : ℝ) * C_vol * N * ((R : ℝ) + 1) ^ d_f *
        Real.exp (-((R : ℝ) ^ 2) / (2 * N))) := by
      rw [← ENNReal.ofReal_natCast N, ← ENNReal.ofReal_mul (Nat.cast_nonneg N),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      dsimp [K]
      ring

omit [G.LocallyFinite] [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] in
/-- Polynomial prefactors are absorbed above the diffusive scale. -/
theorem exists_polyR_gaussian_bound {d_f s : ℝ} (hdf : 0 ≤ d_f) (hs : 0 < s) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      (N : ℝ) * ((polyR 2 s N : ℝ) + 1) ^ d_f *
          Real.exp (-((polyR 2 s N : ℝ) ^ 2) / (2 * N)) ≤
        C * Real.exp (-((N : ℝ) ^ (2 * s)) / 4) := by
  obtain ⟨C0, hC00, hC0⟩ := rpow_mul_exp_neg_le
    (A := 1 + (1 / 2 + s) * d_f) (c := 1 / 4) (θ := 2 * s)
    (by norm_num) (by positivity)
  refine ⟨(3 : ℝ) ^ d_f * (C0 + 1), by positivity, fun N hN => ?_⟩
  have hx1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hx0 : (0 : ℝ) < N := by linarith
  have he : (0 : ℝ) ≤ 1 / 2 + s := by linarith
  have hp1 := one_le_rpow_natCast he hN
  have hRup : (polyR 2 s N : ℝ) + 1 ≤ 3 * (N : ℝ) ^ (1 / 2 + s) := by
    have := polyR_le (d_w := 2) (s := s) (by norm_num) hs hN
    linarith
  have hRlo : (N : ℝ) ^ (1 / 2 + s) ≤ (polyR 2 s N : ℝ) := Nat.le_ceil _
  have hsquare : ((N : ℝ) ^ (1 / 2 + s)) ^ 2 = (N : ℝ) * (N : ℝ) ^ (2 * s) := by
    rw [← Real.rpow_natCast ((N : ℝ) ^ (1 / 2 + s)) 2,
      ← Real.rpow_mul hx0.le]
    have heq : (1 / 2 + s) * (2 : ℕ) = 1 + 2 * s := by norm_num; ring
    rw [heq, Real.rpow_add hx0, Real.rpow_one]
  have hsquare_le : (N : ℝ) * (N : ℝ) ^ (2 * s) ≤ (polyR 2 s N : ℝ) ^ 2 := by
    rw [← hsquare]
    exact pow_le_pow_left₀ (Real.rpow_nonneg hx0.le _) hRlo 2
  have hE : Real.exp (-((polyR 2 s N : ℝ) ^ 2) / (2 * N)) ≤
      Real.exp (-((N : ℝ) ^ (2 * s)) / 2) := by
    apply Real.exp_le_exp.2
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * N) (by norm_num : (0 : ℝ) < 2)]
    nlinarith only [hsquare_le]
  have hP : (N : ℝ) * ((polyR 2 s N : ℝ) + 1) ^ d_f ≤
      (3 : ℝ) ^ d_f * (N : ℝ) ^ (1 + (1 / 2 + s) * d_f) := by
    have hpow := Real.rpow_le_rpow (by positivity) hRup hdf
    rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hx0.le _),
      ← Real.rpow_mul hx0.le] at hpow
    rw [Real.rpow_add hx0, Real.rpow_one]
    nlinarith [mul_le_mul_of_nonneg_left hpow hx0.le]
  have habsorb : (N : ℝ) ^ (1 + (1 / 2 + s) * d_f) *
      Real.exp (-((N : ℝ) ^ (2 * s)) / 4) ≤ C0 + 1 := by
    have h := hC0 (N : ℝ) hx1
    have hsmall := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by norm_num : (-1 : ℝ) ≤ 0)
    have hm : C0 * (N : ℝ) ^ (-1 : ℝ) ≤ C0 := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hsmall hC00
    have heq : -((1 / 4 : ℝ) * (N : ℝ) ^ (2 * s)) = -((N : ℝ) ^ (2 * s)) / 4 := by ring
    rw [heq] at h
    linarith
  have hsplit : Real.exp (-((N : ℝ) ^ (2 * s)) / 2) =
      Real.exp (-((N : ℝ) ^ (2 * s)) / 4) *
        Real.exp (-((N : ℝ) ^ (2 * s)) / 4) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc (N : ℝ) * ((polyR 2 s N : ℝ) + 1) ^ d_f *
          Real.exp (-((polyR 2 s N : ℝ) ^ 2) / (2 * N))
      ≤ ((3 : ℝ) ^ d_f * (N : ℝ) ^ (1 + (1 / 2 + s) * d_f)) *
          Real.exp (-((N : ℝ) ^ (2 * s)) / 2) :=
        mul_le_mul hP hE (Real.exp_nonneg _) (by positivity)
    _ = (3 : ℝ) ^ d_f * ((N : ℝ) ^ (1 + (1 / 2 + s) * d_f) *
          Real.exp (-((N : ℝ) ^ (2 * s)) / 4)) *
          Real.exp (-((N : ℝ) ^ (2 * s)) / 4) := by rw [hsplit]; ring
    _ ≤ (3 : ℝ) ^ d_f * (C0 + 1) * Real.exp (-((N : ℝ) ^ (2 * s)) / 4) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left habsorb (Real.rpow_nonneg (by norm_num) _))
        (Real.exp_nonneg _)


/-- Pointwise Gaussian transitions and rooted volume growth supply exit control
at every polynomial radius strictly above the diffusive scale. -/
theorem polynomialExitBoundAt_of_pointwise (hG : G.Connected)
    (hdeg : ∀ v : V, 0 < G.degree v) (d : ℕ) (hbd : RWRS.BoundedDegree G d)
    (o : V) {C_vol d_f : ℝ} (hC : 0 ≤ C_vol) (hdf : 0 ≤ d_f)
    (hvol : RWRS.VolumeGrowthUpper G o C_vol d_f)
    (hpoint : ∀ (y : V) (n : ℕ), 1 ≤ n →
      RWRS.walkLaw G o {X : ℕ → V | X n = y} ≤
        ENNReal.ofReal (2 * Real.sqrt ((G.degree y : ℝ) / G.degree o) *
          Real.exp (-((G.dist o y : ℝ) ^ 2) / (2 * n)))) :
    PolynomialExitBoundAt G o 2 := by
  intro s hs
  obtain ⟨C, hC0, hCbound⟩ := exists_polyR_gaussian_bound hdf hs
  let A : ℝ := 2 * Real.sqrt (d : ℝ) * C_vol
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨A * C + 1, 1 / 4, by positivity, by norm_num, fun N hN => ?_⟩
  refine (walkLaw_exit_le_of_pointwise hG hdeg d hbd o hC hvol hpoint (polyR 2 s N) N).trans
    (ENNReal.ofReal_le_ofReal ?_)
  have h := mul_le_mul_of_nonneg_left (hCbound N hN) hA
  have he : s * 2 / (2 - 1) = 2 * s := by ring
  rw [he]
  have hexp : -(1 / 4 * (N : ℝ) ^ (2 * s)) = -((N : ℝ) ^ (2 * s)) / 4 := by ring
  rw [hexp]
  calc 2 * Real.sqrt (d : ℝ) * C_vol * N * ((polyR 2 s N : ℝ) + 1) ^ d_f *
        Real.exp (-((polyR 2 s N : ℝ) ^ 2) / (2 * N))
      = A * ((N : ℝ) * ((polyR 2 s N : ℝ) + 1) ^ d_f *
        Real.exp (-((polyR 2 s N : ℝ) ^ 2) / (2 * N))) := by dsimp [A]; ring
    _ ≤ A * (C * Real.exp (-((N : ℝ) ^ (2 * s)) / 4)) := h
    _ ≤ (A * C + 1) * Real.exp (-((N : ℝ) ^ (2 * s)) / 4) := by
      nlinarith [Real.exp_pos (-((N : ℝ) ^ (2 * s)) / 4)]


end RWRS.Support
