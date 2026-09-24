/-
Step 1 of `prop:poly-growth`: the scenery event has positive probability.

`rwrs.tex:1267` bounds the tail masses above the levels by Markov's inequality
and sums them over the vertices by partial summation against the volume growth.
Here the sum is grouped along the DYADIC shells instead: a vertex at distance
between `2^i` and `2^{i+1}` carries a level at least `2^{iβ}`, and there are at
most `C_vol 2^{(i+1)d_f}` such vertices, so the shell contributes
`C_vol 2^{(i+1)d_f} E[(ξ^+)^p] 2^{-iβp}`, and the series is geometric because
`βp > d_f`.  Splitting the level as a geometric mean of `M_0` and of the shell
radius keeps the whole series geometric while leaving a factor `M_0^{-p(1-λ)}`
in front, which is then made small.
-/
import RWRS.Support.SubPolyExp

namespace RWRS.Support

open MeasureTheory
open scoped ENNReal

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

omit [G.LocallyFinite] in
/-- The dyadic shell of a vertex sits inside the ball of twice its radius. -/
theorem fiber_subset_closedBall (hG : G.Connected) (o : V) (i : ℕ) :
    (fun v : V => Nat.log 2 ((G.edist v o).toNat)) ⁻¹' {i}
      ⊆ RWRS.closedBall G o (2 ^ (i + 1)) := by
  intro v hv
  have hi : Nat.log 2 ((G.edist v o).toNat) = i := hv
  have hne : G.edist v o ≠ ⊤ := SimpleGraph.edist_ne_top_iff_reachable.2 (hG.preconnected v o)
  have hlt : (G.edist v o).toNat < 2 ^ (i + 1) := by
    have hstep := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) ((G.edist v o).toNat)
    rw [hi] at hstep
    exact hstep
  have hcast : (((G.edist v o).toNat : ℕ) : ℕ∞) = G.edist v o := ENat.coe_toNat hne
  show G.edist v o ≤ ((2 ^ (i + 1) : ℕ) : ℕ∞)
  rw [← hcast]
  exact_mod_cast hlt.le

omit [G.LocallyFinite] in
/-- Inside a dyadic shell the level is at least the level of the inner radius. -/
theorem shellLevel_le_polyLevel {M0 β : ℝ} (hM0 : 1 ≤ M0) (hβ : 0 ≤ β) (o : V) {i : ℕ} {v : V}
    (hv : Nat.log 2 ((G.edist v o).toNat) = i) :
    max M0 ((2:ℝ) ^ ((i : ℝ) * β)) ≤ polyLevel G o M0 β v := by
  rcases Nat.eq_zero_or_pos i with hi | hi
  · subst hi
    have h0 : (2:ℝ) ^ (((0:ℕ) : ℝ) * β) = 1 := by norm_num
    rw [h0, max_eq_left hM0]
    exact le_polyLevel G o M0 β v
  · have hn0 : (G.edist v o).toNat ≠ 0 := by
      intro h
      rw [h] at hv
      simp only [Nat.log_zero_right] at hv
      omega
    have hpow : 2 ^ i ≤ (G.edist v o).toNat := by
      have hstep := Nat.pow_log_le_self 2 hn0
      rw [hv] at hstep
      exact hstep
    have hcast : ((2:ℝ) ^ (i : ℝ)) ≤ (((G.edist v o).toNat : ℕ) : ℝ) := by
      rw [Real.rpow_natCast]
      exact_mod_cast hpow
    have hsplit : (2:ℝ) ^ ((i : ℝ) * β) = ((2:ℝ) ^ (i : ℝ)) ^ β :=
      Real.rpow_mul (by norm_num) _ _
    rw [hsplit, polyLevel]
    refine max_le_max le_rfl ?_
    exact Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num) _) hcast hβ

/-- A geometric mean is below the maximum. -/
theorem rpow_mul_rpow_le_max {A B lam : ℝ} (hA : 0 < A) (hB : 0 < B) (h0 : 0 ≤ lam)
    (h1 : lam ≤ 1) : A ^ (1 - lam) * B ^ lam ≤ max A B := by
  have hmax0 : (0:ℝ) < max A B := lt_of_lt_of_le hA (le_max_left A B)
  have h2 : A ^ (1 - lam) ≤ (max A B) ^ (1 - lam) :=
    Real.rpow_le_rpow hA.le (le_max_left A B) (by linarith)
  have h3 : B ^ lam ≤ (max A B) ^ lam := Real.rpow_le_rpow hB.le (le_max_right A B) h0
  have h4 : (max A B) ^ (1 - lam) * (max A B) ^ lam = max A B := by
    rw [← Real.rpow_add hmax0]
    norm_num
  calc A ^ (1 - lam) * B ^ lam
      ≤ (max A B) ^ (1 - lam) * (max A B) ^ lam :=
        mul_le_mul h2 h3 (Real.rpow_nonneg hB.le lam) (Real.rpow_nonneg hmax0.le _)
    _ = max A B := h4

/-- Markov's inequality with the moment given as a real bound. -/
theorem meas_Ioi_le_ofReal (ν : Measure ℝ) {Q s p : ℝ}
    (hQ : RWRS.posMoment ν p ≤ ENNReal.ofReal Q) (hs : 0 < s) (hp : 0 < p) :
    ν (Set.Ioi s) ≤ ENNReal.ofReal (Q / s ^ p) := by
  have hsp : (0:ℝ) < s ^ p := Real.rpow_pos_of_pos hs p
  refine le_trans (meas_Ioi_le_posMoment ν hs hp) ?_
  refine le_trans (ENNReal.div_le_div_right hQ _) ?_
  rw [← ENNReal.ofReal_div_of_pos hsp]

/-- The geometric series of the shell bounds. -/
theorem tsum_ofReal_geom (D r : ℝ) (hD : 0 ≤ D) (hr0 : 0 ≤ r) (hr : r < 1) :
    ∑' i : ℕ, ENNReal.ofReal (D * r ^ i) = ENNReal.ofReal (D / (1 - r)) := by
  have hsum : Summable (fun i : ℕ => D * r ^ i) :=
    (summable_geometric_of_lt_one hr0 hr).mul_left D
  have hnn : ∀ i : ℕ, 0 ≤ D * r ^ i := fun i => by positivity
  rw [← ENNReal.ofReal_tsum_of_nonneg hnn hsum]
  congr 1
  rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr]
  ring

omit [G.LocallyFinite] in
/-- The scenery event fails only if some coordinate exceeds its level. -/
theorem meas_forall_le_compl_le [Countable V] [MeasurableSpace V] (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (t : V → ℝ) :
    RWRS.iidLaw V ν {ξ : V → ℝ | ∀ v, ξ v ≤ t v}ᶜ ≤ ∑' v : V, ν (Set.Ioi (t v)) := by
  have hcompl : {ξ : V → ℝ | ∀ v, ξ v ≤ t v}ᶜ
      = ⋃ v : V, {ξ : V → ℝ | ξ v ∈ Set.Ioi (t v)} := by
    ext ξ
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_Ioi, not_forall,
      not_le]
  rw [hcompl]
  refine le_trans (MeasureTheory.measure_iUnion_le _) ?_
  exact ENNReal.tsum_le_tsum fun v => le_of_eq (meas_coord v measurableSet_Ioi)

omit [G.LocallyFinite] in
/-- **Step 1 of `prop:poly-growth`**: the tail masses above the levels sum to as
little as one likes, once the level `M_0` is large enough. -/
theorem exists_polyLevel_tsum_le [Countable V] (hG : G.Connected) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] {C_vol d_f : ℝ} (hCvol : 0 ≤ C_vol) (hdf : 0 < d_f)
    (o : V) (hH1 : RWRS.VolumeGrowthUpper G o C_vol d_f)
    {p β : ℝ} (hp : 0 < p) (hβ : 0 < β) (hβp : d_f < β * p)
    (hmom : RWRS.posMoment ν p ≠ ⊤) {ε : ℝ} (hε : 0 < ε) :
    ∃ M0 : ℝ, 1 ≤ M0 ∧
      (∑' v : V, ν (Set.Ioi (polyLevel G o M0 β v))) ≤ ENNReal.ofReal ε := by
  classical
  have hX : (0:ℝ) < 2 := by norm_num
  set Q : ℝ := (RWRS.posMoment ν p).toReal with hQdef
  have hQ0 : (0:ℝ) ≤ Q := ENNReal.toReal_nonneg
  have hQeq : RWRS.posMoment ν p = ENNReal.ofReal Q := (ENNReal.ofReal_toReal hmom).symm
  have hbp0 : (0:ℝ) < β * p := by positivity
  set lam : ℝ := (d_f + β * p) / (2 * (β * p)) with hlamdef
  have hlam0 : (0:ℝ) < lam := by rw [hlamdef]; positivity
  have hlam1 : lam < 1 := by
    rw [hlamdef, div_lt_one (by positivity)]
    linarith
  have hlamp : d_f < lam * (β * p) := by
    have hval : lam * (β * p) = (d_f + β * p) / 2 := by
      rw [hlamdef]
      field_simp
    rw [hval]
    linarith
  set E : ℝ := p * (1 - lam) with hEdef
  have hE0 : (0:ℝ) < E := by rw [hEdef]; nlinarith
  set r : ℝ := (2:ℝ) ^ (d_f - lam * (β * p)) with hrdef
  have hr0 : (0:ℝ) < r := Real.rpow_pos_of_pos hX _
  have hr1 : r < 1 := by
    rw [hrdef]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have h1r : (0:ℝ) < 1 - r := by linarith
  have hnum : (0:ℝ) ≤ C_vol * (2:ℝ) ^ d_f * Q := by positivity
  set W : ℝ := C_vol * (2:ℝ) ^ d_f * Q / (ε * (1 - r)) + 1 with hWdef
  have hW0 : (0:ℝ) < W := by
    have hq : (0:ℝ) ≤ C_vol * (2:ℝ) ^ d_f * Q / (ε * (1 - r)) := by positivity
    rw [hWdef]
    linarith
  set M0 : ℝ := max 1 (W ^ (1 / E)) with hM0def
  have hM01 : (1:ℝ) ≤ M0 := le_max_left _ _
  have hM00 : (0:ℝ) < M0 := lt_of_lt_of_le zero_lt_one hM01
  have hM0E0 : (0:ℝ) < M0 ^ E := Real.rpow_pos_of_pos hM00 E
  have hM0E : W ≤ M0 ^ E := by
    have h1 : W ^ (1 / E) ≤ M0 := le_max_right _ _
    have h2 : (W ^ (1 / E)) ^ E ≤ M0 ^ E :=
      Real.rpow_le_rpow (Real.rpow_nonneg hW0.le _) h1 hE0.le
    rwa [← Real.rpow_mul hW0.le, one_div, inv_mul_cancel₀ (ne_of_gt hE0), Real.rpow_one] at h2
  set D : ℝ := C_vol * (2:ℝ) ^ d_f * Q / M0 ^ E with hDdef
  have hD0 : (0:ℝ) ≤ D := by rw [hDdef]; positivity
  refine ⟨M0, hM01, ?_⟩
  have hg : ∀ v : V, ν (Set.Ioi (polyLevel G o M0 β v))
      ≤ ENNReal.ofReal (Q / (M0 ^ E
          * (2:ℝ) ^ ((Nat.log 2 ((G.edist v o).toNat) : ℝ) * (β * p * lam)))) := by
    intro v
    set i : ℕ := Nat.log 2 ((G.edist v o).toNat) with hidef
    have hlev : max M0 ((2:ℝ) ^ ((i : ℝ) * β)) ≤ polyLevel G o M0 β v :=
      shellLevel_le_polyLevel hM01 hβ.le o rfl
    have hLpos : (0:ℝ) < max M0 ((2:ℝ) ^ ((i : ℝ) * β)) :=
      lt_of_lt_of_le hM00 (le_max_left _ _)
    have hPpos : (0:ℝ) < polyLevel G o M0 β v := lt_of_lt_of_le hLpos hlev
    have hmk : ν (Set.Ioi (polyLevel G o M0 β v))
        ≤ ENNReal.ofReal (Q / (polyLevel G o M0 β v) ^ p) :=
      meas_Ioi_le_ofReal ν (le_of_eq hQeq) hPpos hp
    have hA : M0 ^ (1 - lam) * ((2:ℝ) ^ ((i : ℝ) * β)) ^ lam
        ≤ max M0 ((2:ℝ) ^ ((i : ℝ) * β)) :=
      rpow_mul_rpow_le_max hM00 (Real.rpow_pos_of_pos hX _) hlam0.le hlam1.le
    have hBle : (M0 ^ (1 - lam) * ((2:ℝ) ^ ((i : ℝ) * β)) ^ lam) ^ p
        ≤ (polyLevel G o M0 β v) ^ p :=
      Real.rpow_le_rpow (by positivity) (le_trans hA hlev) hp.le
    have h2 : ((2:ℝ) ^ ((i : ℝ) * β)) ^ lam = (2:ℝ) ^ ((i : ℝ) * β * lam) :=
      (Real.rpow_mul hX.le _ _).symm
    have hexp1 : (1 - lam) * p = E := by rw [hEdef]; ring
    have hexp2 : (i : ℝ) * β * lam * p = (i : ℝ) * (β * p * lam) := by ring
    have hC : (M0 ^ (1 - lam) * ((2:ℝ) ^ ((i : ℝ) * β)) ^ lam) ^ p
        = M0 ^ E * (2:ℝ) ^ ((i : ℝ) * (β * p * lam)) := by
      rw [h2, Real.mul_rpow (Real.rpow_nonneg hM00.le _) (Real.rpow_nonneg hX.le _),
        ← Real.rpow_mul hM00.le, ← Real.rpow_mul hX.le, hexp1, hexp2]
    rw [hC] at hBle
    refine le_trans hmk (ENNReal.ofReal_le_ofReal ?_)
    exact div_le_div_of_nonneg_left hQ0 (by positivity) hBle
  have hcard : ∀ i : ℕ,
      ((((fun v : V => Nat.log 2 ((G.edist v o).toNat)) ⁻¹' {i}).encard : ℕ∞) : ℝ≥0∞)
        ≤ ENNReal.ofReal (C_vol * ((2:ℝ) ^ (i + 1)) ^ d_f) := by
    intro i
    have h1 : ((((fun v : V => Nat.log 2 ((G.edist v o).toNat)) ⁻¹' {i}).encard : ℕ∞) : ℝ≥0∞)
        ≤ (((RWRS.closedBall G o (2 ^ (i + 1))).encard : ℕ∞) : ℝ≥0∞) := by
      exact_mod_cast Set.encard_mono (fiber_subset_closedBall hG o i)
    refine le_trans h1 ?_
    have h2 := hH1 (2 ^ (i + 1)) Nat.one_le_two_pow
    refine le_trans h2 (le_of_eq ?_)
    congr 2
    push_cast
    ring
  have hmain := tsum_le_fiber_card (fun v : V => ν (Set.Ioi (polyLevel G o M0 β v)))
    (fun v : V => Nat.log 2 ((G.edist v o).toNat))
    (fun i : ℕ => ENNReal.ofReal (Q / (M0 ^ E * (2:ℝ) ^ ((i : ℝ) * (β * p * lam)))))
    (fun i : ℕ => ENNReal.ofReal (C_vol * ((2:ℝ) ^ (i + 1)) ^ d_f)) hg hcard
  have hterm : ∀ i : ℕ,
      ENNReal.ofReal (C_vol * ((2:ℝ) ^ (i + 1)) ^ d_f)
          * ENNReal.ofReal (Q / (M0 ^ E * (2:ℝ) ^ ((i : ℝ) * (β * p * lam))))
        = ENNReal.ofReal (D * r ^ i) := by
    intro i
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have e1 : ((2:ℝ) ^ (i + 1)) ^ d_f = (2:ℝ) ^ (((i : ℝ) + 1) * d_f) := by
      rw [← Real.rpow_natCast (2:ℝ) (i + 1), ← Real.rpow_mul hX.le]
      push_cast
      ring_nf
    have e2 : r ^ i = (2:ℝ) ^ ((i : ℝ) * (d_f - lam * (β * p))) := by
      rw [hrdef, ← Real.rpow_natCast ((2:ℝ) ^ (d_f - lam * (β * p))) i, ← Real.rpow_mul hX.le]
      ring_nf
    have hB0 : (0:ℝ) < (2:ℝ) ^ ((i : ℝ) * (β * p * lam)) := Real.rpow_pos_of_pos hX _
    have key : (2:ℝ) ^ (((i : ℝ) + 1) * d_f) / (2:ℝ) ^ ((i : ℝ) * (β * p * lam))
        = (2:ℝ) ^ d_f * (2:ℝ) ^ ((i : ℝ) * (d_f - lam * (β * p))) := by
      rw [← Real.rpow_sub hX, ← Real.rpow_add hX]
      congr 1
      ring
    calc C_vol * ((2:ℝ) ^ (i + 1)) ^ d_f
          * (Q / (M0 ^ E * (2:ℝ) ^ ((i : ℝ) * (β * p * lam))))
        = (C_vol * Q / M0 ^ E)
            * ((2:ℝ) ^ (((i : ℝ) + 1) * d_f) / (2:ℝ) ^ ((i : ℝ) * (β * p * lam))) := by
          rw [e1]
          field_simp
      _ = (C_vol * Q / M0 ^ E)
            * ((2:ℝ) ^ d_f * (2:ℝ) ^ ((i : ℝ) * (d_f - lam * (β * p)))) := by rw [key]
      _ = D * r ^ i := by
          rw [e2, hDdef]
          field_simp
  have hsum : ∑' i : ℕ, ENNReal.ofReal (C_vol * ((2:ℝ) ^ (i + 1)) ^ d_f)
        * ENNReal.ofReal (Q / (M0 ^ E * (2:ℝ) ^ ((i : ℝ) * (β * p * lam))))
      = ENNReal.ofReal (D / (1 - r)) := by
    rw [tsum_congr hterm]
    exact tsum_ofReal_geom D r hD0 hr0.le hr1
  rw [hsum] at hmain
  refine le_trans hmain (ENNReal.ofReal_le_ofReal ?_)
  have h1 : D ≤ C_vol * (2:ℝ) ^ d_f * Q / W := by
    rw [hDdef]
    exact div_le_div_of_nonneg_left hnum hW0 hM0E
  have h2 : C_vol * (2:ℝ) ^ d_f * Q / W < ε * (1 - r) := by
    rw [div_lt_iff₀ hW0]
    have h3 : C_vol * (2:ℝ) ^ d_f * Q / (ε * (1 - r)) < W := by
      rw [hWdef]
      linarith
    rw [div_lt_iff₀ (by positivity : (0:ℝ) < ε * (1 - r))] at h3
    linarith
  have hDlt : D < ε * (1 - r) := lt_of_le_of_lt h1 h2
  rw [div_le_iff₀ h1r]
  linarith

end RWRS.Support
