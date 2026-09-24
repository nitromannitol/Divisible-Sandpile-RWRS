/-
The assembly of `prop:poly-growth`.

`rwrs.tex:1300-1346`: the block moments of Steps 4 and 5 are summed over the
scales.  At the `k`-th scale the good-walk contribution is a polynomial in the
block length `N = 2^{k+1}` against `exp(-cN^{d_s/2-δ-β/d_w})`, the displacement
contribution a polynomial against `exp(-c_{\mathrm{disp}}N^{sd_w/(d_w-1)})`, and
the local-time contribution a polynomial against `N^{d_s/2-r\delta}` with `r`
chosen large; each is below a constant multiple of `2^{-k}`, so the series
converges and the running supremum of the payoff of the recentred field has a
finite joint mean.
-/
import RWRS.Support.SubPolyGeom
import RWRS.Support.GreenUnique

namespace RWRS.Support

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

/-- A moment of a lower order is finite too. -/
theorem absMoment_ne_top_of_le (ρ : Measure ℝ) [IsProbabilityMeasure ρ] {p q : ℝ}
    (hq : 0 ≤ q) (hqp : q ≤ p) (h : RWRS.absMoment ρ p ≠ ⊤) : RWRS.absMoment ρ q ≠ ⊤ := by
  have hpt : ∀ z : ℝ, ENNReal.ofReal (|z| ^ q) ≤ 1 + ENNReal.ofReal (|z| ^ p) := by
    intro z
    rcases le_or_gt |z| 1 with h1 | h1
    · have hle : |z| ^ q ≤ 1 := Real.rpow_le_one (abs_nonneg z) h1 hq
      have : ENNReal.ofReal (|z| ^ q) ≤ 1 := by
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal hle
      exact le_trans this le_self_add
    · have hle : |z| ^ q ≤ |z| ^ p := Real.rpow_le_rpow_of_exponent_le h1.le hqp
      exact le_trans (ENNReal.ofReal_le_ofReal hle) le_add_self
  have hle : RWRS.absMoment ρ q ≤ ∫⁻ z, (1 + ENNReal.ofReal (|z| ^ p)) ∂ρ := by
    rw [RWRS.absMoment]
    exact lintegral_mono hpt
  have heq : (∫⁻ z, (1 + ENNReal.ofReal (|z| ^ p)) ∂ρ) = 1 + RWRS.absMoment ρ p := by
    rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
      RWRS.absMoment]
  rw [heq] at hle
  exact ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, h⟩) hle

/-- A power of a number above one is above one. -/
theorem one_le_rpow_of_one_le {x e : ℝ} (hx : 1 ≤ x) (he : 0 ≤ e) : (1:ℝ) ≤ x ^ e := by
  calc (1:ℝ) = (1:ℝ) ^ e := (Real.one_rpow e).symm
    _ ≤ x ^ e := Real.rpow_le_rpow (by norm_num) hx he

variable [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]

set_option maxHeartbeats 1600000 in
/-- **The `k`-th block moment of the recentred field is geometrically small in
the scale.** -/
theorem exists_block_bound_poly [Infinite V] (hG : G.Connected)
    (d : ℕ) (hbd : RWRS.BoundedDegree G d) (hdeg : ∀ v : V, 1 ≤ G.degree v) (hd : 0 < d)
    {d_s A : ℝ} (hds0 : 0 < d_s) (hds2 : d_s < 2) (hH2 : RWRS.SpectralDimensionBound G d_s A)
    {d_w : ℝ} (hdw : 2 ≤ d_w)
    (ρ : Measure ℝ) [IsProbabilityMeasure ρ] {m : ℝ} (hmeq : RWRS.extMean ρ = (m : EReal))
    (hm : m < 0) {p : ℝ} (hp1 : 1 ≤ p) (habs : RWRS.absMoment ρ p ≠ ⊤)
    (o : V) (hExit : PolynomialExitBoundAt G o d_w) {M M0 β δ Cm p2 : ℝ} (hM : 0 ≤ M) (hM0 : 1 ≤ M0)
    (hβ0 : 0 < β) (hβdw : β / d_w < d_s / 2) (hδ : δ = (d_s / 2 - β / d_w) / 2)
    (hp2a : 1 ≤ p2) (hp2b : p2 ≤ 2) (hCm : 0 ≤ Cm)
    (hvarbd : ∀ v : V, (∫ z, (siteShift ρ M m (polyLevel G o M0 β v) z - m) ^ 2 ∂ρ)
        ≤ (polyLevel G o M0 β v + M) ^ (2 - p2) * Cm) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ,
      (∫⁻ z, ENNReal.ofReal
          (RWRS.dyadicY G (zetaField ρ M m (polyLevel G o M0 β) z.1) m d k z.2)
          ∂(RWRS.jointLaw G ρ o)) ≤ ENNReal.ofReal (C * (1 / 2 : ℝ) ^ k) := by
  have hdw0 : (0:ℝ) < d_w := by linarith
  have hdw1 : (0:ℝ) < d_w - 1 := by linarith
  have hδ0 : (0:ℝ) < δ := by rw [hδ]; linarith
  set α : ℝ := max (1 - d_s / 2) 0 with hα
  have hαval : α = 1 - d_s / 2 := max_eq_left (by linarith)
  have hα0 : (0:ℝ) ≤ α := le_max_right _ _
  set s : ℝ := δ / (4 * (β + 1)) with hs
  have hs0 : (0:ℝ) < s := by rw [hs]; positivity
  obtain ⟨C_disp, c_disp, hCd, hcd, hExitBound⟩ := hExit s hs0
  set σ : ℝ := δ / 8 with hσ
  have hσ0 : (0:ℝ) < σ := by rw [hσ]; positivity
  set γ : ℝ := β * (1 / d_w + s) with hγ
  have hγ0 : (0:ℝ) ≤ γ := by rw [hγ]; positivity
  have hβs : β * s ≤ δ / 4 := by
    have hpos : (0:ℝ) < 4 * (β + 1) := by positivity
    have hrw : β * s = β * δ / (4 * (β + 1)) := by rw [hs]; ring
    rw [hrw, div_le_div_iff₀ hpos (by norm_num : (0:ℝ) < 4)]
    nlinarith [hβ0, hδ0]
  have hkey : δ / 2 ≤ 2 - 2 * σ - 1 - α - δ - γ := by
    rw [hαval, hγ, hσ]
    have hd2 : d_s / 2 - β / d_w = 2 * δ := by rw [hδ]; ring
    have hexp : β * (1 / d_w + s) = β / d_w + β * s := by
      field_simp
    rw [hexp]
    linarith [hβs, hd2]
  have hδ1 : δ < min (d_s / 2) 1 := by
    refine lt_min ?_ ?_
    · rw [hδ]
      have : (0:ℝ) < β / d_w := by positivity
      linarith
    · rw [hδ]
      linarith
  obtain ⟨Cσ, hCσ0, hCσ⟩ := succ_le_rpow hσ0
  set CL : ℝ := M0 + M + (2:ℝ) ^ β with hCL
  have hCL1 : (1:ℝ) ≤ CL := by
    have h2 : (0:ℝ) < (2:ℝ) ^ β := Real.rpow_pos_of_pos (by norm_num) β
    rw [hCL]
    linarith
  have hCL0 : (0:ℝ) < CL := lt_of_lt_of_le zero_lt_one hCL1
  set CB : ℝ := M0 + M + 1 with hCB
  have hCB1 : (1:ℝ) ≤ CB := by rw [hCB]; linarith
  have hCB0 : (0:ℝ) < CB := lt_of_lt_of_le zero_lt_one hCB1
  have hdR : (1:ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hmabs : (0:ℝ) < |m| := abs_pos.2 (ne_of_lt hm)
  -- the order of the local-time moment
  obtain ⟨r0, hr0⟩ := exists_nat_ge ((2 + β + d_s / 2) / δ)
  set r : ℕ := max r0 1 with hr
  have hr1 : 1 ≤ r := le_max_right _ _
  have hrδ : 2 + β + d_s / 2 ≤ (r : ℝ) * δ := by
    have h1 : ((r0 : ℕ) : ℝ) ≤ ((r : ℕ) : ℝ) := by exact_mod_cast le_max_left r0 1
    have h2 : (2 + β + d_s / 2) / δ ≤ ((r : ℕ) : ℝ) := le_trans hr0 h1
    rw [div_le_iff₀ hδ0] at h2
    linarith
  obtain ⟨Cr, hCr0, hCrb⟩ := (RWRS.Frozen.goodWalkBounds hG d hbd d_s A hds0 hH2 ρ
    inferInstance m hmeq hm p hp1 habs α δ hα hδ0 hδ1).1 r hr1
  -- the two geometric bounds
  set cw : ℝ := |m| / (2 * (d : ℝ) * Cσ) with hcw
  have hcw0 : (0:ℝ) < cw := by rw [hcw]; positivity
  set Cden : ℝ := CL * Cm + CL * |m| / 3 + 1 with hCden
  have hCden0 : (0:ℝ) < Cden := by rw [hCden]; positivity
  set cE : ℝ := cw ^ 2 / (2 * Cden) with hcE
  have hcE0 : (0:ℝ) < cE := by rw [hcE]; positivity
  obtain ⟨C1, hC10, hC1⟩ := exists_geom_bound (A := 3 + γ) (CB := 2 * CL) (c := cE)
    (θ := δ / 2) (by positivity) hcE0 (by positivity)
  obtain ⟨C2, hC20, hC2⟩ := exists_geom_bound (A := 1 + β) (CB := CB * C_disp) (c := c_disp)
    (θ := s * d_w / (d_w - 1)) (by positivity) hcd (div_pos (by positivity) hdw1)
  refine ⟨C1 + CB * Cr + C2, by positivity, fun k => ?_⟩
  set N : ℝ := (2 ^ (k + 1) : ℝ) with hN
  have hN1 : (1:ℝ) ≤ N := one_le_pow₀ (by norm_num)
  have hN0 : (0:ℝ) < N := lt_of_lt_of_le zero_lt_one hN1
  set Nn : ℕ := 2 ^ (k + 1) with hNn
  have hNn1 : 1 ≤ Nn := Nat.one_le_two_pow
  have hNcast : ((Nn : ℕ) : ℝ) = N := by rw [hNn, hN]; push_cast; ring
  set Rk : ℕ := polyR d_w s Nn with hRk
  have hblock := lintegral_dyadicY_polyLevel_le (G := G) (ρ := ρ) RWRS.External.bernstein hdeg
    hM hM0 hβ0.le hm hCm (by linarith : (0:ℝ) ≤ 2 - p2) hvarbd (k := k) (R := Rk) (α := α)
    (δ := δ) hd
  refine le_trans hblock ?_
  rw [← hN]
  -- the cap inside the ball
  have hL1 : (1:ℝ) ≤ polyCap M0 β M Rk := one_le_polyCap hM0 hM Rk
  have hNγ1 : (1:ℝ) ≤ N ^ γ := one_le_rpow_of_one_le hN1 hγ0
  have hNβ1 : (1:ℝ) ≤ N ^ β := one_le_rpow_of_one_le hN1 hβ0.le
  have hRle : ((Rk : ℕ) : ℝ) ≤ 2 * N ^ (1 / d_w + s) := by
    have hstep := polyR_le (d_w := d_w) (s := s) hdw hs0 hNn1
    rw [hNcast] at hstep
    exact hstep
  have hRβ : (((Rk : ℕ) : ℝ)) ^ β ≤ (2:ℝ) ^ β * N ^ γ := by
    have hpow : ((2:ℝ) * N ^ (1 / d_w + s)) ^ β = (2:ℝ) ^ β * N ^ γ := by
      rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hN0.le _), ← Real.rpow_mul hN0.le, hγ]
      congr 2
      ring
    calc (((Rk : ℕ) : ℝ)) ^ β ≤ ((2:ℝ) * N ^ (1 / d_w + s)) ^ β :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) hRle hβ0.le
      _ = (2:ℝ) ^ β * N ^ γ := hpow
  have hLbd : polyCap M0 β M Rk ≤ CL * N ^ γ := by
    have hRβ0 : (0:ℝ) ≤ (((Rk : ℕ) : ℝ)) ^ β := Real.rpow_nonneg (Nat.cast_nonneg _) β
    have h2β : (0:ℝ) < (2:ℝ) ^ β := Real.rpow_pos_of_pos (by norm_num) β
    have hmax : max M0 (((Rk : ℕ) : ℝ) ^ β) ≤ M0 + (((Rk : ℕ) : ℝ)) ^ β :=
      max_le (by linarith) (by linarith)
    have hstep : polyCap M0 β M Rk ≤ M0 + M + (2:ℝ) ^ β * N ^ γ := by
      rw [polyCap]
      linarith only [hRβ, hmax]
    refine le_trans hstep ?_
    have h0 : (0:ℝ) ≤ M0 + M := by linarith only [hM, hM0]
    have hkey2 : M0 + M ≤ (M0 + M) * N ^ γ := by
      calc M0 + M = (M0 + M) * 1 := (mul_one _).symm
        _ ≤ (M0 + M) * N ^ γ := mul_le_mul_of_nonneg_left hNγ1 h0
    have hexp2 : CL * N ^ γ = (M0 + M) * N ^ γ + (2:ℝ) ^ β * N ^ γ := by rw [hCL]; ring
    rw [hexp2]
    linarith only [hkey2]
  have hLcap0 : (0:ℝ) < polyCap M0 β M Rk := lt_of_lt_of_le zero_lt_one hL1
  have hk0 : (0:ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hk1pos : (0:ℝ) < (k : ℝ) + 1 := by linarith only [hk0]
  have hk1N : ((k : ℝ) + 1) ≤ N := by
    have h1 : k + 1 < 2 ^ (k + 1) := Nat.lt_two_pow_self
    have h2 : ((k + 1 : ℕ) : ℝ) ≤ ((2 ^ (k + 1) : ℕ) : ℝ) := by exact_mod_cast h1.le
    rw [hNcast] at h2
    push_cast at h2
    linarith only [h2]
  set w : ℝ := |m| / (d : ℝ) * 2 ^ k / ((k : ℝ) + 1) with hwdef
  have hw0 : (0:ℝ) < w := by rw [hwdef]; positivity
  have hweq : w = |m| * N / (2 * (d : ℝ) * ((k : ℝ) + 1)) := by
    rw [hwdef, hN]
    have h2 : ((2:ℝ)) ^ (k + 1) = 2 * 2 ^ k := by ring
    rw [h2]
    field_simp
  have hden1 : (1:ℝ) ≤ 2 * (d : ℝ) * ((k : ℝ) + 1) := by nlinarith only [hdR, hk0]
  have hwub : w ≤ |m| * N := by
    rw [hweq, div_le_iff₀ (by positivity)]
    have hstep := mul_le_mul_of_nonneg_left hden1 (le_of_lt (mul_pos hmabs hN0))
    rw [mul_one] at hstep
    linarith only [hstep]
  have hCσk : ((k : ℝ) + 1) ≤ Cσ * N ^ σ := by
    have hstep := hCσ k
    rw [← hN] at hstep
    exact hstep
  have hNσ0 : (0:ℝ) < N ^ σ := Real.rpow_pos_of_pos hN0 σ
  have hwlb : cw * N ^ (1 - σ) ≤ w := by
    have hd1 : (0:ℝ) < 2 * (d : ℝ) * ((k : ℝ) + 1) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hCσk (by positivity : (0:ℝ) ≤ 2 * (d : ℝ))
    have hstep : |m| * N / (2 * (d : ℝ) * (Cσ * N ^ σ)) ≤ w := by
      rw [hweq]
      exact div_le_div_of_nonneg_left (by positivity) hd1 (by linarith only [hmul])
    refine le_trans (le_of_eq ?_) hstep
    rw [hcw, Real.rpow_sub hN0, Real.rpow_one]
    field_simp
  set Mb : ℝ := N ^ (α + δ) * polyCap M0 β M Rk with hMbdef
  set Db : ℝ := (polyCap M0 β M Rk) ^ (2 - p2) * Cm * (N ^ (α + δ) * N) with hDbdef
  have hMb0 : (0:ℝ) < Mb := by
    rw [hMbdef]
    exact mul_pos (Real.rpow_pos_of_pos hN0 _) hLcap0
  have hDb0 : (0:ℝ) ≤ Db := by
    rw [hDbdef]
    have h1 : (0:ℝ) ≤ (polyCap M0 β M Rk) ^ (2 - p2) := Real.rpow_nonneg hLcap0.le _
    have h2 : (0:ℝ) ≤ N ^ (α + δ) * N := by positivity
    exact mul_nonneg (mul_nonneg h1 hCm) h2
  have hMbub : Mb ≤ CL * N ^ (α + δ + γ) := by
    rw [hMbdef]
    have h1 : N ^ (α + δ) * polyCap M0 β M Rk ≤ N ^ (α + δ) * (CL * N ^ γ) :=
      mul_le_mul_of_nonneg_left hLbd (Real.rpow_nonneg hN0.le _)
    refine le_trans h1 (le_of_eq ?_)
    have hid : N ^ (α + δ + γ) = N ^ (α + δ) * N ^ γ := Real.rpow_add hN0 (α + δ) γ
    rw [hid]
    ring
  have hDbub : Db ≤ CL * Cm * N ^ (1 + (α + δ + γ)) := by
    rw [hDbdef]
    have hcapexp : (polyCap M0 β M Rk) ^ (2 - p2) ≤ polyCap M0 β M Rk := by
      have h1 : (polyCap M0 β M Rk) ^ (2 - p2) ≤ (polyCap M0 β M Rk) ^ (1:ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hL1 (by linarith only [hp2a])
      rwa [Real.rpow_one] at h1
    have h2 : (polyCap M0 β M Rk) ^ (2 - p2) ≤ CL * N ^ γ := le_trans hcapexp hLbd
    have hnn : (0:ℝ) ≤ Cm * (N ^ (α + δ) * N) := by positivity
    have h3 : (polyCap M0 β M Rk) ^ (2 - p2) * (Cm * (N ^ (α + δ) * N))
        ≤ (CL * N ^ γ) * (Cm * (N ^ (α + δ) * N)) := mul_le_mul_of_nonneg_right h2 hnn
    have h4 : (polyCap M0 β M Rk) ^ (2 - p2) * Cm * (N ^ (α + δ) * N)
        = (polyCap M0 β M Rk) ^ (2 - p2) * (Cm * (N ^ (α + δ) * N)) := by ring
    rw [h4]
    refine le_trans h3 (le_of_eq ?_)
    have hid : N ^ (1 + (α + δ + γ)) = N ^ γ * (N ^ (α + δ) * N) := by
      rw [show (1:ℝ) + (α + δ + γ) = γ + ((α + δ) + 1) by ring,
        Real.rpow_add hN0 γ ((α + δ) + 1), Real.rpow_add hN0 (α + δ) 1, Real.rpow_one]
    rw [hid]
    ring
  set B : ℝ := Db + Mb * w / 3 with hBdef
  have hB0 : (0:ℝ) < B := by
    rw [hBdef]
    have h1 : (0:ℝ) < Mb * w / 3 := by positivity
    linarith only [hDb0, h1]
  have hBub : B ≤ Cden * N ^ (1 + (α + δ + γ)) := by
    have hMw : Mb * w ≤ (CL * N ^ (α + δ + γ)) * (|m| * N) :=
      mul_le_mul hMbub hwub hw0.le (by positivity)
    have hval : (CL * N ^ (α + δ + γ)) * (|m| * N)
        = CL * |m| * N ^ (1 + (α + δ + γ)) := by
      have hid : N ^ (1 + (α + δ + γ)) = N ^ (α + δ + γ) * N := by
        rw [show (1:ℝ) + (α + δ + γ) = (α + δ + γ) + 1 by ring,
          Real.rpow_add hN0 (α + δ + γ) 1, Real.rpow_one]
      rw [hid]
      ring
    rw [hval] at hMw
    have hNe0 : (0:ℝ) < N ^ (1 + (α + δ + γ)) := Real.rpow_pos_of_pos hN0 _
    rw [hBdef, hCden]
    nlinarith only [hDbub, hMw, hNe0]
  have hNsq : (N ^ (1 - σ)) ^ 2 = N ^ (2 - 2 * σ) := by
    rw [← Real.rpow_natCast (N ^ (1 - σ)) 2, ← Real.rpow_mul hN0.le]
    congr 1
    push_cast
    ring
  have hAlb : cw ^ 2 / 2 * N ^ (2 - 2 * σ) ≤ w ^ 2 / 2 := by
    have hpos : (0:ℝ) ≤ cw * N ^ (1 - σ) := by positivity
    have h1 : (cw * N ^ (1 - σ)) ^ 2 ≤ w ^ 2 := pow_le_pow_left₀ hpos hwlb 2
    have h2 : (cw * N ^ (1 - σ)) ^ 2 = cw ^ 2 * N ^ (2 - 2 * σ) := by rw [mul_pow, hNsq]
    rw [h2] at h1
    linarith only [h1]
  have hE : cE * N ^ (δ / 2) ≤ w ^ 2 / 2 / B := by
    have hstep : (cw ^ 2 / 2 * N ^ (2 - 2 * σ)) / (Cden * N ^ (1 + (α + δ + γ)))
        ≤ w ^ 2 / 2 / B := div_le_div₀ (by positivity) hAlb hB0 hBub
    have heq : (cw ^ 2 / 2 * N ^ (2 - 2 * σ)) / (Cden * N ^ (1 + (α + δ + γ)))
        = cE * N ^ (2 - 2 * σ - (1 + (α + δ + γ))) := by
      rw [hcE, Real.rpow_sub hN0 (2 - 2 * σ) (1 + (α + δ + γ))]
      field_simp
    have hmono : N ^ (δ / 2) ≤ N ^ (2 - 2 * σ - (1 + (α + δ + γ))) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by linarith only [hkey])
    calc cE * N ^ (δ / 2) ≤ cE * N ^ (2 - 2 * σ - (1 + (α + δ + γ))) :=
          mul_le_mul_of_nonneg_left hmono hcE0.le
      _ = (cw ^ 2 / 2 * N ^ (2 - 2 * σ)) / (Cden * N ^ (1 + (α + δ + γ))) := heq.symm
      _ ≤ w ^ 2 / 2 / B := hstep
  -- the good-walk contribution
  have hterm1 : N * polyCap M0 β M Rk * polyBern m d k Mb Db ≤ C1 * (1 / 2 : ℝ) ^ k := by
    refine hC1 k _ (w ^ 2 / 2 / B) ?_ hE
    rw [polyBern, ← hN, ← hwdef, ← hBdef, neg_div]
    have hN3 : N ^ (3 + γ) = N * N * N * N ^ γ := by
      have h3 : N ^ (3:ℝ) = N * N * N := by
        rw [show (3:ℝ) = ((3:ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        ring
      rw [Real.rpow_add hN0 3 γ, h3]
    have hLnn : (0:ℝ) ≤ polyCap M0 β M Rk := hLcap0.le
    have hstep1 : ((k : ℝ) + 1) * N * N * polyCap M0 β M Rk
        ≤ N * N * N * polyCap M0 β M Rk := by
      have hpre : ((k : ℝ) + 1) * N * N ≤ N * N * N := by
        have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hk1N hN0.le) hN0.le
        linarith only [h]
      exact mul_le_mul_of_nonneg_right hpre hLnn
    have hstep2 : N * N * N * polyCap M0 β M Rk ≤ N * N * N * (CL * N ^ γ) :=
      mul_le_mul_of_nonneg_left hLbd (by positivity)
    have hcore : ((k : ℝ) + 1) * N * N * polyCap M0 β M Rk ≤ CL * N ^ (3 + γ) := by
      rw [hN3]
      nlinarith only [hstep1, hstep2]
    have hLHS : N * polyCap M0 β M Rk
          * (((k : ℝ) + 1) * N * (2 * Real.exp (-(w ^ 2 / 2 / B))))
        = 2 * (((k : ℝ) + 1) * N * N * polyCap M0 β M Rk) * Real.exp (-(w ^ 2 / 2 / B)) := by
      ring
    have hRHS : 2 * CL * N ^ (3 + γ) * Real.exp (-(w ^ 2 / 2 / B))
        = 2 * (CL * N ^ (3 + γ)) * Real.exp (-(w ^ 2 / 2 / B)) := by ring
    rw [hLHS, hRHS]
    exact mul_le_mul_of_nonneg_right (by linarith only [hcore]) (Real.exp_nonneg _)
  -- the bad-walk contribution
  have hcapNn0 : (0:ℝ) ≤ polyCap M0 β M Nn := (polyCap_pos hM0 hM Nn).le
  have hBbub : N * polyCap M0 β M Nn ≤ CB * N ^ (1 + β) := by
    have hcapN : polyCap M0 β M Nn ≤ CB * N ^ β := by
      rw [polyCap, hNcast]
      have hNβ0 : (0:ℝ) ≤ N ^ β := Real.rpow_nonneg hN0.le β
      have hmax : max M0 (N ^ β) ≤ M0 + N ^ β :=
        max_le (by linarith only [hNβ0]) (by linarith only [hM0])
      have hkey3 : M0 + M ≤ (M0 + M) * N ^ β := by
        calc M0 + M = (M0 + M) * 1 := (mul_one _).symm
          _ ≤ (M0 + M) * N ^ β := mul_le_mul_of_nonneg_left hNβ1 (by linarith only [hM, hM0])
      have hexp3 : CB * N ^ β = (M0 + M) * N ^ β + N ^ β := by rw [hCB]; ring
      rw [hexp3]
      linarith only [hmax, hkey3]
    have h1 : N * polyCap M0 β M Nn ≤ N * (CB * N ^ β) :=
      mul_le_mul_of_nonneg_left hcapN hN0.le
    refine le_trans h1 (le_of_eq ?_)
    have hid : N ^ (1 + β) = N * N ^ β := by
      rw [Real.rpow_add hN0 1 β, Real.rpow_one]
    rw [hid]
    ring
  have hcompl : RWRS.walkLaw G o (polyGood G o α δ k Rk)ᶜ
      ≤ ENNReal.ofReal (Cr * N ^ (d_s / 2 - (r : ℝ) * δ))
        + ENNReal.ofReal (C_disp * Real.exp (-(c_disp * N ^ (s * d_w / (d_w - 1))))) := by
    refine le_trans (walkLaw_polyGood_compl_le o o α δ k Rk) (add_le_add ?_ ?_)
    · exact (hCrb o k).1 hds2
    · have hstep := hExitBound Nn hNn1
      rw [hNcast] at hstep
      exact hstep
  have hterm2 : ENNReal.ofReal (N * polyCap M0 β M Nn)
        * RWRS.walkLaw G o (polyGood G o α δ k Rk)ᶜ
      ≤ ENNReal.ofReal ((CB * Cr + C2) * (1 / 2 : ℝ) ^ k) := by
    have hBb0 : (0:ℝ) ≤ N * polyCap M0 β M Nn := mul_nonneg hN0.le hcapNn0
    have hA : (N * polyCap M0 β M Nn) * (Cr * N ^ (d_s / 2 - (r : ℝ) * δ))
        ≤ CB * Cr * (1 / 2 : ℝ) ^ k := by
      have h1 : (N * polyCap M0 β M Nn) * (Cr * N ^ (d_s / 2 - (r : ℝ) * δ))
          ≤ (CB * N ^ (1 + β)) * (Cr * N ^ (d_s / 2 - (r : ℝ) * δ)) :=
        mul_le_mul_of_nonneg_right hBbub (by positivity)
      have h2 : (CB * N ^ (1 + β)) * (Cr * N ^ (d_s / 2 - (r : ℝ) * δ))
          = CB * Cr * N ^ ((1 + β) + (d_s / 2 - (r : ℝ) * δ)) := by
        rw [Real.rpow_add hN0 (1 + β) (d_s / 2 - (r : ℝ) * δ)]
        ring
      rw [h2] at h1
      refine le_trans h1 ?_
      have h3 : N ^ ((1 + β) + (d_s / 2 - (r : ℝ) * δ)) ≤ (1 / 2 : ℝ) ^ k :=
        rpow_le_geom (by linarith only [hrδ]) k
      exact mul_le_mul_of_nonneg_left h3 (by positivity)
    have hBg : (N * polyCap M0 β M Nn)
          * (C_disp * Real.exp (-(c_disp * N ^ (s * d_w / (d_w - 1)))))
        ≤ C2 * (1 / 2 : ℝ) ^ k := by
      refine hC2 k _ (c_disp * N ^ (s * d_w / (d_w - 1))) ?_ le_rfl
      rw [← hN]
      have h1 : (N * polyCap M0 β M Nn)
            * (C_disp * Real.exp (-(c_disp * N ^ (s * d_w / (d_w - 1)))))
          ≤ (CB * N ^ (1 + β))
            * (C_disp * Real.exp (-(c_disp * N ^ (s * d_w / (d_w - 1))))) :=
        mul_le_mul_of_nonneg_right hBbub (by positivity)
      refine le_trans h1 (le_of_eq ?_)
      ring
    calc ENNReal.ofReal (N * polyCap M0 β M Nn)
          * RWRS.walkLaw G o (polyGood G o α δ k Rk)ᶜ
        ≤ ENNReal.ofReal (N * polyCap M0 β M Nn)
            * (ENNReal.ofReal (Cr * N ^ (d_s / 2 - (r : ℝ) * δ))
              + ENNReal.ofReal (C_disp
                  * Real.exp (-(c_disp * N ^ (s * d_w / (d_w - 1)))))) :=
          mul_le_mul' le_rfl hcompl
      _ = ENNReal.ofReal ((N * polyCap M0 β M Nn) * (Cr * N ^ (d_s / 2 - (r : ℝ) * δ)))
            + ENNReal.ofReal ((N * polyCap M0 β M Nn)
                * (C_disp * Real.exp (-(c_disp * N ^ (s * d_w / (d_w - 1)))))) := by
          rw [mul_add, ← ENNReal.ofReal_mul hBb0, ← ENNReal.ofReal_mul hBb0]
      _ ≤ ENNReal.ofReal (CB * Cr * (1 / 2 : ℝ) ^ k)
            + ENNReal.ofReal (C2 * (1 / 2 : ℝ) ^ k) :=
          add_le_add (ENNReal.ofReal_le_ofReal hA) (ENNReal.ofReal_le_ofReal hBg)
      _ = ENNReal.ofReal ((CB * Cr + C2) * (1 / 2 : ℝ) ^ k) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          ring
  calc ENNReal.ofReal (N * polyCap M0 β M Rk * polyBern m d k Mb Db)
        + ENNReal.ofReal (N * polyCap M0 β M Nn)
          * RWRS.walkLaw G o (polyGood G o α δ k Rk)ᶜ
      ≤ ENNReal.ofReal (C1 * (1 / 2 : ℝ) ^ k)
          + ENNReal.ofReal ((CB * Cr + C2) * (1 / 2 : ℝ) ^ k) :=
        add_le_add (ENNReal.ofReal_le_ofReal hterm1) hterm2
    _ = ENNReal.ofReal ((C1 + CB * Cr + C2) * (1 / 2 : ℝ) ^ k) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

/-- **The running supremum of the payoff of the recentred field has a finite
joint mean.** -/
theorem lintegral_supPayoff_ne_top_poly [Infinite V] (hG : G.Connected)
    (d : ℕ) (hbd : RWRS.BoundedDegree G d) (hdeg : ∀ v : V, 1 ≤ G.degree v) (hd : 0 < d)
    {d_s A : ℝ} (hds0 : 0 < d_s) (hds2 : d_s < 2) (hH2 : RWRS.SpectralDimensionBound G d_s A)
    {d_w : ℝ} (hdw : 2 ≤ d_w)
    (ρ : Measure ℝ) [IsProbabilityMeasure ρ] {m : ℝ} (hmeq : RWRS.extMean ρ = (m : EReal))
    (hm : m < 0) {p : ℝ} (hp1 : 1 ≤ p) (habs : RWRS.absMoment ρ p ≠ ⊤)
    (o : V) (hExit : PolynomialExitBoundAt G o d_w) {M M0 β δ Cm p2 : ℝ} (hM : 0 ≤ M) (hM0 : 1 ≤ M0)
    (hβ0 : 0 < β) (hβdw : β / d_w < d_s / 2) (hδ : δ = (d_s / 2 - β / d_w) / 2)
    (hp2a : 1 ≤ p2) (hp2b : p2 ≤ 2) (hCm : 0 ≤ Cm)
    (hvarbd : ∀ v : V, (∫ z, (siteShift ρ M m (polyLevel G o M0 β v) z - m) ^ 2 ∂ρ)
        ≤ (polyLevel G o M0 β v + M) ^ (2 - p2) * Cm) :
    (∫⁻ z, RWRS.supPayoff G (zetaField ρ M m (polyLevel G o M0 β) z.1) z.2
        ∂(RWRS.jointLaw G ρ o)) ≠ ⊤ := by
  obtain ⟨C, hC0, hCk⟩ := exists_block_bound_poly hG d hbd hdeg hd hds0 hds2 hH2 hdw
    ρ hmeq hm hp1 habs o hExit hM hM0 hβ0 hβdw hδ hp2a hp2b hCm hvarbd
  refine ne_top_of_le_ne_top ?_ (lintegral_supPayoff_zetaField_le hG hbd hm _ o)
  refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hCk)
  rw [tsum_ofReal_geom C (1 / 2) hC0 (by norm_num) (by norm_num)]
  exact ENNReal.ofReal_ne_top

/-- Polynomial volume growth, spectral dimension below two and polynomial-radius
exit control at the distinguished origin give an almost surely finite optimal
bounded rule for a scenery of negative mean with a finite moment of order
`p > max(2d_f/(d_wd_s),1)`. -/
theorem ae_supStopValue_ne_top_poly_of_exit [Infinite V] (hG : G.Connected)
    (d : ℕ) (hbd : RWRS.BoundedDegree G d)
    {C_vol d_f : ℝ} (hdf : 0 < d_f) (o : V) (hH1 : RWRS.VolumeGrowthUpper G o C_vol d_f)
    {d_s A : ℝ} (hds0 : 0 < d_s) (hds2 : d_s < 2) (hH2 : RWRS.SpectralDimensionBound G d_s A)
    {d_w : ℝ} (hdw : 2 ≤ d_w) (hExit : PolynomialExitBoundAt G o d_w)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hmean : RWRS.extMean ν < 0)
    {p : ℝ} (hp : max (2 * d_f / (d_w * d_s)) 1 < p) (hmom : RWRS.posMoment ν p ≠ ⊤) :
    ∀ᵐ ξ ∂(RWRS.iidLaw V ν), RWRS.supStopValue G ξ o ≠ ⊤ := by
  classical
  haveI : IsProbabilityMeasure (RWRS.iidLaw V ν) := instIsProbabilityMeasureIid ν
  haveI : IsProbabilityMeasure (RWRS.walkLaw G o) := by rw [walkLaw_eq_lib]; infer_instance
  have hdeg : ∀ v : V, 1 ≤ G.degree v := fun v => degree_pos_of_connected hG v
  have hd0 : 0 < d := lt_of_lt_of_le (hdeg o) (hbd o)
  have hp1 : 1 ≤ p := le_of_lt (lt_of_le_of_lt (le_max_right _ _) hp)
  have hp0 : (0:ℝ) < p := lt_of_lt_of_le zero_lt_one hp1
  have hpdf : 2 * d_f / (d_w * d_s) < p := lt_of_le_of_lt (le_max_left _ _) hp
  have hdw0 : (0:ℝ) < d_w := by linarith
  have hdsw0 : (0:ℝ) < d_w * d_s := by positivity
  have h1 : 2 * d_f < p * (d_w * d_s) := by
    rw [div_lt_iff₀ hdsw0] at hpdf
    linarith
  have hdfp : d_f / p < d_w * d_s / 2 := by
    rw [div_lt_div_iff₀ hp0 (by norm_num : (0:ℝ) < 2)]
    linarith
  set β : ℝ := (d_f / p + d_w * d_s / 2) / 2 with hβdef
  have hdfp0 : (0:ℝ) < d_f / p := by positivity
  have hβ0 : (0:ℝ) < β := by rw [hβdef]; linarith
  have hβp : d_f < β * p := by
    have hlt : d_f / p < β := by rw [hβdef]; linarith
    rw [div_lt_iff₀ hp0] at hlt
    linarith
  have hβdw : β / d_w < d_s / 2 := by
    have hb : β < d_w * d_s / 2 := by rw [hβdef]; linarith
    rw [div_lt_div_iff₀ hdw0 (by norm_num : (0:ℝ) < 2)]
    nlinarith [hb, hdw0]
  set δ : ℝ := (d_s / 2 - β / d_w) / 2 with hδdef
  obtain ⟨M, hM0, habsM, m, hmeq, hm⟩ := exists_lowTrunc ν hp1 hmom hmean
  set ρ : Measure ℝ := ν.map (lowTrunc M) with hρ
  haveI : IsProbabilityMeasure ρ :=
    Measure.isProbabilityMeasure_map (measurable_lowTrunc M).aemeasurable
  set p2 : ℝ := min p 2 with hp2def
  have hp2a : 1 ≤ p2 := le_min hp1 (by norm_num)
  have hp2b : p2 ≤ 2 := min_le_right _ _
  have habs2 : RWRS.absMoment ρ p2 ≠ ⊤ :=
    absMoment_ne_top_of_le ρ (by linarith) (min_le_left _ _) habsM
  obtain ⟨Cm, hCm0, hCmb⟩ := exists_moment_bound ρ (m := m) hM0 hp2a hp2b habs2
  have hvarbd : ∀ M0 : ℝ, 1 ≤ M0 → ∀ v : V,
      (∫ z, (siteShift ρ M m (polyLevel G o M0 β v) z - m) ^ 2 ∂ρ)
        ≤ (polyLevel G o M0 β v + M) ^ (2 - p2) * Cm := by
    intro M0 hM01 v
    have hlev : -M ≤ polyLevel G o M0 β v := neg_le_polyLevel (by linarith) β o v
    have hpos : (0:ℝ) < polyLevel G o M0 β v + M := by
      have hb := le_polyLevel G o M0 β v
      linarith
    exact integral_sq_siteShift_le ρ hM0 hp2a hp2b hlev hpos habs2 (hCmb _ hlev)
  have hposP : RWRS.posPart ρ ≠ ⊤ := by
    rw [hρ, posPart_map_lowTrunc ν hM0]
    exact posPart_ne_top_of_posMoment ν hp1 hmom
  have hnegP : RWRS.negPart ρ ≠ ⊤ := negPart_map_lowTrunc_ne_top ν M
  have hint : Integrable (fun z : ℝ => z) ρ := integrable_id_of_finite hposP hnegP
  have hmint : ∫ z, z ∂ρ = m := by
    rw [integral_id_eq hint]
    have hcoe : ((m : ℝ) : EReal)
        = (((RWRS.posPart ρ).toReal - (RWRS.negPart ρ).toReal : ℝ) : EReal) := by
      rw [← hmeq, extMean_eq_coe hposP hnegP]
    exact (EReal.coe_eq_coe_iff.1 hcoe).symm
  have hCvol : RWRS.VolumeGrowthUpper G o (max C_vol 0) d_f := by
    intro r hr
    refine le_trans (hH1 r hr) (ENNReal.ofReal_le_ofReal ?_)
    have hle : C_vol ≤ max C_vol 0 := le_max_left _ _
    have hrp : (0:ℝ) ≤ (r : ℝ) ^ d_f := Real.rpow_nonneg (Nat.cast_nonneg r) d_f
    nlinarith
  have hmain : ∀ ε : ℝ, 0 < ε →
      RWRS.iidLaw V ν {ξ : V → ℝ | RWRS.supStopValue G ξ o = ⊤} ≤ ENNReal.ofReal ε := by
    intro ε hε
    obtain ⟨M0, hM01, hM0sum⟩ := exists_polyLevel_tsum_le hG ν (le_max_right C_vol 0) hdf o
      hCvol hp0 hβ0 hβp hmom hε
    have hlevneg : ∀ v : V, -M ≤ polyLevel G o M0 β v :=
      fun v => neg_le_polyLevel (by linarith) β o v
    have hc : ∀ v : V, siteMean ρ M (polyLevel G o M0 β v) ≤ m := by
      intro v
      exact siteMean_le_of_lowTrunc ν (hlevneg v) hint hmint
    have hfin := lintegral_supPayoff_ne_top_poly hG d hbd hdeg hd0 hds0 hds2 hH2 hdw
      ρ hmeq hm hp1 habsM o hExit hM0 hM01 hβ0 hβdw hδdef hp2a hp2b hCm0 (hvarbd M0 hM01)
    have hae := ae_lintegral_supPayoff_ne_top_of_lintegral hG hc o hfin
    have hTmeas : Measurable fun (ξ : V → ℝ) (v : V) => lowTrunc M (ξ v) :=
      measurable_pi_lambda _ fun v => (measurable_lowTrunc M).comp (measurable_pi_apply v)
    have hmapT : (RWRS.iidLaw V ν).map (fun (ξ : V → ℝ) (v : V) => lowTrunc M (ξ v))
        = RWRS.iidLaw V ρ := iidLaw_map ν (measurable_lowTrunc M)
    have hJmeas : Measurable fun ξ : V → ℝ =>
        ∫⁻ X, RWRS.supPayoff G ξ X ∂(RWRS.walkLaw G o) :=
      (measurable_supPayoff_prod (G := G)).lintegral_prod_right'
    have hlow : MeasurableSet {ξ : V → ℝ | ∀ v : V, ξ v ≤ polyLevel G o M0 β v} := by
      have hset : {ξ : V → ℝ | ∀ v : V, ξ v ≤ polyLevel G o M0 β v}
          = ⋂ v : V, {ξ : V → ℝ | ξ v ≤ polyLevel G o M0 β v} := by
        ext ξ
        simp only [Set.mem_setOf_eq, Set.mem_iInter]
      rw [hset]
      exact MeasurableSet.iInter fun v =>
        measurableSet_le (measurable_pi_apply v) measurable_const
    have hSmeas : MeasurableSet {ξ : V → ℝ | (∀ v : V, ξ v ≤ polyLevel G o M0 β v) →
        (∫⁻ X, RWRS.supPayoff G ξ X ∂(RWRS.walkLaw G o)) ≠ ⊤} := by
      have hfinset : MeasurableSet
          {ξ : V → ℝ | (∫⁻ X, RWRS.supPayoff G ξ X ∂(RWRS.walkLaw G o)) ≠ ⊤} :=
        (hJmeas (measurableSet_singleton (⊤ : ℝ≥0∞))).compl
      have hset : {ξ : V → ℝ | (∀ v : V, ξ v ≤ polyLevel G o M0 β v) →
            (∫⁻ X, RWRS.supPayoff G ξ X ∂(RWRS.walkLaw G o)) ≠ ⊤}
          = {ξ : V → ℝ | ∀ v : V, ξ v ≤ polyLevel G o M0 β v}ᶜ
            ∪ {ξ : V → ℝ | (∫⁻ X, RWRS.supPayoff G ξ X ∂(RWRS.walkLaw G o)) ≠ ⊤} := by
        ext ξ
        simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_compl_iff]
        tauto
      rw [hset]
      exact hlow.compl.union hfinset
    have haeν : ∀ᵐ ξ ∂(RWRS.iidLaw V ν),
        (∀ v : V, lowTrunc M (ξ v) ≤ polyLevel G o M0 β v) →
          (∫⁻ X, RWRS.supPayoff G (fun v => lowTrunc M (ξ v)) X ∂(RWRS.walkLaw G o)) ≠ ⊤ := by
      refine (MeasureTheory.ae_map_iff hTmeas.aemeasurable hSmeas).1 ?_
      rw [hmapT]
      exact hae
    have hsub : {ξ : V → ℝ | RWRS.supStopValue G ξ o = ⊤}
        ⊆ {ξ : V → ℝ | ∀ v : V, ξ v ≤ polyLevel G o M0 β v}ᶜ
          ∪ {ξ : V → ℝ | ¬((∀ v : V, lowTrunc M (ξ v) ≤ polyLevel G o M0 β v) →
              (∫⁻ X, RWRS.supPayoff G (fun v => lowTrunc M (ξ v)) X
                ∂(RWRS.walkLaw G o)) ≠ ⊤)} := by
      intro ξ hξ
      by_cases hle : ∀ v : V, ξ v ≤ polyLevel G o M0 β v
      · refine Or.inr ?_
        intro hcon
        have hTle : ∀ v : V, lowTrunc M (ξ v) ≤ polyLevel G o M0 β v := by
          intro v
          rw [lowTrunc]
          exact max_le (hle v) (hlevneg v)
        have hJT := hcon hTle
        have hstop : RWRS.supStopValue G ξ o
            ≤ ∫⁻ X, RWRS.supPayoff G ξ X ∂(RWRS.walkLaw G o) :=
          supStopValue_le_lintegral_supPayoff hG ξ o
        have hmono : (∫⁻ X, RWRS.supPayoff G ξ X ∂(RWRS.walkLaw G o))
            ≤ ∫⁻ X, RWRS.supPayoff G (fun v => lowTrunc M (ξ v)) X ∂(RWRS.walkLaw G o) :=
          lintegral_mono fun X => supPayoff_mono (fun v => le_lowTrunc M (ξ v)) X
        have hξ' : RWRS.supStopValue G ξ o = ⊤ := hξ
        rw [hξ'] at hstop
        exact hJT (top_unique (le_trans hstop hmono))
      · exact Or.inl hle
    refine le_trans (measure_mono hsub) ?_
    refine le_trans (measure_union_le _ _) ?_
    rw [MeasureTheory.ae_iff.1 haeν, add_zero]
    exact le_trans (meas_forall_le_compl_le ν _) hM0sum
  have hzero : RWRS.iidLaw V ν {ξ : V → ℝ | RWRS.supStopValue G ξ o = ⊤} = 0 := by
    refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_) bot_le
    rw [zero_add]
    refine le_trans (hmain (ε : ℝ) (by exact_mod_cast hε)) (le_of_eq ?_)
    exact ENNReal.ofReal_coe_nnreal
  rw [MeasureTheory.ae_iff]
  simpa using hzero

/-- Polynomial volume growth and uniform walk-dimension control give an almost
surely finite optimal stopping value at the distinguished origin. -/
theorem ae_supStopValue_ne_top_poly [Infinite V] (hG : G.Connected)
    (d : ℕ) (hbd : RWRS.BoundedDegree G d)
    {C_vol d_f : ℝ} (hdf : 0 < d_f) (o : V) (hH1 : RWRS.VolumeGrowthUpper G o C_vol d_f)
    {d_s A : ℝ} (hds0 : 0 < d_s) (hds2 : d_s < 2) (hH2 : RWRS.SpectralDimensionBound G d_s A)
    {d_w C_disp c_disp : ℝ} (hdw : 2 ≤ d_w) (hCd : 0 < C_disp) (hcd : 0 < c_disp)
    (hH3 : RWRS.WalkDimensionBound G d_w C_disp c_disp)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hmean : RWRS.extMean ν < 0)
    {p : ℝ} (hp : max (2 * d_f / (d_w * d_s)) 1 < p) (hmom : RWRS.posMoment ν p ≠ ⊤) :
    ∀ᵐ ξ ∂(RWRS.iidLaw V ν), RWRS.supStopValue G ξ o ≠ ⊤ := by
  exact ae_supStopValue_ne_top_poly_of_exit hG d hbd hdf o hH1 hds0 hds2 hH2 hdw
    (polynomialExitBoundAt_of_walkDimensionBound hH3 hdw hCd hcd o) ν hmean hp hmom

end RWRS.Support
