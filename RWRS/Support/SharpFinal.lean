/-
`lem:moment-sharpness`: the assembly.

The first reduction is the constant stopping rule: running the walk for one step
is worth `(σ(o)-1)/deg(o)`, so an infinite mean of the positive part already
makes the mean odometer infinite.  Off that case the marginal is integrable, and
the mean `μ` is a real number.
-/
import RWRS.Support.SharpEvent
import RWRS.Support.SharpTail
import RWRS.Support.MomentDivergence
import RWRS.Support.TailSum
import RWRS.Support.Explosion

namespace RWRS.Support

open MeasureTheory
open scoped ENNReal Classical

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite] [Infinite V]
  {ν : Measure ℝ} [IsProbabilityMeasure ν]

/-- **The first reduction.**  An infinite mean of the positive part of the
marginal already makes the mean odometer infinite, through the rule that stops
after one step. -/
theorem lintegral_odometerLimit_eq_top_of_posPart (hG : G.Connected) (o : V)
    (hpos : RWRS.posPart ν = ⊤) :
    (∫⁻ σ, RWRS.odometerLimit G σ o ∂(RWRS.iidLaw V ν)) = ⊤ := by
  set d : ℝ := (G.degree o : ℝ) with hd
  have hd1 : (1 : ℝ) ≤ d := by
    have := degree_pos (G := G) hG o
    rw [hd]
    exact_mod_cast this
  have hd0 : (0 : ℝ) < d := by linarith
  set f : ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal ((z - 1) / d) with hf
  have hfmeas : Measurable f := ENNReal.measurable_ofReal.comp ((measurable_id.sub_const 1).div_const d)
  have hle : (∫⁻ σ, f (σ o) ∂(RWRS.iidLaw V ν))
      ≤ ∫⁻ σ, RWRS.odometerLimit G σ o ∂(RWRS.iidLaw V ν) :=
    lintegral_mono fun σ => ofReal_excess_le_odometerLimit hG σ o
  have hcoord : (∫⁻ σ, f (σ o) ∂(RWRS.iidLaw V ν)) = ∫⁻ z, f z ∂ν :=
    lintegral_coord o hfmeas
  have hkey : (∫⁻ z, f z ∂ν) = ⊤ := by
    by_contra hcon
    have hpt : ∀ z : ℝ, ENNReal.ofReal z ≤ ENNReal.ofReal d * f z + ENNReal.ofReal d := by
      intro z
      have hprod : ENNReal.ofReal d * f z = ENNReal.ofReal (z - 1) := by
        rw [hf]
        rw [← ENNReal.ofReal_mul hd0.le]
        congr 1
        field_simp
      rw [hprod]
      rcases le_or_gt z 1 with hz | hz
      · refine le_trans (ENNReal.ofReal_le_ofReal (le_trans hz hd1)) le_add_self
      · rw [← ENNReal.ofReal_add (by linarith) hd0.le]
        exact ENNReal.ofReal_le_ofReal (by linarith)
    have hbd : RWRS.posPart ν ≤ ENNReal.ofReal d * (∫⁻ z, f z ∂ν) + ENNReal.ofReal d := by
      rw [RWRS.posPart]
      calc (∫⁻ z, ENNReal.ofReal z ∂ν)
          ≤ ∫⁻ z, (ENNReal.ofReal d * f z + ENNReal.ofReal d) ∂ν := lintegral_mono hpt
        _ = ENNReal.ofReal d * (∫⁻ z, f z ∂ν) + ENNReal.ofReal d := by
            rw [lintegral_add_right _ measurable_const, lintegral_const_mul _ hfmeas]
            simp
    rw [hpos] at hbd
    have : ENNReal.ofReal d * (∫⁻ z, f z ∂ν) + ENNReal.ofReal d ≠ ⊤ :=
      ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hcon, ENNReal.ofReal_ne_top⟩
    exact this (top_le_iff.1 hbd)
  rw [hcoord, hkey] at hle
  exact top_le_iff.1 hle


/-- Half of a real at least one is below its floor. -/
theorem half_le_floor {x : ℝ} (hx : 1 ≤ x) : x / 2 ≤ (⌊x⌋₊ : ℝ) := by
  have h1 : (1 : ℝ) ≤ (⌊x⌋₊ : ℝ) := by
    have : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
    exact_mod_cast this
  rcases le_or_gt x 2 with h | h
  · linarith
  · have := Nat.sub_one_lt_floor x
    linarith

omit [Infinite V] in
/-- **Hypothesis (A3) at the radius `⌊t^{1/d_w}⌋`.** -/
theorem card_ball_lower {o : V} {c_vol d_f d_w : ℝ} (hcv : 0 < c_vol) (hdf : 0 < d_f)
    (hdw : 0 < d_w) (hA3 : RWRS.VolumeGrowthLower G o c_vol d_f) {t : ℕ} (ht : 1 ≤ t) :
    c_vol * 2 ^ (-d_f) * (t : ℝ) ^ (d_f / d_w)
      ≤ ((ballFinset G o ⌊(t : ℝ) ^ (1 / d_w)⌋₊).card : ℝ) := by
  have htR : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  have htpos : (0 : ℝ) < (t : ℝ) := by linarith
  set x : ℝ := (t : ℝ) ^ (1 / d_w) with hx
  have hx1 : (1 : ℝ) ≤ x := Real.one_le_rpow htR (by positivity)
  have hR1 : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx1)
  have hfl : x / 2 ≤ (⌊x⌋₊ : ℝ) := half_le_floor hx1
  have hstep : (x / 2) ^ d_f ≤ ((⌊x⌋₊ : ℕ) : ℝ) ^ d_f :=
    Real.rpow_le_rpow (by positivity) hfl hdf.le
  have hsplit : (x / 2) ^ d_f = x ^ d_f / 2 ^ d_f :=
    Real.div_rpow (by linarith : (0:ℝ) ≤ x) (by norm_num : (0:ℝ) ≤ 2) d_f
  have hxdf : x ^ d_f = (t : ℝ) ^ (d_f / d_w) := by
    rw [hx, ← Real.rpow_mul htpos.le]
    congr 1
    field_simp
  have hpow : (2 : ℝ) ^ (-d_f) = 1 / 2 ^ d_f := by
    rw [Real.rpow_neg (by norm_num)]
    simp
  have hkey : c_vol * 2 ^ (-d_f) * (t : ℝ) ^ (d_f / d_w) ≤ c_vol * ((⌊x⌋₊ : ℕ) : ℝ) ^ d_f := by
    rw [hpow]
    have h2 : (0 : ℝ) < 2 ^ d_f := Real.rpow_pos_of_pos (by norm_num) _
    rw [← hxdf] at *
    have : c_vol * (1 / 2 ^ d_f) * x ^ d_f = c_vol * (x ^ d_f / 2 ^ d_f) := by ring
    rw [this, ← hsplit]
    exact mul_le_mul_of_nonneg_left hstep hcv.le
  exact le_trans hkey (card_ballFinset_ge hA3 hR1)


omit [Infinite V] in
/-- **Step 5, in the vocabulary of the ball.**  The volume-weighted tail sum
diverges. -/
theorem tsum_ball_tail_eq_top {o : V} {c_vol d_f d_w α K : ℝ}
    (hcv : 0 < c_vol) (hdf : 0 < d_f) (hdw : 0 < d_w) (hα : 0 < α) (hK : 0 < K)
    (hA3 : RWRS.VolumeGrowthLower G o c_vol d_f)
    (hmom : RWRS.posMoment ν ((d_f + d_w) / (d_w * α)) = ⊤) :
    (∑' t : ℕ, ENNReal.ofReal (((ballFinset G o ⌊(t : ℝ) ^ (1 / d_w)⌋₊).card : ℝ)
      * (ν {z : ℝ | K * (t : ℝ) ^ α ≤ z}).toReal)) = ⊤ := by
  set c : ℝ := d_f / d_w with hc
  have hc0 : 0 ≤ c := by positivity
  have hexp : (c + 1) / α = (d_f + d_w) / (d_w * α) := by
    rw [hc]; field_simp
  have hbase : (∑' t : ℕ, ENNReal.ofReal ((t : ℝ) ^ c) * ν {z : ℝ | K * (t : ℝ) ^ α ≤ z}) = ⊤ := by
    refine tsum_tail_eq_top hc0 hα hK ?_
    rw [hexp]; exact hmom
  set C : ℝ := c_vol * 2 ^ (-d_f) with hC
  have hCpos : 0 < C := by
    rw [hC]
    have : (0 : ℝ) < 2 ^ (-d_f) := Real.rpow_pos_of_pos (by norm_num) _
    positivity
  set g : ℕ → ℝ≥0∞ := fun t => ENNReal.ofReal C *
    (ENNReal.ofReal ((t : ℝ) ^ c) * ν {z : ℝ | K * (t : ℝ) ^ α ≤ z}) with hg
  have hgtop : (∑' t : ℕ, g t) = ⊤ := by
    rw [hg, ENNReal.tsum_mul_left, hbase]
    refine ENNReal.mul_top ?_
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact hCpos
  refine tsum_eq_top_of_eventually_le 1 (fun t => ?_) (fun t ht => ?_) hgtop
  · rw [hg]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))
  · have hcard := card_ball_lower (G := G) hcv hdf hdw hA3 ht
    have hmeas : (ν {z : ℝ | K * (t : ℝ) ^ α ≤ z}) ≠ ⊤ := measure_ne_top _ _
    have hprod : ENNReal.ofReal C * ENNReal.ofReal ((t : ℝ) ^ c)
        ≤ ENNReal.ofReal (((ballFinset G o ⌊(t : ℝ) ^ (1 / d_w)⌋₊).card : ℝ)) := by
      rw [← ENNReal.ofReal_mul hCpos.le]
      exact ENNReal.ofReal_le_ofReal hcard
    calc g t = (ENNReal.ofReal C * ENNReal.ofReal ((t : ℝ) ^ c))
          * ν {z : ℝ | K * (t : ℝ) ^ α ≤ z} := by rw [hg, mul_assoc]
      _ ≤ ENNReal.ofReal (((ballFinset G o ⌊(t : ℝ) ^ (1 / d_w)⌋₊).card : ℝ))
          * ν {z : ℝ | K * (t : ℝ) ^ α ≤ z} := by gcongr
      _ = ENNReal.ofReal (((ballFinset G o ⌊(t : ℝ) ^ (1 / d_w)⌋₊).card : ℝ)
          * (ν {z : ℝ | K * (t : ℝ) ^ α ≤ z}).toReal) := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hmeas]


theorem ofReal_min_one (x : ℝ) : ENNReal.ofReal (min x 1) = min (ENNReal.ofReal x) 1 := by
  rcases le_total x 1 with h | h
  · rw [min_eq_left h, min_eq_left (by simpa using ENNReal.ofReal_le_ofReal h)]
  · rw [min_eq_right h, min_eq_right (by simpa using ENNReal.ofReal_le_ofReal h)]
    simp

/-- **`lem:moment-sharpness`.** -/
theorem momentSharpness_aux (hG : G.Connected) (o : V)
    {α A : ℝ} (hα : 0 < α)
    (hA1 : ∀ (x : V) (n : ℕ), 1 ≤ n → RWRS.heat G n x x / G.degree x ≤ A * (n : ℝ) ^ (-α))
    {d_w a : ℝ} (hdw : 2 ≤ d_w) (ha : 0 < a)
    (hA2 : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ v ∈ RWRS.closedBall G o ⌊(n : ℝ) ^ (1 / d_w)⌋₊,
      a * (n : ℝ) ^ (1 - α) ≤ RWRS.greenTime G n o v)
    {c_vol d_f : ℝ} (hdf : 0 < d_f) (hcv : 0 < c_vol)
    (hA3 : RWRS.VolumeGrowthLower G o c_vol d_f)
    (hmean : (⊥ : EReal) < RWRS.extMean ν)
    (hmom : RWRS.posMoment ν ((d_f + d_w) / (d_w * α)) = ⊤) :
    (∫⁻ σ, RWRS.odometerLimit G σ o ∂(RWRS.iidLaw V ν)) = ⊤ := by
  haveI : IsProbabilityMeasure (RWRS.iidLaw V ν) := instIsProbabilityMeasureIid ν
  have hdw0 : (0 : ℝ) < d_w := by linarith
  by_cases hpos : RWRS.posPart ν = ⊤
  · exact lintegral_odometerLimit_eq_top_of_posPart hG o hpos
  have hneg : RWRS.negPart ν ≠ ⊤ := by
    intro hn
    rw [RWRS.extMean, hn] at hmean
    simp at hmean
  have hintid : Integrable (fun z : ℝ => z) ν := integrable_id_of_finite hpos hneg
  set μ : ℝ := ∫ z, z ∂ν with hμ
  have hint : Integrable (fun z => z - μ) ν := hintid.sub (integrable_const μ)
  have hmean0 : ∫ z, (z - μ) ∂ν = 0 := by
    rw [integral_sub hintid (integrable_const μ), integral_const]
    simp [hμ]
  obtain ⟨M, hM, htail⟩ := exists_tailPart_le (ν := ν) μ hint (by norm_num : (0:ℝ) < 1 / 32)
  have h2pow : (0 : ℝ) < 2 ^ (1 - α) := Real.rpow_pos_of_pos (by norm_num) _
  set c₀ : ℝ := a * 2 ^ (1 - α) with hc₀def
  have hc₀ : 0 < c₀ := by rw [hc₀def]; positivity
  set K : ℝ := (c₀ * |μ| + 2 * |μ| + 5) / c₀ with hKdef
  have hK : c₀ * K = c₀ * |μ| + 2 * |μ| + 5 := by rw [hKdef]; field_simp
  have hKpos : 0 < K := by nlinarith [abs_nonneg μ]
  have hKμ : μ ≤ K := by
    have h1 : μ ≤ |μ| := le_abs_self μ
    have h2 : |μ| ≤ K := by
      rw [hKdef, le_div_iff₀ hc₀]
      nlinarith [abs_nonneg μ]
    linarith
  set A' : ℝ := max A 1 with hA'def
  have hA'1 : (1 : ℝ) ≤ A' := le_max_right _ _
  set ε : ℝ := 1 / (2048 * A' * (M ^ 2 + 1)) with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; positivity
  obtain ⟨N₁, hN₁1, hN₁⟩ := clockSum_le_eps_mul hα hεpos
  obtain ⟨N₀, hN₀⟩ := hA2
  set T : ℕ := max 1 (max N₀ N₁) with hTdef
  set f : ℕ → ℝ≥0∞ := fun t =>
    RWRS.iidLaw V ν {σ : V → ℝ | ((t : ℕ) : ℝ≥0∞) + 1 ≤ RWRS.odometerLimit G σ o} with hf
  set gg : ℕ → ℝ≥0∞ := fun t => ENNReal.ofReal (9 / 128 *
    min (((ballFinset G o ⌊(t : ℝ) ^ (1 / d_w)⌋₊).card : ℝ)
      * (ν {z : ℝ | K * (t : ℝ) ^ α ≤ z}).toReal) 1) with hgg
  -- the tail sum of the good events diverges
  have hggtop : (∑' t : ℕ, gg t) = ⊤ := by
    have hb := tsum_ball_tail_eq_top (G := G) (ν := ν) (o := o) hcv hdf hdw0 hα hKpos hA3 hmom
    have hmin := tsum_min_one_eq_top
      (a := fun t : ℕ => ENNReal.ofReal (((ballFinset G o ⌊(t : ℝ) ^ (1 / d_w)⌋₊).card : ℝ)
        * (ν {z : ℝ | K * (t : ℝ) ^ α ≤ z}).toReal))
      (fun t => ENNReal.ofReal_ne_top) hb
    have hrw : ∀ t : ℕ, gg t = ENNReal.ofReal (9 / 128) *
        min (ENNReal.ofReal (((ballFinset G o ⌊(t : ℝ) ^ (1 / d_w)⌋₊).card : ℝ)
          * (ν {z : ℝ | K * (t : ℝ) ^ α ≤ z}).toReal)) 1 := by
      intro t
      simp only [hgg]
      rw [ENNReal.ofReal_mul (p := (9 : ℝ) / 128) (by norm_num)]
      rw [ofReal_min_one]
    rw [tsum_congr hrw, ENNReal.tsum_mul_left, hmin]
    refine ENNReal.mul_top ?_
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    norm_num
  -- the good events sit inside the tail events
  have hstep : ∀ t : ℕ, T ≤ t → gg t ≤ f t := by
    intro t htT
    have ht1 : 1 ≤ t := le_trans (le_max_left 1 _) htT
    have htR : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht1
    have htpos : (0 : ℝ) < (t : ℝ) := by linarith
    have hN0t : N₀ ≤ 2 * t := by
      have : N₀ ≤ t := le_trans (le_trans (le_max_left N₀ N₁) (le_max_right 1 _)) htT
      omega
    have hN1t : N₁ ≤ 2 * t := by
      have : N₁ ≤ t := le_trans (le_trans (le_max_right N₀ N₁) (le_max_right 1 _)) htT
      omega
    set R : ℕ := ⌊(t : ℝ) ^ (1 / d_w)⌋₊ with hR
    have hxle : (t : ℝ) ^ (1 / d_w) ≤ (t : ℝ) := by
      calc (t : ℝ) ^ (1 / d_w) ≤ (t : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le htR (by rw [div_le_one hdw0]; linarith)
        _ = (t : ℝ) := Real.rpow_one _
    have hRt : R ≤ t := by
      rw [hR]
      calc ⌊(t : ℝ) ^ (1 / d_w)⌋₊ ≤ ⌊(t : ℝ)⌋₊ := Nat.floor_mono hxle
        _ = t := Nat.floor_natCast t
    have hRn : R ≤ 2 * t := by omega
    -- the Green function is large on the ball
    have hball : ∀ v ∈ ballFinset G o R, c₀ * (t : ℝ) ^ (1 - α) ≤ RWRS.greenTime G (2 * t) o v := by
      intro v hv
      have hmono : R ≤ ⌊((2 * t : ℕ) : ℝ) ^ (1 / d_w)⌋₊ := by
        refine Nat.floor_mono ?_
        refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
        push_cast; linarith
      have hvmem : v ∈ RWRS.closedBall G o ⌊((2 * t : ℕ) : ℝ) ^ (1 / d_w)⌋₊ := by
        have hv' : v ∈ RWRS.closedBall G o R := mem_ballFinset.1 hv
        have : G.edist v o ≤ (R : ℕ∞) := hv'
        exact le_trans this (by exact_mod_cast hmono)
      have hgv := hN₀ (2 * t) hN0t v hvmem
      have hcast : ((2 * t : ℕ) : ℝ) = 2 * (t : ℝ) := by push_cast; ring
      rw [hcast] at hgv
      have hsplit : ((2 : ℝ) * (t : ℝ)) ^ (1 - α) = 2 ^ (1 - α) * (t : ℝ) ^ (1 - α) :=
        Real.mul_rpow (by norm_num) (by linarith)
      rw [hsplit] at hgv
      calc c₀ * (t : ℝ) ^ (1 - α) = a * (2 ^ (1 - α) * (t : ℝ) ^ (1 - α)) := by
            rw [hc₀def]; ring
        _ ≤ RWRS.greenTime G (2 * t) o v := hgv
    -- the Green function is uniformly small
    set H : ℝ := A' * clockSum α (2 * t) with hH
    have hHle : ∀ u : V, RWRS.greenTime G (2 * t) o u ≤ H := fun u =>
      greenTime_le_clockSum hG hA1 (2 * t) o u
    have hH0 : 0 ≤ H := by
      rw [hH]
      have := clockSum_nonneg α (2 * t)
      positivity
    have hHb : H * (2 * (t : ℝ)) * (4 * M ^ 2) ≤ (t : ℝ) ^ 2 / 128 := by
      have hcs : clockSum α (2 * t) ≤ ε * ((2 * t : ℕ) : ℝ) := hN₁ (2 * t) hN1t
      have hcast : ((2 * t : ℕ) : ℝ) = 2 * (t : ℝ) := by push_cast; ring
      rw [hcast] at hcs
      have hHup : H ≤ A' * (ε * (2 * (t : ℝ))) := by
        rw [hH]
        exact mul_le_mul_of_nonneg_left hcs (by linarith)
      have hMM : 16 * A' * ε * M ^ 2 ≤ 1 / 128 := by
        have hA'0 : (0 : ℝ) < A' := by linarith
        have hM1 : (0 : ℝ) < M ^ 2 + 1 := by positivity
        have heq : 16 * A' * ε * M ^ 2 = M ^ 2 / (128 * (M ^ 2 + 1)) := by
          rw [hεdef]; field_simp; ring
        rw [heq, div_le_iff₀ (by positivity : (0 : ℝ) < 128 * (M ^ 2 + 1))]
        nlinarith [sq_nonneg M]
      calc H * (2 * (t : ℝ)) * (4 * M ^ 2)
          ≤ (A' * (ε * (2 * (t : ℝ)))) * (2 * (t : ℝ)) * (4 * M ^ 2) := by
            refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hHup (by linarith))
              (by positivity)
        _ = (16 * A' * ε * M ^ 2) * (t : ℝ) ^ 2 := by ring
        _ ≤ (1 / 128) * (t : ℝ) ^ 2 := by
            refine mul_le_mul_of_nonneg_right hMM (by positivity)
        _ = (t : ℝ) ^ 2 / 128 := by ring
    exact meas_odometer_ge hG o hint hmean0 hM htail hc₀ hα hK hKμ ht1 hRn hball hHle hHb
  have hftop : (∑' t : ℕ, f t) = ⊤ :=
    tsum_eq_top_of_eventually_le T (fun t => ENNReal.ofReal_ne_top) hstep hggtop
  have hle := tsum_meas_le_lintegral (RWRS.iidLaw V ν)
    (fun σ => RWRS.odometerLimit G σ o) (measurable_odometerLimit o)
  rw [hftop] at hle
  exact top_le_iff.1 hle

end RWRS.Support
