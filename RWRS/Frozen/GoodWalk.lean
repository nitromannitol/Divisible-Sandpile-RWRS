/-
Lemma 5.15 of `rwrs.tex`, frozen.  `rwrs.tex:1124-1142` (label
`lem:good-walk`):

  "Let $G=(V,E)$ be an infinite, locally finite, connected graph with degree
   bounded by $d$ and satisfying the bound (eq:return-bound) for some $d_s>0$
   and $A<\infty$.  Let $(\xi(v))_{v\in V}$ be i.i.d. and independent of the
   walk with $\E[\xi]\in(-\infty,0)$ and $\E[|\xi|^p]<\infty$ for some $p\geq1$,
   and let $Y_k\coloneqq(\max_{2^k\leq n<2^{k+1}}W_n-|\E[\xi]|2^k/d)^+$.  Let
   $\alpha\coloneqq(1-d_s/2)^+$ and fix $\delta\in(0,d_s/2\wedge1)$.  For
   $k\geq0$, let $\mathcal A_k\coloneqq\{\max_v L_N(v)\leq N^{\alpha+\delta}\}$,
   $N\coloneqq2^{k+1}$.  Then:
   (a) For every integer $r\geq1$, $\P_x(\mathcal A_k^c)\leq C_r N^{d_s/2-r\delta}$
   if $d_s<2$, $\leq C_r N^{1-r\delta}(1+\log N)^{r-1}$ if $d_s=2$, and
   $\leq C_r N^{1-r\delta}$ if $d_s>2$.
   (b) $\E_x[Y_k^p]\leq CN^p$ uniformly in $x$ and $k$.
   (c) For every $q\in[1,p)$ and $r$ large enough,
   $\E_x[Y_k^q\one_{\mathcal A_k^c}]=O(2^{-3k})$ uniformly in $x$."

`P_x` is the law of the walk and the expectations in (b) and (c) are joint over
the scenery and the walk.  "Uniformly in `x` and `k`" is a constant bound
before `x` and `k`; the `O(2^{-3k})` of (c) is likewise a constant bound before
`x` and `k`.  The parameter `r` of (a) is the one the paper's constant `C_r`
depends on; (c)'s conclusion does not mention `r`, so it is stated without one.
-/
import RWRS.Support.GoodWalkHolder
import RWRS.Support.LocalTimeRegimes
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open MeasureTheory
open scoped ENNReal

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

-- Three binders of the statement are carried but not referred to.  The mean of
-- the scenery and its negativity enter the lemma through `Y_k`, which subtracts
-- the nonnegative quantity `|m|2^k/d` whatever the sign of the mean, so the
-- three bounds hold for every mean; and the upper bound on `δ` is what the
-- section needs when it applies the lemma, the bounds themselves holding for
-- every positive `δ` because the order `r` of the moment is chosen after it.
set_option linter.unusedVariables false in
-- FROZEN-STATEMENT-BEGIN
theorem RWRS.Frozen.goodWalkBounds [Infinite V] [MeasurableSpace V]
    [MeasurableSingletonClass V] (hG : G.Connected)
    (d : ℕ) (hd : RWRS.BoundedDegree G d) (d_s A : ℝ) (hds : 0 < d_s)
    (hspec : RWRS.SpectralDimensionBound G d_s A)
    (ν : Measure ℝ) (hν : IsProbabilityMeasure ν)
    (m : ℝ) (hm : RWRS.extMean ν = (m : EReal)) (hmneg : m < 0)
    (p : ℝ) (hp : 1 ≤ p) (hmom : RWRS.absMoment ν p ≠ ⊤)
    (α δ : ℝ) (hα : α = max (1 - d_s / 2) 0) (hδ0 : 0 < δ) (hδ1 : δ < min (d_s / 2) 1) :
    (∀ r : ℕ, 1 ≤ r → ∃ Cr : ℝ, 0 < Cr ∧ ∀ (x : V) (k : ℕ),
      (d_s < 2 → RWRS.walkLaw G x (RWRS.goodWalk α δ k)ᶜ
          ≤ ENNReal.ofReal (Cr * (2 ^ (k + 1) : ℝ) ^ (d_s / 2 - r * δ))) ∧
      (d_s = 2 → RWRS.walkLaw G x (RWRS.goodWalk α δ k)ᶜ
          ≤ ENNReal.ofReal (Cr * (2 ^ (k + 1) : ℝ) ^ (1 - r * δ)
              * (1 + Real.log (2 ^ (k + 1))) ^ (r - 1))) ∧
      (2 < d_s → RWRS.walkLaw G x (RWRS.goodWalk α δ k)ᶜ
          ≤ ENNReal.ofReal (Cr * (2 ^ (k + 1) : ℝ) ^ (1 - r * δ)))) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ (x : V) (k : ℕ),
      (∫⁻ z, ENNReal.ofReal (RWRS.dyadicY G z.1 m d k z.2 ^ p) ∂(RWRS.jointLaw G ν x))
        ≤ ENNReal.ofReal (C * (2 ^ (k + 1) : ℝ) ^ p)) ∧
    (∀ q : ℝ, 1 ≤ q → q < p → ∃ C : ℝ, 0 < C ∧ ∀ (x : V) (k : ℕ),
      (∫⁻ z, Set.indicator (RWRS.goodWalk α δ k)ᶜ
          (fun X => ENNReal.ofReal (RWRS.dyadicY G z.1 m d k X ^ q)) z.2
          ∂(RWRS.jointLaw G ν x))
        ≤ ENNReal.ofReal (C * (2 : ℝ) ^ (-(3 : ℝ) * k)))
-- FROZEN-STATEMENT-END
:= by
  classical
  haveI := hν
  haveI : Countable V := RWRS.Support.countable_of_connected hG
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp
  have hδ0' : (0 : ℝ) < δ := hδ0
  have hA : ∀ r : ℕ, 1 ≤ r → ∃ Cr : ℝ, 0 < Cr ∧ ∀ (x : V) (k : ℕ),
      (d_s < 2 → RWRS.walkLaw G x (RWRS.goodWalk α δ k)ᶜ
          ≤ ENNReal.ofReal (Cr * (2 ^ (k + 1) : ℝ) ^ (d_s / 2 - r * δ))) ∧
      (d_s = 2 → RWRS.walkLaw G x (RWRS.goodWalk α δ k)ᶜ
          ≤ ENNReal.ofReal (Cr * (2 ^ (k + 1) : ℝ) ^ (1 - r * δ)
              * (1 + Real.log (2 ^ (k + 1))) ^ (r - 1))) ∧
      (2 < d_s → RWRS.walkLaw G x (RWRS.goodWalk α δ k)ᶜ
          ≤ ENNReal.ofReal (Cr * (2 ^ (k + 1) : ℝ) ^ (1 - r * δ))) := by
    intro r hr
    have hrR : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    obtain ⟨Cp, hCp, hmom24⟩ := RWRS.Support.localTimeMomentsAux (r : ℝ) d_s A hrR hds
    refine ⟨Cp, hCp, fun x k => ?_⟩
    have hNpos : (0 : ℝ) < (2 : ℝ) ^ (k + 1) := by positivity
    have hNcast : (((2 ^ (k + 1) : ℕ) : ℝ)) = (2 : ℝ) ^ (k + 1) := by push_cast; ring
    have hN1 : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
    obtain ⟨hlt, heq, hgt⟩ := hmom24 G hG hspec x (2 ^ (k + 1)) hN1
    refine ⟨fun hd2 => ?_, fun hd2 => ?_, fun hd2 => ?_⟩
    · -- below the critical exponent
      have hαval : α = 1 - d_s / 2 := by
        rw [hα, max_eq_left]; linarith
      have hbnd := hlt hd2
      rw [hNcast] at hbnd
      refine le_trans (RWRS.Support.walkLaw_goodWalk_compl_le_div hG
        (by linarith : (0:ℝ) ≤ (r : ℝ)) x k hbnd) (le_of_eq ?_)
      congr 1
      rw [mul_div_assoc, ← Real.rpow_sub hNpos]
      congr 2
      rw [hαval]
      ring
    · -- at the critical exponent
      have hαval : α = 0 := by
        rw [hα, max_eq_right]; linarith
      have hbnd := heq hd2
      rw [hNcast] at hbnd
      refine le_trans (RWRS.Support.walkLaw_goodWalk_compl_le_div hG
        (by linarith : (0:ℝ) ≤ (r : ℝ)) x k hbnd) (le_of_eq ?_)
      congr 1
      have hlognn : (0 : ℝ) ≤ 1 + Real.log ((2 : ℝ) ^ (k + 1)) := by
        have : (0 : ℝ) ≤ Real.log ((2 : ℝ) ^ (k + 1)) :=
          Real.log_nonneg (one_le_pow₀ (by norm_num))
        linarith
      have hexp : (1 + Real.log ((2 : ℝ) ^ (k + 1))) ^ ((r : ℝ) - 1)
          = (1 + Real.log ((2 : ℝ) ^ (k + 1))) ^ (r - 1) := by
        rw [← Real.rpow_natCast (1 + Real.log ((2 : ℝ) ^ (k + 1))) (r - 1)]
        congr 1
        rw [Nat.cast_sub hr]
        norm_num
      rw [hexp]
      rw [hαval]
      field_simp
      rw [← Real.rpow_add hNpos,
        show (r : ℝ) * (0 + δ) + (1 - (r : ℝ) * δ) = 1 by ring, Real.rpow_one]
    · -- above the critical exponent
      have hαval : α = 0 := by
        rw [hα, max_eq_right]; linarith
      have hbnd := hgt hd2
      rw [hNcast] at hbnd
      refine le_trans (RWRS.Support.walkLaw_goodWalk_compl_le_div hG
        (by linarith : (0:ℝ) ≤ (r : ℝ)) x k hbnd) (le_of_eq ?_)
      congr 1
      rw [hαval, mul_div_assoc]
      congr 1
      nth_rewrite 1 [show ((2 : ℝ) ^ (k + 1)) = ((2 : ℝ) ^ (k + 1)) ^ (1 : ℝ) from
        (Real.rpow_one _).symm]
      rw [← Real.rpow_sub hNpos]
      congr 1
      ring
  have hB : ∃ C : ℝ, 0 < C ∧ ∀ (x : V) (k : ℕ),
      (∫⁻ z, ENNReal.ofReal (RWRS.dyadicY G z.1 m d k z.2 ^ p) ∂(RWRS.jointLaw G ν x))
        ≤ ENNReal.ofReal (C * (2 ^ (k + 1) : ℝ) ^ p) := by
    have hcm := RWRS.Support.centeredMoment_ne_top ν (m := m) hp hmom
    refine ⟨max (RWRS.centeredMoment ν m p).toReal 1,
      lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun x k => ?_⟩
    refine le_trans (RWRS.Support.lintegral_dyadicY_rpow_le hG hd ν hp x k) ?_
    have hNnn : (0 : ℝ) ≤ ((2 : ℝ) ^ (k + 1)) ^ p :=
      Real.rpow_nonneg (by positivity) p
    conv_lhs => rw [← ENNReal.ofReal_toReal hcm]
    rw [← ENNReal.ofReal_mul hNnn]
    refine ENNReal.ofReal_le_ofReal ?_
    have hle : (RWRS.centeredMoment ν m p).toReal
        ≤ max (RWRS.centeredMoment ν m p).toReal 1 := le_max_left _ _
    nlinarith [hNnn, hle]
  refine ⟨hA, hB, ?_⟩
  intro q hq1 hqp
  obtain ⟨Cb, hCb, hbB⟩ := hB
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le zero_lt_one hq1
  have hpq : (0 : ℝ) < p - q := by linarith
  set s : ℝ := (p - q) / p with hsdef
  have hs0 : (0 : ℝ) < s := by rw [hsdef]; positivity
  have hδs : (0 : ℝ) < δ * s := by positivity
  rcases lt_trichotomy d_s 2 with hd2 | hd2 | hd2
  · -- below the critical exponent
    set r : ℕ := ⌈(q + 3 + (d_s / 2) * s) / (δ * s)⌉₊ + 1 with hrdef
    have hr1 : 1 ≤ r := by rw [hrdef]; omega
    obtain ⟨Cr, hCr, hrB⟩ := hA r hr1
    have hX : (q + 3 + (d_s / 2) * s) / (δ * s) ≤ (r : ℝ) := by
      refine le_trans (Nat.le_ceil _) ?_
      rw [hrdef]
      push_cast
      linarith
    rw [div_le_iff₀ hδs] at hX
    refine RWRS.Support.lintegral_indicator_decay hG ν hq1 hqp hCb hbB
      (Ka := Cr) (ea := d_s / 2 - (r : ℝ) * δ) hCr (fun x k => (hrB x k).1 hd2) ?_
    nlinarith [hX, hs0]
  · -- at the critical exponent
    set r : ℕ := ⌈(q + 4 + s) / (δ * s)⌉₊ + 1 with hrdef
    have hr1 : 1 ≤ r := by rw [hrdef]; omega
    have hr1R : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
    obtain ⟨Cr, hCr, hrB⟩ := hA r hr1
    set ε : ℝ := 1 / ((r : ℝ) * s + 1) with hεdef
    have hden : (0 : ℝ) < (r : ℝ) * s + 1 := by positivity
    have hε0 : (0 : ℝ) < ε := by rw [hεdef]; positivity
    have hX : (q + 4 + s) / (δ * s) ≤ (r : ℝ) := by
      refine le_trans (Nat.le_ceil _) ?_
      rw [hrdef]
      push_cast
      linarith
    rw [div_le_iff₀ hδs] at hX
    have hεr : ε * ((r : ℝ) - 1) * s ≤ 1 := by
      have heq : ε * ((r : ℝ) - 1) * s = (((r : ℝ) - 1) * s) / ((r : ℝ) * s + 1) := by
        rw [hεdef]
        field_simp
      rw [heq, div_le_one hden]
      nlinarith [hs0, hr1R]
    refine RWRS.Support.lintegral_indicator_decay hG ν hq1 hqp hCb hbB
      (Ka := Cr * (1 + 1 / ε) ^ (r - 1))
      (ea := (1 - (r : ℝ) * δ) + ε * ((r : ℝ) - 1)) (by positivity) (fun x k => ?_) ?_
    · refine le_trans ((hrB x k).2.1 hd2) (ENNReal.ofReal_le_ofReal ?_)
      exact RWRS.Support.log_power_bound hε0 hCr.le hr1 (1 - (r : ℝ) * δ) k
    · nlinarith [hX, hεr, hs0]
  · -- above the critical exponent
    set r : ℕ := ⌈(q + 3 + s) / (δ * s)⌉₊ + 1 with hrdef
    have hr1 : 1 ≤ r := by rw [hrdef]; omega
    obtain ⟨Cr, hCr, hrB⟩ := hA r hr1
    have hX : (q + 3 + s) / (δ * s) ≤ (r : ℝ) := by
      refine le_trans (Nat.le_ceil _) ?_
      rw [hrdef]
      push_cast
      linarith
    rw [div_le_iff₀ hδs] at hX
    refine RWRS.Support.lintegral_indicator_decay hG ν hq1 hqp hCb hbB
      (Ka := Cr) (ea := 1 - (r : ℝ) * δ) hCr (fun x k => (hrB x k).2.2 hd2) ?_
    nlinarith [hX, hs0]
