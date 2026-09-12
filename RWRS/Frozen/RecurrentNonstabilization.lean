/-
Theorem 6.11 of `rwrs.tex`, frozen.  `rwrs.tex:1700-1708` (label
`thm:recurrent-nonstab`):

  "For every $p\in(0,3)$ and every $d_f\in(\max(p,2),3)$, there exists a
   recurrent bounded-degree graph $G$ with $|B(o,R)|\leq CR^{d_f}$ for all
   $R\geq1$, such that for every $\mu<1$, there is an i.i.d. law bounded from
   below with $\E[\sigma]=\mu$ and $\E[|\sigma-\mu|^p]<\infty$ for which
   $u_\infty(o)=\infty$ almost surely.  Hence the divisible sandpile does not
   stabilize.  Moreover, $|B(o,r_k)|\geq cr_k^{d_f}$ along a subsequence
   $r_k\to\infty$, so $\limsup_{r\to\infty}\frac{\log|B(o,r)|}{\log r}=d_f$."

Recurrence is `g(o,o) = ∞`.  The volume bounds compare the `encard` of the
closed balls, in `[0,∞]`, with the stated powers; the subsequence is strictly
increasing, which is the paper's `r_k → ∞`.  In the last clause the cardinality
of the ball is read as a natural number; that this is its cardinality and not
the junk value of an infinite set is the separate assertion that every ball is
finite, which the local finiteness of the constructed graph supplies.
-/
import RWRS.Support.RayFinal
import RWRS.Support.RayGrowth
import RWRS.Support.RaySpikes
import RWRS.Support.ProbHelpers
import RWRS.Support.Pareto
import RWRS.Support.Explosion
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open MeasureTheory Filter
open scoped ENNReal

-- The bound `p < 3` is carried by the statement but not referred to: the proof
-- uses only `p < d_f` and `d_f < 3`, which the two hypotheses on `d_f` already
-- give, so the moment exponent is below three through the tail exponent.
set_option linter.unusedVariables false in
-- FROZEN-STATEMENT-BEGIN
theorem RWRS.Frozen.recurrentNonstabilization (p d_f : ℝ) (hp0 : 0 < p) (hp3 : p < 3)
    (hdf0 : max p 2 < d_f) (hdf3 : d_f < 3) :
    ∃ (V : Type) (G : SimpleGraph V) (hlf : G.LocallyFinite) (o : V) (d : ℕ) (C c : ℝ)
      (r : ℕ → ℕ),
      Infinite V ∧ 0 < C ∧ 0 < c ∧ StrictMono r ∧
        (haveI := hlf
        ∀ R : ℕ, (RWRS.closedBall G o R).Finite) ∧
        (haveI := hlf
        G.Connected ∧ RWRS.BoundedDegree G d ∧ RWRS.Recurrent G o ∧
          RWRS.VolumeGrowthUpper G o C d_f ∧
          (∀ k : ℕ, ENNReal.ofReal (c * (r k : ℝ) ^ d_f)
            ≤ (RWRS.closedBall G o (r k)).encard) ∧
          limsup (fun R : ℕ =>
              Real.log ((RWRS.closedBall G o R).encard.toNat) / Real.log R) atTop = d_f ∧
          ∀ μ : ℝ, μ < 1 → ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧
            (∃ b : ℝ, ∀ᵐ z ∂ν, b ≤ z) ∧ RWRS.extMean ν = (μ : EReal) ∧
            RWRS.centeredMoment ν μ p ≠ ⊤ ∧
            RWRS.iidLaw V ν {σ : V → ℝ | RWRS.odometerLimit G σ o = ⊤} = 1 ∧
            RWRS.iidLaw V ν {σ : V → ℝ | RWRS.Stabilizes G σ} = 0)
-- FROZEN-STATEMENT-END
:= by
  classical
  have hd2 : 2 < d_f := lt_of_le_of_lt (le_max_right p 2) hdf0
  have hpdf : p < d_f := lt_of_le_of_lt (le_max_left p 2) hdf0
  obtain ⟨B, α, ρ, c_loc, C_comb, m, s, hc, hdfα, hρpos, hclocpos, hCcomb, hρlt,
    hmS, hsS, hsdef, hsep, hvol, hdiv, hloc, -⟩ := RWRS.Support.exists_rec_data hd2 hdf3
  set L : ℕ → ℕ := RWRS.combLen B α with hLdef
  have hB2 : 2 ≤ B := hc.1
  have hL2 : ∀ j, 1 ≤ j → 2 ≤ L j := fun j hj => RWRS.Support.two_le_combLen hc hj
  have hL : ∀ j, 1 ≤ j → 1 ≤ L j := RWRS.Support.one_le_of_two_le hL2
  letI hlf : (RWRS.Support.rayGraph B L m s).LocallyFinite :=
    RWRS.Support.rayLocallyFinite (B := B) (L := L) (m := m) hsS
  haveI : Infinite (RWRS.Support.RayV B L m) := RWRS.Support.infinite_rayV
  have hG : (RWRS.Support.rayGraph B L m s).Connected := RWRS.Support.rayGraph_connected hL
  obtain ⟨⟨C_G, hCGpos, hup⟩, ⟨cg, hcgpos, hlowvol⟩⟩ :=
    RWRS.Support.volumeGrowth_rayGraph hc hdfα hρpos hρlt hsdef hsep hvol
  set r : ℕ → ℕ := fun k => s (k + 1) + RWRS.gadgetRadius L (m (k + 1)) with hrdef
  have hrmono : StrictMono r := by
    refine strictMono_nat_of_lt_succ fun k => ?_
    have h1 : s (k + 1) < s (k + 1 + 1) := hsS (by omega)
    have h2 : RWRS.gadgetRadius L (m (k + 1)) ≤ RWRS.gadgetRadius L (m (k + 1 + 1)) :=
      RWRS.Support.gadgetRadius_mono _ (le_of_lt (hmS (by omega)))
    simp only [hrdef]
    omega
  refine ⟨RWRS.Support.RayV B L m, RWRS.Support.rayGraph B L m s, hlf,
    RWRS.Support.rayPt B L m 0, 2 * B + 5, C_G, cg, r,
    inferInstance, hCGpos, hcgpos, hrmono,
    fun R => RWRS.Support.finite_closedBall_rayGraph hsS R,
    hG, (fun x => RWRS.Support.boundedDegree_rayGraph (B := B) (L := L) (m := m) hsS x),
    RWRS.Support.recurrent_rayGraph hL hsS, hup,
    fun k => hlowvol (k + 1) (by omega),
    RWRS.Support.limsup_growth_rayGraph hc hdfα hρpos hρlt hsdef hsep hvol hsS hmS, ?_⟩
  -- the law of the masses
  intro μ hμ
  set ν₀ : Measure ℝ := RWRS.Support.paretoLaw d_f with hν₀
  set mean : ℝ := ∫ y, y ∂ν₀ with hmean
  set cshift : ℝ := μ - mean with hcshift
  set b : ℝ := 1 - cshift with hbdef
  have hdf0 : (0 : ℝ) < d_f := by linarith
  have hmeannn : (0 : ℝ) ≤ mean := by
    rw [hmean]
    refine integral_nonneg_of_ae ?_
    filter_upwards [RWRS.Support.ae_one_le_paretoLaw hdf0] with y hy
    show (0 : ℝ) ≤ y
    linarith
  have hb : (0 : ℝ) ≤ b := by rw [hbdef, hcshift]; linarith
  obtain ⟨hlow, hmeanν, hmom⟩ :=
    RWRS.Support.shiftedParetoLaw_spec (q := d_f) (μ := μ) (p := p) (by linarith) hp0.le hpdf
  have hK : (0 : ℝ) < 2 + 2 * b * (C_comb + 1) := by nlinarith [hb, hCcomb]
  refine ⟨RWRS.Support.shiftedParetoLaw d_f μ, inferInstance, ⟨1 + cshift, hlow⟩,
    hmeanν, hmom, ?_, ?_⟩
  all_goals
    (
    have hΦm : Measurable (fun (Y : RWRS.Support.RayV B L m → ℝ)
        (v : RWRS.Support.RayV B L m) => Y v + cshift) := by
      refine measurable_pi_lambda _ fun v => ?_
      have hco : Measurable (fun Y : RWRS.Support.RayV B L m → ℝ => Y v) :=
        measurable_pi_apply v
      exact hco.add_const cshift
    have hlaw : RWRS.iidLaw (RWRS.Support.RayV B L m) (RWRS.Support.shiftedParetoLaw d_f μ)
        = (RWRS.iidLaw (RWRS.Support.RayV B L m) ν₀).map
            (fun (Y : RWRS.Support.RayV B L m → ℝ) (v : RWRS.Support.RayV B L m) =>
              Y v + cshift) := by
      rw [RWRS.Support.iidLaw_map (V := RWRS.Support.RayV B L m) ν₀
        (f := fun z : ℝ => z + cshift) (measurable_id.add_const cshift)]
      rfl
    have hae : ∀ᵐ Y ∂(RWRS.iidLaw (RWRS.Support.RayV B L m) ν₀),
        RWRS.odometerLimit (RWRS.Support.rayGraph B L m s)
          (fun v => Y v + cshift) (RWRS.Support.rayPt B L m 0) = ⊤ := by
      have hgood := RWRS.Support.good_events_rayGraph (s := s) hc hdfα hK ν₀ inferInstance
        (RWRS.Support.isPareto_paretoLaw hdf0)
        (fun k hk => le_trans hk hmS.le_apply)
      have hone := RWRS.Support.ae_all_mem (ι := RWRS.Support.RayV B L m) ν₀
        measurableSet_Ici
        (by filter_upwards [RWRS.Support.ae_one_le_paretoLaw hdf0] with y hy using hy)
      filter_upwards [hgood, hone] with Y hY1 hY2
      have hmain := RWRS.Support.odometerLimit_ray_top hB2 hL2 hsS hmS hd2 hCGpos hsep hup
        hdiv hloc b hb Y (fun v => hY2 v) ?_
      · have hfun : (fun v : RWRS.Support.RayV B L m => Y v + cshift)
            = fun v : RWRS.Support.RayV B L m => Y v - b + 1 := by
          funext v
          rw [hbdef]
          ring
        rw [hfun]
        exact hmain
      · refine Set.Infinite.mono ?_ hY1
        intro k hk
        obtain ⟨x, hx, hthr⟩ := hk
        exact ⟨x, hx, hthr⟩)
  · have hAm : MeasurableSet {σ : RWRS.Support.RayV B L m → ℝ |
        RWRS.odometerLimit (RWRS.Support.rayGraph B L m s) σ
          (RWRS.Support.rayPt B L m 0) = ⊤} :=
      (RWRS.Support.measurable_odometerLimit (G := RWRS.Support.rayGraph B L m s)
        (RWRS.Support.rayPt B L m 0)) (measurableSet_singleton ⊤)
    rw [hlaw, Measure.map_apply hΦm hAm]
    exact RWRS.Support.prob_eq_one_of_ae_mem (by filter_upwards [hae] with Y hY using hY)
  · rw [hlaw, Measure.map_apply hΦm (RWRS.Support.measurableSet_stabilizes hG)]
    refine measure_mono_null (fun Y hY => ?_) hae
    intro hcon
    exact hY (RWRS.Support.rayPt B L m 0) hcon
