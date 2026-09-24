/-
The degree-weighted mass of an i.i.d. marked network, and the emission bound
under a truncated configuration.

Part (i) of `thm:stationary-phase` uses three elementary facts about the mass:
the identity `a = min(a,1) + (a-1)⁺` bounds the mass at the root after `k`
rounds by `1/deg(ρ)` plus the emission (`rwrs.tex:354`); under a configuration
bounded by `M` every emission of every round is at most `M - 1`
(`rwrs.tex:351-353`); and, the marks being sampled independently of the rooted
graph, a function of the mark at the root times a function of the rooted graph
integrates as the product of the two integrals (`rwrs.tex:357`).
-/
import RWRS.Support.Toppling
import RWRS.Support.Odometer
import RWRS.Support.ErgCondLaw
import RWRS.Support.Critical

namespace RWRS.Support

open MeasureTheory
open scoped ENNReal

theorem netWeightedMassAt_le (N : RWRS.Net 1) (k : ℕ) :
    RWRS.netWeightedMassAt N k
      ≤ 1 / ((RWRS.netGraph N).degree (RWRS.netRoot N) : ℝ) + netEmission N k := by
  set d : ℝ := ((RWRS.netGraph N).degree (RWRS.netRoot N) : ℝ) with hd
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  set a : ℝ := RWRS.config (RWRS.netGraph N) (RWRS.netConfig N) k (RWRS.netRoot N) with ha
  have hsplit : a ≤ 1 + max (a - 1) 0 := by
    rcases le_total a 1 with h | h
    · rw [max_eq_right (by linarith)]; linarith
    · rw [max_eq_left (by linarith)]; linarith
  rw [RWRS.netWeightedMassAt, netEmission, RWRS.emission, ← hd, ← ha]
  rw [show (1 : ℝ) / d + max (a - 1) 0 / d = (1 + max (a - 1) 0) / d from by ring]
  gcongr

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

theorem emission_config_le [Infinite V] (hG : G.Connected) {σ : V → ℝ} {M : ℝ} (hM : 1 ≤ M)
    (hσ : ∀ v, σ v ≤ M) (k : ℕ) (v : V) :
    RWRS.emission G (RWRS.config G σ k) v ≤ M - 1 := by
  have hdpos : ∀ w : V, (1 : ℝ) ≤ (G.degree w : ℝ) := fun w => by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (degree_pos hG w))
  have hM0 : (0 : ℝ) ≤ M - 1 := by linarith
  induction k generalizing v with
  | zero =>
    have hc : RWRS.config G σ 0 = σ := rfl
    rw [RWRS.emission, hc, div_le_iff₀ (by linarith [hdpos v])]
    have h1 : max (σ v - 1) 0 ≤ M - 1 := max_le (by linarith [hσ v]) hM0
    nlinarith [hdpos v]
  | succ k ih =>
    rw [RWRS.emission, config_succ, RWRS.topple, div_le_iff₀ (by linarith [hdpos v])]
    have hsum : ∑ w ∈ G.neighborFinset v, RWRS.emission G (RWRS.config G σ k) w
        ≤ (G.degree v : ℝ) * (M - 1) := by
      calc ∑ w ∈ G.neighborFinset v, RWRS.emission G (RWRS.config G σ k) w
          ≤ ∑ _w ∈ G.neighborFinset v, (M - 1) := Finset.sum_le_sum fun w _ => ih w
        _ = (G.degree v : ℝ) * (M - 1) := by
            rw [Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree, nsmul_eq_mul]
    have hmin : min (RWRS.config G σ k v) 1 ≤ 1 := min_le_right _ _
    refine max_le (by nlinarith) (by nlinarith [hdpos v])


/-- The mark at the root is independent of the rooted graph: a function of it
times a function of the rooted graph integrates as the product. -/
theorem lintegral_markIid_mark_mul (Q : Measure (RWRS.Net 0)) [IsProbabilityMeasure Q]
    (ν : Measure ℝ) [IsProbabilityMeasure ν] {f : ℝ → ℝ≥0∞} (hf : Measurable f)
    {w : RWRS.Net 0 → ℝ≥0∞} (hw : Measurable w) :
    (∫⁻ M, f (RWRS.netConfig M (RWRS.netRoot M)) * w (RWRS.forgetMarks M) ∂(RWRS.markIid Q ν))
      = (∫⁻ z, f z ∂ν) * ∫⁻ N, w N ∂Q := by
  haveI := instIsProbabilityMeasureIidLaw (V := ℕ) ν
  have hmeasroot : Measurable fun M : RWRS.Net 1 => RWRS.netConfig M (RWRS.netRoot M) := by
    have hpair : Measurable fun q : RWRS.Net 1 × ℕ => RWRS.netConfig q.1 q.2 :=
      measurable_from_prod_countable_left fun r =>
        (measurable_pi_apply (0 : Fin 1)).comp
          ((measurable_pi_apply r).comp (measurable_snd.comp measurable_snd))
    exact hpair.comp (measurable_id.prodMk measurable_netRoot)
  have hmeas : Measurable fun M : RWRS.Net 1 =>
      f (RWRS.netConfig M (RWRS.netRoot M)) * w (RWRS.forgetMarks M) :=
    (hf.comp hmeasroot).mul (hw.comp measurable_forgetMarks)
  rw [lintegral_markIid Q ν hmeas]
  have hstep : ∀ N : RWRS.Net 0,
      markAvg ν (fun M => f (RWRS.netConfig M (RWRS.netRoot M)) * w (RWRS.forgetMarks M)) N
        = (∫⁻ z, f z ∂ν) * w N := by
    intro N
    have hpt : ∀ ξ : ℕ → ℝ,
        f (RWRS.netConfig (markMap (N, ξ)) (RWRS.netRoot (markMap (N, ξ))))
            * w (RWRS.forgetMarks (markMap (N, ξ)))
          = f (ξ (RWRS.netRoot N)) * w N := by
      intro ξ
      rw [forgetMarks_markMap]
      rfl
    have hcoord : (∫⁻ ξ : ℕ → ℝ, f (ξ (RWRS.netRoot N)) ∂(RWRS.iidLaw ℕ ν)) = ∫⁻ z, f z ∂ν := by
      conv_rhs => rw [← map_eval_iidLaw (V := ℕ) ν (RWRS.netRoot N)]
      exact (lintegral_map hf (measurable_pi_apply _)).symm
    calc markAvg ν (fun M => f (RWRS.netConfig M (RWRS.netRoot M)) * w (RWRS.forgetMarks M)) N
        = ∫⁻ ξ : ℕ → ℝ, f (ξ (RWRS.netRoot N)) * w N ∂(RWRS.iidLaw ℕ ν) := by
          unfold markAvg
          exact lintegral_congr fun ξ => hpt ξ
      _ = (∫⁻ ξ : ℕ → ℝ, f (ξ (RWRS.netRoot N)) ∂(RWRS.iidLaw ℕ ν)) * w N :=
          lintegral_mul_const _ (hf.comp (measurable_pi_apply _))
      _ = (∫⁻ z, f z ∂ν) * w N := by rw [hcoord]
  simp only [hstep]
  exact lintegral_const_mul _ hw

end RWRS.Support
