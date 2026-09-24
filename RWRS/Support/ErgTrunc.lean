/-
Truncating the marks from above, for part (i) of `thm:stationary-phase`.

The proof of part (i) replaces `σ` by `σ ∧ M` (`rwrs.tex:351`): the truncated
configuration still stabilizes, because the odometer is monotone in the initial
configuration, and its emissions are bounded by `M - 1`, which is what makes
dominated convergence available.  The truncated marked network is the i.i.d.
marking of the same rooted graph by the truncated mark law.
-/
import RWRS.Frozen.Recursion
import RWRS.Support.ErgPhase
import RWRS.Support.Explosion

namespace RWRS.Support

open MeasureTheory Filter Topology
open scoped ENNReal

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

/-- The odometer is monotone in the initial configuration. -/
theorem odometer_mono_config [Infinite V] (hG : G.Connected) {σ σ' : V → ℝ}
    (hσ : ∀ v, σ v ≤ σ' v) (n : ℕ) (x : V) :
    RWRS.odometer G σ n x ≤ RWRS.odometer G σ' n x := by
  induction n generalizing x with
  | zero => simp [RWRS.odometer]
  | succ n ih =>
    rw [RWRS.Frozen.recursion hG σ n x, RWRS.Frozen.recursion hG σ' n x]
    refine max_le_max ?_ le_rfl
    refine add_le_add (walkOp_mono (fun v => ih v) x) ?_
    unfold RWRS.scenery
    have hdeg : (0 : ℝ) ≤ (G.degree x : ℝ) := Nat.cast_nonneg _
    gcongr
    exact hσ x

/-- A configuration below one that stabilizes stabilizes. -/
theorem stabilizes_of_le [Infinite V] (hG : G.Connected) {σ σ' : V → ℝ}
    (hσ : ∀ v, σ v ≤ σ' v) (hstab : RWRS.Stabilizes G σ') : RWRS.Stabilizes G σ := by
  intro v
  refine ne_top_of_le_ne_top (hstab v) ?_
  refine iSup_le fun n => le_trans ?_ (le_iSup
    (fun m : ℕ => ENNReal.ofReal (RWRS.odometer G σ' m v)) n)
  exact ENNReal.ofReal_le_ofReal (odometer_mono_config hG hσ n v)

/-- When the configuration stabilizes the emission at a vertex tends to zero. -/
theorem tendsto_emission_of_stabilizes {σ : V → ℝ} (hstab : RWRS.Stabilizes G σ) (v : V) :
    Tendsto (fun k : ℕ => RWRS.emission G (RWRS.config G σ k) v) atTop (𝓝 0) := by
  have hmono : Monotone fun n => RWRS.odometer G σ n v := fun m n h => odometer_le_of_le σ h v
  have hne := hstab v
  have hlt : (⨆ n : ℕ, ENNReal.ofReal (RWRS.odometer G σ n v)) < ⊤ := lt_top_iff_ne_top.mpr hne
  have hC : ∀ n, RWRS.odometer G σ n v
      ≤ (⨆ n : ℕ, ENNReal.ofReal (RWRS.odometer G σ n v)).toReal := by
    intro n
    have h1 : ENNReal.ofReal (RWRS.odometer G σ n v)
        ≤ ⨆ m : ℕ, ENNReal.ofReal (RWRS.odometer G σ m v) :=
      le_iSup (fun m : ℕ => ENNReal.ofReal (RWRS.odometer G σ m v)) n
    have := ENNReal.toReal_mono (lt_top_iff_ne_top.mp hlt) h1
    rwa [ENNReal.toReal_ofReal (odometer_nonneg σ n v)] at this
  have hbdd : BddAbove (Set.range fun n => RWRS.odometer G σ n v) := by
    refine ⟨(⨆ n : ℕ, ENNReal.ofReal (RWRS.odometer G σ n v)).toReal, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact hC n
  have hL := tendsto_atTop_ciSup hmono hbdd
  have hshift : Tendsto (fun n => RWRS.odometer G σ (n + 1) v) atTop
      (𝓝 (⨆ n : ℕ, RWRS.odometer G σ n v)) := hL.comp (Filter.tendsto_add_atTop_nat 1)
  have hdiff := hshift.sub hL
  rw [sub_self] at hdiff
  refine hdiff.congr fun n => ?_
  rw [odometer_succ]
  ring

/-! ### Truncating the marks of a network -/

/-- The network with every mark truncated above at `M`. -/
def truncMarks (M : ℝ) (N : RWRS.Net 1) : RWRS.Net 1 :=
  (N.1, N.2.1, fun i j => min (N.2.2 i j) M)

theorem measurable_truncMarks (M : ℝ) : Measurable (truncMarks M) := by
  refine measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk ?_)
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  exact ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp
    (measurable_snd.comp measurable_snd))).min measurable_const

theorem netGraph_truncMarks (M : ℝ) (N : RWRS.Net 1) :
    RWRS.netGraph (truncMarks M N) = RWRS.netGraph N := rfl

theorem netConfig_truncMarks (M : ℝ) (N : RWRS.Net 1) (v : ℕ) :
    RWRS.netConfig (truncMarks M N) v = min (RWRS.netConfig N v) M := rfl

/-- Truncating the marks of an i.i.d. marked network is the i.i.d. marking by the
truncated mark law. -/
theorem markIid_map_truncMarks (Q : Measure (RWRS.Net 0)) [IsProbabilityMeasure Q]
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (M : ℝ) :
    (RWRS.markIid Q ν).map (truncMarks M) = RWRS.markIid Q (ν.map (fun z => min z M)) := by
  haveI := instIsProbabilityMeasureIidLaw (V := ℕ) ν
  have hg : Measurable fun (ξ : ℕ → ℝ) (i : ℕ) => min (ξ i) M :=
    measurable_pi_lambda _ fun i => (measurable_pi_apply i).min measurable_const
  rw [markIid_eq_map, markIid_eq_map, Measure.map_map (measurable_truncMarks M) measurable_markMap]
  have hcomp : truncMarks M ∘ markMap
      = markMap ∘ (Prod.map id fun (ξ : ℕ → ℝ) (i : ℕ) => min (ξ i) M) := rfl
  rw [hcomp, ← Measure.map_map measurable_markMap (measurable_id.prodMap hg),
    ← Measure.map_prod_map Q (RWRS.iidLaw ℕ ν) measurable_id hg, Measure.map_id]
  have hiid : (RWRS.iidLaw ℕ ν).map (fun (ξ : ℕ → ℝ) (i : ℕ) => min (ξ i) M)
      = RWRS.iidLaw ℕ (ν.map fun z => min z M) :=
    iidLaw_map (V := ℕ) ν (f := fun z => min z M) (measurable_id.min measurable_const)
  rw [hiid]

end RWRS.Support
