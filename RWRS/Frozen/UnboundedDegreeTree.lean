/-
Lemma 6.1 of `rwrs.tex`, frozen.  `rwrs.tex:1364-1366` (label
`ex:counterexample`):

  "There exists a locally finite tree $T$ such that for every collection of
   i.i.d. random variables $(\sigma(v))_{v\in V}$ with $\E[|\sigma|]<\infty$,
   the divisible sandpile on $T$ stabilizes almost surely."

The tree of the proof is infinite, which is what makes the statement about the
divisible sandpile nontrivial, so infiniteness is part of the assertion.
`E[|σ|]<∞` is the finiteness of the first absolute moment of the marginal.
-/
import RWRS.Support.TreeGreen
import RWRS.Support.ShortClock
import RWRS.Frozen.RWInfinite
import Mathlib.Combinatorics.SimpleGraph.Acyclic

open MeasureTheory
open scoped ENNReal

-- FROZEN-STATEMENT-BEGIN
theorem RWRS.Frozen.unboundedDegreeTree :
    ∃ (V : Type) (G : SimpleGraph V) (hlf : G.LocallyFinite),
      Infinite V ∧ G.IsTree ∧
        (haveI := hlf
        ∀ ν : Measure ℝ, IsProbabilityMeasure ν → RWRS.absMoment ν 1 ≠ ⊤ →
          RWRS.iidLaw V ν {σ : V → ℝ | RWRS.Stabilizes G σ} = 1)
-- FROZEN-STATEMENT-END
:= by
  classical
  refine ⟨RWRS.Support.TreeV RWRS.Support.bTree, RWRS.Support.treeGraph RWRS.Support.bTree,
    RWRS.Support.treeLocallyFinite RWRS.Support.bTree, ?_, RWRS.Support.treeIsTree _, ?_⟩
  · exact RWRS.Support.treeInfinite RWRS.Support.bTree RWRS.Support.bTree_pos
  · intro ν hν habs
    haveI := hν
    haveI : MeasureTheory.IsProbabilityMeasure
        (RWRS.iidLaw (RWRS.Support.TreeV RWRS.Support.bTree) ν) := by
      rw [RWRS.iidLaw]; infer_instance
    haveI := RWRS.Support.countable_of_connected
      (RWRS.Support.treeConnected RWRS.Support.bTree)
    haveI := RWRS.Support.treeInfinite RWRS.Support.bTree RWRS.Support.bTree_pos
    have hG := RWRS.Support.treeConnected RWRS.Support.bTree
    have hshift : Measurable fun z : ℝ => ENNReal.ofReal (max (z - 1) 0) :=
      ((measurable_id.sub measurable_const).max measurable_const).ennreal_ofReal
    have hfin : (∫⁻ z, ENNReal.ofReal (max (z - 1) 0) ∂ν) ≠ ⊤ := by
      have hpt : ∀ z : ℝ, ENNReal.ofReal (max (z - 1) 0)
          ≤ ENNReal.ofReal (|z| ^ (1 : ℝ)) + 1 := by
        intro z
        have hz : max (z - 1) 0 ≤ |z| ^ (1 : ℝ) + 1 := by
          rw [Real.rpow_one]
          rcases le_total z 1 with h | h
          · have : max (z - 1) 0 = 0 := max_eq_right (by linarith)
            rw [this]
            have := abs_nonneg z
            linarith
          · have : max (z - 1) 0 = z - 1 := max_eq_left (by linarith)
            rw [this]
            have := le_abs_self z
            linarith
        refine le_trans (ENNReal.ofReal_le_ofReal hz) ?_
        rw [ENNReal.ofReal_add (by positivity) (by norm_num), ENNReal.ofReal_one]
      refine ne_top_of_le_ne_top (b := RWRS.absMoment ν 1 + 1) ?_ ?_
      · exact ENNReal.add_ne_top.mpr ⟨habs, ENNReal.one_ne_top⟩
      · refine le_trans (MeasureTheory.lintegral_mono hpt) ?_
        rw [MeasureTheory.lintegral_add_right _ measurable_const,
          MeasureTheory.lintegral_one, MeasureTheory.measure_univ]
        exact le_rfl
    have hbound : ∀ o : RWRS.Support.TreeV RWRS.Support.bTree,
        ∀ᵐ σ ∂(RWRS.iidLaw (RWRS.Support.TreeV RWRS.Support.bTree) ν),
          RWRS.odometerLimit (RWRS.Support.treeGraph RWRS.Support.bTree) σ o ≠ ⊤ := by
      intro o
      have hmeas : AEMeasurable (fun σ : RWRS.Support.TreeV RWRS.Support.bTree → ℝ =>
          ∑' v, RWRS.green (RWRS.Support.treeGraph RWRS.Support.bTree) o v
            * ENNReal.ofReal (max (RWRS.excess σ v) 0))
          (RWRS.iidLaw (RWRS.Support.TreeV RWRS.Support.bTree) ν) := by
        refine Measurable.aemeasurable ?_
        refine Measurable.tsum fun v => ?_
        exact ((((measurable_pi_apply v).sub measurable_const).max
          measurable_const).ennreal_ofReal).const_mul _
      have hkey : (∫⁻ σ, ∑' v, RWRS.green (RWRS.Support.treeGraph RWRS.Support.bTree) o v
            * ENNReal.ofReal (max (RWRS.excess σ v) 0)
          ∂(RWRS.iidLaw (RWRS.Support.TreeV RWRS.Support.bTree) ν)) ≠ ⊤ := by
        simp only [RWRS.excess]
        rw [RWRS.Support.lintegral_green_bound' hG o ν hν
          (fun z => ENNReal.ofReal (max (z - 1) 0)) hshift]
        exact ENNReal.mul_ne_top (RWRS.Support.tsum_green_ne_top o) hfin
      have hae := MeasureTheory.ae_lt_top' hmeas hkey
      filter_upwards [hae] with σ hσ
      rw [RWRS.Frozen.rwInfinite hG σ o]
      exact ne_of_lt (lt_of_le_of_lt
        (RWRS.Support.supStopValue_le_green hG (RWRS.excess σ) o) hσ)
    have hall : ∀ᵐ σ ∂(RWRS.iidLaw (RWRS.Support.TreeV RWRS.Support.bTree) ν),
        RWRS.Stabilizes (RWRS.Support.treeGraph RWRS.Support.bTree) σ :=
      MeasureTheory.ae_all_iff.mpr hbound
    have hnull : (RWRS.iidLaw (RWRS.Support.TreeV RWRS.Support.bTree) ν)
        {σ | RWRS.Stabilizes (RWRS.Support.treeGraph RWRS.Support.bTree) σ}ᶜ = 0 :=
      MeasureTheory.ae_iff.mp hall
    rw [← MeasureTheory.measure_univ
      (μ := RWRS.iidLaw (RWRS.Support.TreeV RWRS.Support.bTree) ν)]
    exact MeasureTheory.measure_congr (MeasureTheory.ae_eq_univ.mpr hnull)
