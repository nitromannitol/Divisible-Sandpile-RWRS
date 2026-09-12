/-
Lemma 6.16 of `rwrs.tex`, frozen.  `rwrs.tex:1946-1948` (label `lem:rec-good`),
under the setup of `sec:recurrent-nonstab` (`rwrs.tex:1928-1944`):

  "There exists $\eta>0$ such that $\P(E_k)\geq\eta$ for every $k\geq1$.  The
   events $E_1,E_2,\ldots$ are independent.  In particular, infinitely many
   $E_k$ occur almost surely."

`A_k` is the set of vertices in the first half of every terminal pipe of the
gadget `H(m_k)`, sitting inside the global graph; the two properties of it that
the setup records are that the `A_k` are pairwise disjoint, since different
gadgets have disjoint vertex sets, and that
`|A_k| ≥ B^{m_k}L_{m_k}/4` (`eq:rec-Ak`).  The statement is made for any family
with those two properties, and `E_k` is the event that some vertex of `A_k`
carries a Pareto variable of size at least `K L_{m_k}`.
-/
import RWRS.Support.GoodEvents
import Mathlib.Probability.Independence.Basic

open MeasureTheory
open scoped ENNReal

-- FROZEN-STATEMENT-BEGIN
theorem RWRS.Frozen.recGoodEvents (B : ℕ) (α d_f K : ℝ) (hcond : RWRS.CombCond B α)
    (hdf : d_f = 1 + 1 / α) (hK : 0 < K)
    (ν : Measure ℝ) (hν : IsProbabilityMeasure ν) (hpar : RWRS.IsPareto ν d_f)
    {V : Type} [Countable V] (m : ℕ → ℕ) (A : ℕ → Set V)
    (hdisj : Pairwise (Function.onFun Disjoint A))
    (hcard : ∀ k : ℕ, 1 ≤ k →
      ENNReal.ofReal ((B : ℝ) ^ m k * (RWRS.combLen B α (m k) : ℝ) / 4) ≤ (A k).encard) :
    ∃ η : ℝ, 0 < η ∧
      (∀ k : ℕ, 1 ≤ k → ENNReal.ofReal η ≤ RWRS.iidLaw V ν
        {Y : V → ℝ | ∃ v ∈ A k, K * (RWRS.combLen B α (m k) : ℝ) ≤ Y v}) ∧
      ProbabilityTheory.iIndepSet
        (fun k : ℕ => {Y : V → ℝ | ∃ v ∈ A k, K * (RWRS.combLen B α (m k) : ℝ) ≤ Y v})
        (RWRS.iidLaw V ν) ∧
      ∀ᵐ Y ∂(RWRS.iidLaw V ν),
        {k : ℕ | ∃ v ∈ A k, K * (RWRS.combLen B α (m k) : ℝ) ≤ Y v}.Infinite
-- FROZEN-STATEMENT-END
:= by
  classical
  haveI := hν
  haveI : IsProbabilityMeasure (RWRS.iidLaw V ν) := by rw [RWRS.iidLaw]; infer_instance
  set c : ℕ → ℝ := fun k => K * (RWRS.combLen B α (m k) : ℝ) with hcdef
  set E : ℕ → Set (V → ℝ) := fun k => {Y : V → ℝ | ∃ v ∈ A k, c k ≤ Y v} with hEdef
  have hdfpos : 0 < d_f := RWRS.Support.df_pos hcond hdf
  set θ : ℝ := min (K ^ (-d_f) / 4) 1 with hθdef
  have hθpos : 0 < θ := lt_min (by positivity) one_pos
  have hηpos : 0 < 1 - Real.exp (-θ) := by
    have : Real.exp (-θ) < 1 := Real.exp_lt_one_iff.2 (by linarith)
    linarith
  -- the uniform lower bound on the good events
  have hlow : ∀ k : ℕ, 1 ≤ k →
      ENNReal.ofReal (1 - Real.exp (-θ)) ≤ RWRS.iidLaw V ν (E k) := by
    intro k hk
    obtain ⟨S, hSsub, hScard⟩ := RWRS.Support.exists_finset_card_ge (hcard k hk)
    have hLpos : (0 : ℝ) < (RWRS.combLen B α (m k) : ℝ) := by
      exact_mod_cast RWRS.Support.combLen_pos' hcond (m k)
    have hBpos : (0 : ℝ) < (B : ℝ) ^ m k := by
      have := RWRS.Support.cast_B_pos hcond; positivity
    have hxpos : (0 : ℝ) < (B : ℝ) ^ m k * (RWRS.combLen B α (m k) : ℝ) / 4 := by positivity
    have hS1 : (1 : ℝ) ≤ (S.card : ℝ) := by
      have hpos : (0 : ℝ) < (S.card : ℝ) := lt_of_lt_of_le hxpos hScard
      have : 0 < S.card := by exact_mod_cast hpos
      exact_mod_cast this
    set c' : ℝ := max (c k) 1 with hc'def
    have hc'1 : (1 : ℝ) ≤ c' := le_max_right _ _
    have hmean : θ ≤ (S.card : ℝ) * c' ^ (-d_f) := by
      rcases le_or_gt 1 (c k) with h1 | h1
      · have hcc : c' = c k := max_eq_left h1
        rw [hcc]
        exact le_trans (min_le_left _ _)
          (RWRS.Support.mean_spikes_ge hcond hdf hK hScard)
      · have hcc : c' = 1 := max_eq_right h1.le
        rw [hcc, Real.one_rpow, mul_one]
        exact le_trans (min_le_right _ _) hS1
    refine le_trans
      (RWRS.Support.le_measure_spike_const ν hdfpos hpar S hc'1 hmean) (measure_mono ?_)
    rintro Y ⟨v, hv, hle⟩
    exact ⟨v, hSsub (by simpa using hv), le_trans (le_max_left _ _) hle⟩
  -- independence: different gadgets read disjoint blocks of coordinates
  have hindep : ProbabilityTheory.iIndepSet E (RWRS.iidLaw V ν) := by
    rw [RWRS.iidLaw]
    exact LatticeProb.iIndepSet_of_pairwise_disjoint ν A hdisj E
      fun k => RWRS.Support.measurableSet_comap_spike (A k) (c k)
  have hmeas : ∀ k : ℕ, MeasurableSet (E k) :=
    fun k => RWRS.Support.measurableSet_spike (A k) (c k)
  refine ⟨1 - Real.exp (-θ), hηpos, hlow, hindep, ?_⟩
  -- the second Borel-Cantelli lemma
  have hsum : ∑' k : ℕ, RWRS.iidLaw V ν (E k) = ⊤ :=
    RWRS.Support.tsum_eq_top_of_const_le
      (by simp [ENNReal.ofReal_eq_zero]; linarith) hlow
  have hlim := ProbabilityTheory.measure_limsup_eq_one hmeas hindep hsum
  rw [MeasureTheory.ae_iff]
  refine measure_mono_null ?_
    ((MeasureTheory.prob_compl_eq_zero_iff
      (MeasurableSet.measurableSet_limsup hmeas)).2 hlim)
  intro Y hY hmem
  exact hY (RWRS.Support.infinite_of_mem_limsup hmem)
