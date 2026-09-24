/-
Lemma 6.9 of `rwrs.tex`, frozen.  `rwrs.tex:1661-1663` (label `lem:tr-good`),
under the setup of `sec:transient-nonstab` (`rwrs.tex:1580-1600`):

  "Almost surely, for all sufficiently large $n$, at least one level-$n$ pipe is
   good."

A level-`n` pipe is indexed by a word `w` of length `n`, and it is good when
some vertex in its first half, `RWRS.combFirstHalf`, carries a Pareto variable
of size at least `K L_n`.  The parameters are those the section fixes: `q` with
`max(p,1) < q < 3`, `α` with `1/2 < α < min(1, 1/(q-1))`, the Pareto tail
`P(Y ≥ t) = t^{-q}`, and the constant `K` of `prop:comb-estimates`(d).
-/
import RWRS.Support.TrGood

open MeasureTheory Filter
open scoped ENNReal

-- FROZEN-STATEMENT-BEGIN
theorem RWRS.Frozen.transientGoodPipes (B : ℕ) (α q K : ℝ) (hcond : RWRS.CombCond B α)
    (hq : 1 < q) (hq3 : q < 3) (hα : α < 1 / (q - 1)) (hK : 0 < K)
    (ν : Measure ℝ) (hν : IsProbabilityMeasure ν) (hpar : RWRS.IsPareto ν q) :
    ∀ᵐ Y ∂(RWRS.iidLaw (List (Fin B) × ℕ) ν), ∀ᶠ n : ℕ in atTop,
      ∃ w : List (Fin B), w.length = n ∧
        ∃ v ∈ RWRS.combFirstHalf B (RWRS.combLen B α) n w,
          K * (RWRS.combLen B α n : ℝ) ≤ Y v
-- FROZEN-STATEMENT-END
:= by
  classical
  haveI := hν
  haveI : IsProbabilityMeasure (RWRS.iidLaw (List (Fin B) × ℕ) ν) := by
    rw [RWRS.iidLaw]; infer_instance
  -- `q < 3` is what fixes the moment of the marginal in `thm:transient-nonstab`;
  -- the good-pipe estimate itself uses only `1 < q` and `α(q-1) < 1`.
  have _hq3 : q < 3 := hq3
  have hqpos : (0 : ℝ) < q := by linarith
  set γ : ℝ := (B : ℝ) ^ (1 - α * (q - 1)) with hγdef
  have hγ1 : 1 < γ := RWRS.Support.one_lt_base_geom hcond hq hα
  set c₀ : ℝ := K ^ (-q) / 4 with hc₀def
  have hc₀ : 0 < c₀ := by
    have : (0 : ℝ) < K ^ (-q) := Real.rpow_pos_of_pos hK _
    rw [hc₀def]; linarith
  set S : ℕ → Finset (List (Fin B) × ℕ) :=
    fun n => RWRS.Support.firstHalfFinset B (RWRS.combLen B α) (n + 1) with hSdef
  set bad : ℕ → Set ((List (Fin B) × ℕ) → ℝ) :=
    fun n => {Y | ∀ v ∈ S n, Y v < K * (RWRS.combLen B α (n + 1) : ℝ)} with hbaddef
  -- the probability that no site of level `n+1` is good
  have hbound : ∀ n : ℕ, RWRS.iidLaw (List (Fin B) × ℕ) ν (bad n)
      ≤ ENNReal.ofReal (Real.exp (-(c₀ * γ ^ (n + 1)))) := by
    intro n
    refine RWRS.Support.measure_all_lt_le ν hqpos hpar (S n)
      (RWRS.Support.card_firstHalfFinset_pos hcond (by omega)) ?_
    exact RWRS.Support.mean_good_ge hcond hq hK (by omega)
  -- the bound is summable
  have hsummable : Summable (fun n : ℕ => Real.exp (-(c₀ * γ ^ (n + 1)))) := by
    refine Summable.of_nonneg_of_le (fun n => (Real.exp_pos _).le) (fun n => ?_)
      (RWRS.Support.summable_exp_neg_geom hc₀ hγ1)
    refine Real.exp_le_exp.2 ?_
    have hpow : γ ^ n ≤ γ ^ (n + 1) :=
      pow_le_pow_right₀ (le_of_lt hγ1) (by omega)
    nlinarith
  have hne : (∑' n : ℕ, RWRS.iidLaw (List (Fin B) × ℕ) ν (bad n)) ≠ ⊤ := by
    have h1 : (∑' n : ℕ, RWRS.iidLaw (List (Fin B) × ℕ) ν (bad n))
        ≤ ∑' n : ℕ, ENNReal.ofReal (Real.exp (-(c₀ * γ ^ (n + 1)))) :=
      ENNReal.tsum_le_tsum hbound
    have h2 : (∑' n : ℕ, ENNReal.ofReal (Real.exp (-(c₀ * γ ^ (n + 1)))))
        = ENNReal.ofReal (∑' n : ℕ, Real.exp (-(c₀ * γ ^ (n + 1)))) :=
      (ENNReal.ofReal_tsum_of_nonneg (fun n => (Real.exp_pos _).le) hsummable).symm
    rw [h2] at h1
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top h1
  have hae := MeasureTheory.ae_eventually_notMem hne
  filter_upwards [hae] with Y hY
  rw [Filter.eventually_atTop] at hY ⊢
  obtain ⟨N, hN⟩ := hY
  refine ⟨N + 1, fun m hm => ?_⟩
  have hmem := hN (m - 1) (by omega)
  simp only [hbaddef, hSdef, Set.mem_setOf_eq, not_forall, not_lt, exists_prop] at hmem
  rw [show m - 1 + 1 = m by omega] at hmem
  obtain ⟨v, hv, hle⟩ := hmem
  obtain ⟨hlen, h1, h2⟩ := RWRS.Support.firstHalf_of_mem hv
  exact ⟨v.1, hlen, v, ⟨rfl, h1, h2⟩, hle⟩
