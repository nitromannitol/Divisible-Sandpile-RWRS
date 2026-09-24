/-
Proposition 6.15 of `rwrs.tex`, frozen.  `rwrs.tex:1919-1922` (label
`prop:rec-growth`), under the setup of `sec:recurrent-nonstab`
(`rwrs.tex:1805-1826`):

  "There exists $C_G>0$ such that $|B(o,r)|\leq C_Gr^{d_f}$ for every $r\geq1$.
   Moreover, along $r_k\coloneqq s_k+R_{m_k}$, one has
   $|B(o,r_k)|\geq cr_k^{d_f}$ for some $c>0$."

The graph is the one the section constructs: a ray from the root with a copy of
the gadget `H(m_k)` attached at the ray vertex `r_{s_k}`, which is
`RWRS.RayGadget`; the depths `m_k` are chosen so that the separation and volume
conditions `eq:rec-cond-sep` and `eq:rec-cond-vol` hold, with
`s_k = ⌈R_{m_k}^ρ⌉` as in `eq:rec-sk`.  Cardinalities are `encard`s in `[0,∞]`.

The exponent `ρ` is the one the section chooses in `eq:rec-rho`
(`rwrs.tex:1806-1808`): `0 < ρ < δ/(d_f+1)` with
`δ = log λ /(α log B)` of `cor:rec-loc`.  Both halves of that choice are
hypotheses here; the upper half is what makes `s_k = ⌈R_{m_k}^ρ⌉` negligible
against `R_{m_k}`, which is what the volume lower bound along `r_k` asserts.
-/
import RWRS.Support.RayGadget
import RWRS.Frozen.GadgetGeometry
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

open scoped ENNReal

-- FROZEN-STATEMENT-BEGIN
theorem RWRS.Frozen.recVolumeGrowth (B : ℕ) (α d_f ρ : ℝ) (hcond : RWRS.CombCond B α)
    (hdf : d_f = 1 + 1 / α) (hρ : 0 < ρ)
    (hρ' : ρ < Real.log (RWRS.combLambda B α) / (α * Real.log B) / (d_f + 1))
    (m s : ℕ → ℕ)
    (hs : ∀ k : ℕ, s k = ⌈(RWRS.gadgetRadius (RWRS.combLen B α) (m k) : ℝ) ^ ρ⌉₊)
    (hsep : ∀ k : ℕ, 2 ≤ k →
      s (k - 1) + RWRS.gadgetRadius (RWRS.combLen B α) (m (k - 1)) < s k)
    (hvol : ∀ k : ℕ, 2 ≤ k →
      (∑ j ∈ Finset.range k, (RWRS.gadgetSize B (RWRS.combLen B α) (m j) : ℝ))
        ≤ (s k : ℝ) ^ d_f)
    {V : Type} (G : SimpleGraph V) (o : V) (ray : ℕ → V)
    (φ : ∀ k : ℕ, RWRS.gadgetSites B (RWRS.combLen B α) (m k) → V)
    (hRG : RWRS.RayGadget G o B (RWRS.combLen B α) m s ray φ) :
    (∃ C_G : ℝ, 0 < C_G ∧ ∀ r : ℕ, 1 ≤ r →
      (RWRS.closedBall G o r).encard ≤ ENNReal.ofReal (C_G * (r : ℝ) ^ d_f)) ∧
    (∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, 1 ≤ k →
      ENNReal.ofReal (c * ((s k + RWRS.gadgetRadius (RWRS.combLen B α) (m k) : ℕ) : ℝ) ^ d_f)
        ≤ (RWRS.closedBall G o (s k + RWRS.gadgetRadius (RWRS.combLen B α) (m k))).encard)
-- FROZEN-STATEMENT-END
:= by
  classical
  have hL : ∀ j : ℕ, 1 ≤ j → 1 ≤ RWRS.combLen B α j :=
    fun j _ => RWRS.Support.combLen_pos' hcond j
  have hdfpos : 0 < d_f := RWRS.Support.df_pos hcond hdf
  have hρ1 : ρ < 1 := RWRS.Support.rho_lt_one hcond hdf hρ'
  refine ⟨⟨7 + (RWRS.gadgetSize B (RWRS.combLen B α) (m 0) : ℝ)
      + 4 * (B : ℝ) ^ 2 * (2 : ℝ) ^ (1 / α), ?_, ?_⟩, ?_⟩
  · have h1 : (0 : ℝ) ≤ (RWRS.gadgetSize B (RWRS.combLen B α) (m 0) : ℝ) :=
      Nat.cast_nonneg _
    have h2 : (0 : ℝ) < (2 : ℝ) ^ (1 / α) := Real.rpow_pos_of_pos (by norm_num) _
    have h3 : (0 : ℝ) ≤ 4 * (B : ℝ) ^ 2 * (2 : ℝ) ^ (1 / α) := by positivity
    linarith
  · intro r hr
    exact RWRS.Support.encard_closedBall_le_real hcond hdf hRG hsep hvol hr
  · obtain ⟨c_N, C_N, C_ball, hcN, -, -, -, hB, -⟩ :=
      RWRS.Frozen.gadgetGeometry B α d_f hcond hdf
    have h2df : (0 : ℝ) < (2 : ℝ) ^ d_f := Real.rpow_pos_of_pos (by norm_num) _
    refine ⟨c_N / (2 : ℝ) ^ d_f, by positivity, ?_⟩
    intro k hk
    set R := RWRS.gadgetRadius (RWRS.combLen B α) (m k) with hR
    rcases Nat.eq_zero_or_pos R with hR0 | hRpos
    · have hs0 : s k = 0 := by
        rw [hs k, ← hR, hR0]
        simp [Real.zero_rpow (ne_of_gt hρ)]
      have hzero : ((s k + R : ℕ) : ℝ) = 0 := by rw [hs0, hR0]; simp
      rw [hzero, Real.zero_rpow (ne_of_gt hdfpos)]
      simp
    · have hR1 : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hRpos
      have hsk : s k ≤ R := by
        rw [hs k, ← hR]
        have hle : (R : ℝ) ^ ρ ≤ (R : ℝ) := by
          calc (R : ℝ) ^ ρ ≤ (R : ℝ) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le hR1 hρ1.le
            _ = (R : ℝ) := Real.rpow_one _
        calc ⌈(R : ℝ) ^ ρ⌉₊ ≤ ⌈(R : ℝ)⌉₊ := Nat.ceil_le_ceil hle
          _ = R := Nat.ceil_natCast R
      have hrk : ((s k + R : ℕ) : ℝ) ≤ 2 * (R : ℝ) := by
        have : (s k : ℝ) ≤ (R : ℝ) := by exact_mod_cast hsk
        push_cast
        linarith
      have hrknn : (0 : ℝ) ≤ ((s k + R : ℕ) : ℝ) := Nat.cast_nonneg _
      have hhalf : ((s k + R : ℕ) : ℝ) / 2 ≤ (R : ℝ) := by linarith
      have hpow : (((s k + R : ℕ) : ℝ) / 2) ^ d_f ≤ (R : ℝ) ^ d_f :=
        Real.rpow_le_rpow (by positivity) hhalf hdfpos.le
      have hsplit : (((s k + R : ℕ) : ℝ) / 2) ^ d_f
          = ((s k + R : ℕ) : ℝ) ^ d_f / (2 : ℝ) ^ d_f :=
        Real.div_rpow hrknn (by norm_num) d_f
      have hgeom : c_N * (R : ℝ) ^ d_f
          ≤ (RWRS.gadgetSize B (RWRS.combLen B α) (m k) : ℝ) := (hB (m k)).1
      have hkey : c_N / (2 : ℝ) ^ d_f * ((s k + R : ℕ) : ℝ) ^ d_f
          ≤ (RWRS.gadgetSize B (RWRS.combLen B α) (m k) : ℝ) := by
        have hstep : c_N * ((((s k + R : ℕ) : ℝ) / 2) ^ d_f) ≤ c_N * (R : ℝ) ^ d_f :=
          mul_le_mul_of_nonneg_left hpow hcN.le
        rw [hsplit] at hstep
        have : c_N / (2 : ℝ) ^ d_f * ((s k + R : ℕ) : ℝ) ^ d_f
            = c_N * (((s k + R : ℕ) : ℝ) ^ d_f / (2 : ℝ) ^ d_f) := by ring
        rw [this]
        linarith
      calc ENNReal.ofReal (c_N / (2 : ℝ) ^ d_f * ((s k + R : ℕ) : ℝ) ^ d_f)
          ≤ ENNReal.ofReal ((RWRS.gadgetSize B (RWRS.combLen B α) (m k) : ℝ)) :=
            ENNReal.ofReal_le_ofReal hkey
        _ = (((RWRS.gadgetSize B (RWRS.combLen B α) (m k) : ℕ) : ℕ∞) : ℝ≥0∞) := by
            simp
        _ ≤ ((RWRS.closedBall G o (s k + R)).encard : ℝ≥0∞) :=
            ENat.toENNReal_mono
              (RWRS.Support.gadgetSize_le_encard_closedBall hRG hL k)
