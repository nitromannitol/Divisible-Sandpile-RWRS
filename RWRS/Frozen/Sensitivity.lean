/-
Lemma 5.5 of `rwrs.tex`, frozen.  `rwrs.tex:636-648` (label
`lem:sensitivity`):

  "Let $G=(V,E)$ be an infinite, locally finite, connected graph, and fix
   vertices $o,v\in V$.  Let $\xi^{(v)}$ denote the scenery obtained by
   replacing $\xi(v)$ with an independent copy $\xi'(v)$.  Then for each
   $n\geq1$, $|u_n(o;\xi)-u_n(o;\xi^{(v)})|\leq g_n(o,v)|\xi(v)-\xi'(v)|$.
   If the walk is transient, then
   $u_\infty(o;\xi)\leq u_\infty(o;\xi^{(v)})+g(o,v)|\xi(v)-\xi'(v)|$, and the
   same bound with $\xi$ and $\xi^{(v)}$ interchanged.  In particular, if both
   values are finite, then
   $|u_\infty(o;\xi)-u_\infty(o;\xi^{(v)})|\leq g(o,v)|\xi(v)-\xi'(v)|$."

The resampled scenery is `RWRS.resample ξ v t` for the replacement value `t`,
which is the pathwise form of the statement, valid for every value of the
independent copy.  Here `u_n(o;ξ)` is the value `v_n(o) = sup_{τ≤n} E_o[S_τ]`
of the optimal stopping problem in the scenery, which `thm:RW` identifies with
the odometer, and `u_∞(o;ξ)` is its supremum over bounded stopping times, taken
in `[0,∞]`.  Transience at `o` is `g(o,o) < ∞`.
-/
import RWRS.Support.Sensitivity

open scoped ENNReal

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

-- FROZEN-STATEMENT-BEGIN
theorem RWRS.Frozen.sensitivity [Infinite V] (hG : G.Connected) (o v : V) (ξ : V → ℝ)
    (t : ℝ) :
    (∀ n : ℕ, 1 ≤ n →
      |RWRS.value G ξ n o - RWRS.value G (RWRS.resample ξ v t) n o|
        ≤ RWRS.greenTime G n o v * |ξ v - t|) ∧
    (¬ RWRS.Recurrent G o →
      (RWRS.supStopValue G ξ o
          ≤ RWRS.supStopValue G (RWRS.resample ξ v t) o
            + RWRS.green G o v * ENNReal.ofReal |ξ v - t| ∧
        RWRS.supStopValue G (RWRS.resample ξ v t) o
          ≤ RWRS.supStopValue G ξ o + RWRS.green G o v * ENNReal.ofReal |ξ v - t|) ∧
      (RWRS.supStopValue G ξ o ≠ ⊤ → RWRS.supStopValue G (RWRS.resample ξ v t) o ≠ ⊤ →
        |(RWRS.supStopValue G ξ o).toReal
            - (RWRS.supStopValue G (RWRS.resample ξ v t) o).toReal|
          ≤ (RWRS.green G o v).toReal * |ξ v - t|))
-- FROZEN-STATEMENT-END
:= by
  have hone := RWRS.Support.value_le_resample hG ξ v t
  have htwo := RWRS.Support.value_le_resample hG (RWRS.resample ξ v t) v (ξ v)
  refine ⟨fun n _ => ?_, fun hrec => ?_⟩
  · have h1 := hone n o
    have h2 := htwo n o
    rw [RWRS.Support.resample_resample, RWRS.Support.resample_self,
      abs_sub_comm t (ξ v)] at h2
    rw [abs_sub_le_iff]
    exact ⟨by linarith, by linarith⟩
  · have hgt : RWRS.green G o v ≠ ⊤ :=
      RWRS.Support.green_ne_top_of_not_recurrent hG hrec v
    have h1 := RWRS.Support.supStopValue_le_resample hG ξ v t o
    have h2 := RWRS.Support.supStopValue_le_resample hG (RWRS.resample ξ v t) v (ξ v) o
    rw [RWRS.Support.resample_resample, RWRS.Support.resample_self,
      abs_sub_comm t (ξ v)] at h2
    refine ⟨⟨h1, h2⟩, fun hA hB => ?_⟩
    set c : ℝ≥0∞ := RWRS.green G o v * ENNReal.ofReal |ξ v - t| with hc
    have hcne : c ≠ ⊤ := ENNReal.mul_ne_top hgt ENNReal.ofReal_ne_top
    have hcR : c.toReal = (RWRS.green G o v).toReal * |ξ v - t| := by
      rw [hc, ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _)]
    have k1 : (RWRS.supStopValue G ξ o).toReal
        ≤ (RWRS.supStopValue G (RWRS.resample ξ v t) o).toReal + c.toReal := by
      rw [← ENNReal.toReal_add hB hcne]
      exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hB, hcne⟩) h1
    have k2 : (RWRS.supStopValue G (RWRS.resample ξ v t) o).toReal
        ≤ (RWRS.supStopValue G ξ o).toReal + c.toReal := by
      rw [← ENNReal.toReal_add hA hcne]
      exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hA, hcne⟩) h2
    rw [abs_sub_le_iff, ← hcR]
    exact ⟨by linarith, by linarith⟩
