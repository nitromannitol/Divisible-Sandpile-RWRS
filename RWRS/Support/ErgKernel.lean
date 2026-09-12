/-
The conditional law of the rooted graph given the rerooting-invariant events,
integrated against a general non-negative function.

The ergodic decomposition supplies the kernel `K` only through the identity
`∫⁻_{B} K N A dQ = Q (A ∩ B)` on events `A`.  Everything downstream integrates a
function of the rooted graph against `K N`, so the identity is extended here
from indicators to every non-negative measurable function by the monotone class
argument, carrying the measurability of `N ↦ ∫⁻ f dK N` for the σ-algebra of
rerooting-invariant events along with it.
-/
import RWRS.Support.ErgGraph

namespace RWRS.Support

open MeasureTheory
open scoped ENNReal

/-- The conditional-law identity of the ergodic decomposition for a general
non-negative measurable function, with the invariant measurability of the
conditional integral. -/
theorem kernel_lintegral (Q : Measure (RWRS.Net 0)) (K : RWRS.Net 0 → Measure (RWRS.Net 0))
    (hKmeas : ∀ A : Set (RWRS.Net 0), MeasurableSet A →
      Measurable[RWRS.invariantSigma 0] fun N => K N A)
    (hKid : ∀ A : Set (RWRS.Net 0), MeasurableSet A →
      ∀ B : Set (RWRS.Net 0), MeasurableSet[RWRS.invariantSigma 0] B →
        (∫⁻ N in B, K N A ∂Q) = Q (A ∩ B))
    {f : RWRS.Net 0 → ℝ≥0∞} (hf : Measurable f) :
    Measurable[RWRS.invariantSigma 0] (fun N => ∫⁻ M, f M ∂(K N)) ∧
      ∀ B : Set (RWRS.Net 0), MeasurableSet[RWRS.invariantSigma 0] B →
        (∫⁻ N in B, (∫⁻ M, f M ∂(K N)) ∂Q) = ∫⁻ N in B, f N ∂Q := by
  refine Measurable.ennreal_induction (motive := fun f =>
    Measurable[RWRS.invariantSigma 0] (fun N => ∫⁻ M, f M ∂(K N)) ∧
      ∀ B : Set (RWRS.Net 0), MeasurableSet[RWRS.invariantSigma 0] B →
        (∫⁻ N in B, (∫⁻ M, f M ∂(K N)) ∂Q) = ∫⁻ N in B, f N ∂Q) ?_ ?_ ?_ hf
  · -- indicators
    intro c s hs
    have hval : ∀ N, (∫⁻ M, s.indicator (fun _ => c) M ∂(K N)) = c * K N s := fun N =>
      lintegral_indicator_const hs c
    have hms : Measurable fun N => K N s := (hKmeas s hs).mono invariantSigma_le le_rfl
    constructor
    · simp only [hval]
      exact (hKmeas s hs).const_mul c
    · intro B hB
      simp only [hval]
      rw [lintegral_const_mul c hms, hKid s hs B hB, lintegral_indicator_const hs c,
        Measure.restrict_apply hs]
  · -- sums
    rintro f g _ hfm hgm ⟨hfmeas, hfid⟩ ⟨hgmeas, hgid⟩
    have hval : ∀ N, (∫⁻ M, (f + g) M ∂(K N))
        = (∫⁻ M, f M ∂(K N)) + ∫⁻ M, g M ∂(K N) := fun N => by
      simpa using lintegral_add_left (μ := K N) hfm g
    constructor
    · simp only [hval]
      exact hfmeas.add hgmeas
    · intro B hB
      simp only [hval]
      rw [lintegral_add_left (hfmeas.mono invariantSigma_le le_rfl), hfid B hB, hgid B hB,
        ← lintegral_add_left hfm]
      rfl
  · -- monotone limits
    rintro f hfm hmono hind
    have hval : ∀ N, (∫⁻ M, (⨆ n, f n M) ∂(K N)) = ⨆ n, ∫⁻ M, f n M ∂(K N) := fun N =>
      lintegral_iSup hfm hmono
    have hmono' : Monotone fun n N => ∫⁻ M, f n M ∂(K N) := by
      intro i j hij N
      exact lintegral_mono fun M => hmono hij M
    constructor
    · simp only [hval]
      exact Measurable.iSup fun n => (hind n).1
    · intro B hB
      simp only [hval]
      rw [lintegral_iSup (fun n => ((hind n).1.mono invariantSigma_le le_rfl)) hmono',
        lintegral_iSup hfm hmono]
      exact iSup_congr fun n => (hind n).2 B hB

end RWRS.Support
