/-
The finite-horizon walk average on the lattice is the integral against the law
of the trajectory.

The proof is an induction on the horizon.  One step is peeled with the head-tail
decomposition of the product measure over the naturals, and the resulting
integral over the first increment is the averaging operator.  The only thing
that needs care is integrability, and it comes for free from the same induction
run first in `[0,∞]`, where no integrability hypothesis is needed.
-/
import RWRS.Zd.Basic
import LatticeProb.Walk.Markov
import LatticeProb.Prob.InfinitePiSplit

open MeasureTheory LatticeProb
open scoped ENNReal

namespace RWRS.Support

variable {d : ℕ}

/-- The averaging operator on `[0,∞]`-valued functions. -/
noncomputable def walkOpE (d : ℕ) (ψ : Site d → ℝ≥0∞) (x : Site d) : ℝ≥0∞ :=
  (∑ i : Fin d, (ψ (x + unit i) + ψ (x - unit i))) / (2 * d)

/-- The finite-horizon walk average on `[0,∞]`-valued functionals. -/
noncomputable def walkExpE (d : ℕ) : ℕ → Site d → ((ℕ → Site d) → ℝ≥0∞) → ℝ≥0∞
  | 0, x, f => f (fun _ => x)
  | n + 1, x, f => walkOpE d (fun y => walkExpE d n y (fun Y => f (RWRS.cons x Y))) x

theorem walkExpE_ne_top (d : ℕ) [NeZero d] :
    ∀ (n : ℕ) (x : Site d) (f : (ℕ → Site d) → ℝ≥0∞), (∀ X, f X ≠ ⊤) →
      walkExpE d n x f ≠ ⊤ := by
  intro n
  induction n with
  | zero => intro x f hf; exact hf _
  | succ n ih =>
      intro x f hf
      rw [walkExpE, walkOpE]
      refine (ENNReal.div_lt_top ?_ ?_).ne
      · exact (ENNReal.sum_lt_top.mpr fun i _ =>
          ENNReal.add_lt_top.mpr ⟨(ih _ _ fun X => hf _).lt_top,
            (ih _ _ fun X => hf _).lt_top⟩).ne
      · have : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
        simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, Nat.cast_eq_zero, false_or]
        omega

theorem sitePath_consNat (x : Site d) (u : Site d) (ω : ℕ → Site d) :
    sitePath x (consNat u ω) = RWRS.cons x (sitePath (x + u) ω) := by
  funext k
  match k with
  | 0 => simp [sitePath, RWRS.cons]
  | k + 1 =>
      simp only [RWRS.cons, sitePath, Finset.sum_range_succ']
      simp only [consNat, Nat.rec_zero]
      abel

theorem lintegral_incLaw_add (d : ℕ) [NeZero d] (ψ : Site d → ℝ≥0∞) (x : Site d) :
    ∫⁻ v, ψ (x + v) ∂(incLaw d) = walkOpE d ψ x := by
  rw [incLaw, instructionLaw, lintegral_smul_measure,
    lintegral_finsetSum_measure]
  have hstep : ∀ i : Fin d,
      ∫⁻ v, ψ (x + v) ∂(Measure.dirac ((0 : Site d) + unit i)
        + Measure.dirac ((0 : Site d) - unit i))
        = ψ (x + unit i) + ψ (x - unit i) := by
    intro i
    rw [lintegral_add_measure, lintegral_dirac, lintegral_dirac]
    simp [sub_eq_add_neg]
  rw [Finset.sum_congr rfl fun i _ => hstep i, walkOpE, ENNReal.div_eq_inv_mul]
  rfl

theorem measurable_cons (x : Site d) : Measurable (RWRS.cons (V := Site d) x) := by
  refine measurable_pi_lambda _ fun k => ?_
  match k with
  | 0 => exact measurable_const
  | k + 1 => exact measurable_pi_apply k

/-- The bridge in `[0,∞]`, where no integrability hypothesis is needed. -/
theorem lintegral_siteWalkLaw (d : ℕ) [NeZero d] :
    ∀ (n : ℕ) (x : Site d) (f : (ℕ → Site d) → ℝ≥0∞), Measurable f →
      (∀ X Y : ℕ → Site d, (∀ j ≤ n, X j = Y j) → f X = f Y) →
      ∫⁻ X, f X ∂(siteWalkLaw d x) = walkExpE d n x f := by
  intro n
  induction n with
  | zero =>
      intro x f hf hdep
      rw [siteWalkLaw, lintegral_map hf (measurable_sitePath x)]
      have : ∀ ξ : ℕ → Site d, f (sitePath x ξ) = f (fun _ => x) := by
        intro ξ
        refine hdep _ _ fun j hj => ?_
        rw [Nat.le_zero.mp hj, sitePath_zero]
      simp only [this, lintegral_const, measure_univ, mul_one]
      rfl
  | succ n ih =>
      intro x f hf hdep
      have hfs : Measurable fun ξ : ℕ → Site d => f (sitePath x ξ) :=
        hf.comp (measurable_sitePath x)
      rw [siteWalkLaw, lintegral_map hf (measurable_sitePath x),
        lintegral_infinitePi_nat_head_tail (incLaw d) _ hfs]
      have hinner : ∀ u : Site d,
          ∫⁻ ω, f (sitePath x (consNat u ω)) ∂(Measure.infinitePi fun _ : ℕ => incLaw d)
            = walkExpE d n (x + u) (fun Y => f (RWRS.cons x Y)) := by
        intro u
        have hg : Measurable fun Y : ℕ → Site d => f (RWRS.cons x Y) :=
          hf.comp (measurable_cons x)
        have hgdep : ∀ Y Z : ℕ → Site d, (∀ j ≤ n, Y j = Z j) →
            f (RWRS.cons x Y) = f (RWRS.cons x Z) := by
          intro Y Z hYZ
          refine hdep _ _ fun j hj => ?_
          match j with
          | 0 => rfl
          | j + 1 => exact hYZ j (by omega)
        have := ih (x + u) (fun Y => f (RWRS.cons x Y)) hg hgdep
        rw [siteWalkLaw, lintegral_map hg (measurable_sitePath (x + u))] at this
        rw [← this]
        exact lintegral_congr fun ω => by rw [sitePath_consNat]
      simp only [hinner]
      exact lintegral_incLaw_add d (fun y => walkExpE d n y (fun Y => f (RWRS.cons x Y))) x

/-- A functional settled by the positions up to time `n` is integrable for the
law of the walk. -/
theorem integrable_of_dependsUpTo (d : ℕ) [NeZero d] (n : ℕ) (x : Site d)
    (F : (ℕ → Site d) → ℝ) (hF : Measurable F)
    (hdep : ∀ X Y : ℕ → Site d, (∀ j ≤ n, X j = Y j) → F X = F Y) :
    Integrable F (siteWalkLaw d x) := by
  refine ⟨hF.aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral]
  have h := lintegral_siteWalkLaw d n x (fun X => ‖F X‖ₑ) hF.enorm
    (fun X Y hXY => by rw [hdep X Y hXY])
  rw [h]
  exact lt_of_le_of_ne le_top (walkExpE_ne_top d n x _ fun X => enorm_lt_top.ne)

/-- **The bridge.**  For a functional settled by the positions up to time `n`,
the finite-horizon walk average is the integral against the law of the walk. -/
theorem walkExp_eq_integral_siteWalkLaw (d : ℕ) [NeZero d] :
    ∀ (n : ℕ) (x : Site d) (F : (ℕ → Site d) → ℝ), Measurable F →
      (∀ X Y : ℕ → Site d, (∀ j ≤ n, X j = Y j) → F X = F Y) →
      RWRS.walkExp (lattice d) n x F = ∫ X, F X ∂(siteWalkLaw d x) := by
  intro n
  induction n with
  | zero =>
      intro x F hF hdep
      rw [siteWalkLaw, integral_map (measurable_sitePath x).aemeasurable
        hF.aestronglyMeasurable]
      have : ∀ ξ : ℕ → Site d, F (sitePath x ξ) = F (fun _ => x) := by
        intro ξ
        refine hdep _ _ fun j hj => ?_
        rw [Nat.le_zero.mp hj, sitePath_zero]
      simp only [this, integral_const, probReal_univ, smul_eq_mul, one_mul]
      rfl
  | succ n ih =>
      intro x F hF hdep
      have hFs : Measurable fun ξ : ℕ → Site d => F (sitePath x ξ) :=
        hF.comp (measurable_sitePath x)
      have hint : Integrable F (siteWalkLaw d x) :=
        integrable_of_dependsUpTo d (n + 1) x F hF hdep
      have hint' : Integrable (fun ξ : ℕ → Site d => F (sitePath x ξ))
          (Measure.infinitePi fun _ : ℕ => incLaw d) := by
        rw [siteWalkLaw] at hint
        exact (integrable_map_measure hF.aestronglyMeasurable
          (measurable_sitePath x).aemeasurable).mp hint
      rw [siteWalkLaw, integral_map (measurable_sitePath x).aemeasurable
        hF.aestronglyMeasurable,
        integral_infinitePi_nat_head_tail (incLaw d) _ hint']
      have hinner : ∀ u : Site d,
          ∫ ω, F (sitePath x (consNat u ω)) ∂(Measure.infinitePi fun _ : ℕ => incLaw d)
            = RWRS.walkExp (lattice d) n (x + u) (fun Y => F (RWRS.cons x Y)) := by
        intro u
        have hg : Measurable fun Y : ℕ → Site d => F (RWRS.cons x Y) :=
          hF.comp (measurable_cons x)
        have hgdep : ∀ Y Z : ℕ → Site d, (∀ j ≤ n, Y j = Z j) →
            F (RWRS.cons x Y) = F (RWRS.cons x Z) := by
          intro Y Z hYZ
          refine hdep _ _ fun j hj => ?_
          match j with
          | 0 => rfl
          | j + 1 => exact hYZ j (by omega)
        have hrec := ih (x + u) (fun Y => F (RWRS.cons x Y)) hg hgdep
        rw [siteWalkLaw, integral_map (measurable_sitePath (x + u)).aemeasurable
          hg.aestronglyMeasurable] at hrec
        rw [hrec]
        exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by
          simp only []
          rw [sitePath_consNat])
      simp only [hinner]
      rw [integral_incLaw_add d (fun y =>
        RWRS.walkExp (lattice d) n y (fun Y => F (RWRS.cons x Y))) x,
        ← RWRS.Zd.walkOp_eq]
      exact (RWRS.Support.walkExp_succ n x F).symm

end RWRS.Support
