/-
The exit payoff `x ↦ E_x[S_{τ_C}]` of `prop:finite-vol`, and the identification
of the finite-volume value with it on the active component.

The exit payoff satisfies the same first-step identity as the value `v_K` does
on the active component, and it vanishes off `C`, exactly where the value
vanishes when `C` is a connected component of the active set.  The difference
is therefore harmonic on `C` and vanishes off it, so the maximum principle for
a network Laplacian makes it zero.
-/
import RWRS.Support.Bellman
import LatticeProb.Network.MaximumPrinciple

namespace RWRS.Support

open MeasureTheory LatticeProb.Graph LatticeProb.Network
open scoped ENNReal

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]
variable [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] [DecidableEq V]

/-! ### The payoff at the exit time -/

omit [DecidableEq V] in
/-- The payoff at the exit time of a set is measurable. -/
theorem measurable_payoffAtExit (ξ : V → ℝ) (C : Set V) :
    Measurable (fun X : ℕ → V => RWRS.payoffAtExit G ξ C X) := by
  have h1 : Measurable (fun X : ℕ → V => (LatticeProb.Graph.exitTime C X).toNat) :=
    LatticeProb.Graph.measurable_exitNat C
  have h2 : Measurable (fun p : (ℕ → V) × ℕ => RWRS.payoff G ξ p.2 p.1) :=
    measurable_from_prod_countable_left fun n => measurable_payoff ξ n
  exact h2.comp (measurable_id.prodMk h1)

/-- The payoff at the exit time of a finite set the walk escapes is integrable. -/
theorem integrable_payoffAtExit (hdeg : ∀ v : V, 0 < G.degree v) (ξ : V → ℝ) (C : Finset V)
    (hesc : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ (C : Set V)) (x : V) :
    Integrable (fun X => RWRS.payoffAtExit G ξ (C : Set V) X)
      (LatticeProb.Graph.walkLaw G x) := by
  classical
  have hbdd : Integrable
      (fun X => stepBound G ξ C
        * (((LatticeProb.Graph.exitTime (C : Set V) X).toNat : ℕ) : ℝ))
      (LatticeProb.Graph.walkLaw G x) :=
    (LatticeProb.Graph.integrable_exitNat hdeg C hesc x).const_mul _
  have hfin := LatticeProb.Graph.ae_exitTime_ne_top hdeg C hesc x
  refine Integrable.mono' hbdd (measurable_payoffAtExit ξ (C : Set V)).aestronglyMeasurable ?_
  filter_upwards [hfin] with X hX
  obtain ⟨-, hin⟩ := exitNat_spec hX
  have h1 := abs_payoff_le (G := G) (ξ := ξ) (C := C)
    (n := (LatticeProb.Graph.exitTime (C : Set V) X).toNat) (X := X) hin
  rw [Real.norm_eq_abs, RWRS.payoffAtExit, exitTime_eq_lib, mul_comm]
  exact h1

/-- `x ↦ E_x[S_{τ_C}]`, the exit payoff of `prop:finite-vol`. -/
noncomputable def exitValue (G : SimpleGraph V) [G.LocallyFinite]
    (ξ : V → ℝ) (C : Set V) (x : V) : ℝ :=
  ∫ X, RWRS.payoffAtExit G ξ C X ∂(LatticeProb.Graph.walkLaw G x)

omit [DecidableEq V] in
/-- The exit payoff vanishes off `C`, where the exit time is zero. -/
theorem exitValue_eq_zero_of_notMem (ξ : V → ℝ) (C : Set V) {x : V} (hx : x ∉ C) :
    exitValue G ξ C x = 0 := by
  have hstart := LatticeProb.Graph.ae_walkLaw_start (G := G) x
  have hae : ∀ᵐ X ∂(LatticeProb.Graph.walkLaw G x), RWRS.payoffAtExit G ξ C X = 0 := by
    filter_upwards [hstart] with X hX
    have h0 : LatticeProb.Graph.exitTime C X = 0 :=
      LatticeProb.Graph.exitTime_eq_natCast_of C (n := 0) (by rw [hX]; exact hx) (by omega)
    have hz : (LatticeProb.Graph.exitTime C X).toNat = 0 := by rw [h0]; rfl
    simp only [RWRS.payoffAtExit, exitTime_eq_lib, hz]
    rfl
  rw [exitValue, integral_congr_ae hae, integral_zero]

/-- **The first-step identity for the exit payoff.**  Inside `C` the walk makes
one step and starts again, so the exit payoff solves the same equation the value
does on the active component. -/
theorem exitValue_firstStep (hdeg : ∀ v : V, 0 < G.degree v) (ξ : V → ℝ) (C : Finset V)
    (hesc : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ (C : Set V))
    {x : V} (hx : x ∈ C) :
    exitValue G ξ (C : Set V) x
      = ξ x / G.degree x
        + (G.degree x : ℝ)⁻¹ * ∑ y ∈ G.neighborFinset x, exitValue G ξ (C : Set V) y := by
  classical
  have hxC : x ∈ (C : Set V) := by exact_mod_cast hx
  have hfs := integral_walkLaw_firstStep' (G := G) x (hdeg x)
    (fun X => RWRS.payoffAtExit G ξ (C : Set V) X) (measurable_payoffAtExit ξ _)
    (integrable_payoffAtExit hdeg ξ C hesc x)
  have hterm : ∀ y ∈ G.neighborFinset x,
      ∫ X, RWRS.payoffAtExit G ξ (C : Set V) (LatticeProb.Graph.cons x X)
          ∂(LatticeProb.Graph.walkLaw G y)
        = ξ x / G.degree x + exitValue G ξ (C : Set V) y := by
    intro y _
    have hfin := LatticeProb.Graph.ae_exitTime_ne_top hdeg C hesc y
    have hae : ∀ᵐ X ∂(LatticeProb.Graph.walkLaw G y),
        RWRS.payoffAtExit G ξ (C : Set V) (LatticeProb.Graph.cons x X)
          = ξ x / G.degree x + RWRS.payoffAtExit G ξ (C : Set V) X := by
      filter_upwards [hfin] with X hX
      rw [← cons_eq_lib]
      obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hX
      have hcons : LatticeProb.Graph.exitTime (C : Set V) (RWRS.cons x X)
          = (n : ℕ∞) + 1 := by rw [exitTime_cons_of_mem hxC X, ← hn]
      have htn : (LatticeProb.Graph.exitTime (C : Set V) (RWRS.cons x X)).toNat = n + 1 := by
        rw [hcons]
        rw [show ((n : ℕ∞) + 1) = ((n + 1 : ℕ) : ℕ∞) by push_cast; ring]
        simp
      have htX : (LatticeProb.Graph.exitTime (C : Set V) X).toNat = n := by rw [← hn]; simp
      simp only [RWRS.payoffAtExit, exitTime_eq_lib, htn, htX]
      rw [payoff_cons]
    rw [integral_congr_ae hae,
      integral_add (integrable_const _) (integrable_payoffAtExit hdeg ξ C hesc y)]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    rfl
  rw [exitValue, hfs, Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_const,
    SimpleGraph.card_neighborFinset_eq_degree, nsmul_eq_mul]
  have hdx : (G.degree x : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (hdeg x).ne'
  field_simp

/-! ### The value on the active component -/

omit [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] [DecidableEq V] in
/-- The unit-conductance Laplacian in the form the comparison uses. -/
theorem netLaplacian_unit_eq (f : V → ℝ) (x : V) :
    netLaplacian G (unitCond G) f x
      = (∑ y ∈ G.neighborFinset x, f y) - G.degree x * f x := by
  classical
  rw [netLaplacian]
  rw [Finset.sum_congr rfl (fun y hy => by
    rw [unitCond, if_pos ((SimpleGraph.mem_neighborFinset _ _ _).mp hy), one_mul])]
  rw [Finset.sum_sub_distrib, Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree,
    nsmul_eq_mul]

/-- **The value on the active component is the exit payoff.**  On a set `D` of
sites where the value is positive and whose boundary carries value zero, the
value and the exit payoff from `D` solve the same equation with the same
boundary data, so they agree. -/
theorem valueExit_eq_exitValue (hG : G.Connected) (hdeg : ∀ v : V, 0 < G.degree v)
    (ξ : V → ℝ) (K : Finset V)
    (hesc : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ (K : Set V))
    (D : Finset V) (hDK : D ⊆ K)
    (hDpos : ∀ x ∈ D, 0 < RWRS.valueExit G ξ (K : Set V) x)
    (hDbdry : ∀ x ∈ D, ∀ y, G.Adj x y → y ∉ D → RWRS.valueExit G ξ (K : Set V) y = 0)
    {q : V} (hq : q ∉ D) {x : V} (hx : x ∈ D) :
    RWRS.valueExit G ξ (K : Set V) x = exitValue G ξ (D : Set V) x := by
  classical
  have hescD : ∀ z : V, ∃ (r : V) (_ : G.Walk z r), r ∉ (D : Set V) := by
    intro z
    obtain ⟨r, p, hr⟩ := hesc z
    exact ⟨r, p, fun hc => hr (by exact_mod_cast hDK (by exact_mod_cast hc))⟩
  set vD : V → ℝ := fun z => if z ∈ D then RWRS.valueExit G ξ (K : Set V) z else 0 with hvD
  set f : V → ℝ := fun z => vD z - exitValue G ξ (D : Set V) z with hf
  have hfout : ∀ z : V, z ∉ D → f z = 0 := by
    intro z hz
    have h1 : vD z = 0 := by simp [hvD, hz]
    have h2 : exitValue G ξ (D : Set V) z = 0 :=
      exitValue_eq_zero_of_notMem ξ _ (by exact_mod_cast hz)
    rw [hf]
    simp only [h1, h2, sub_zero]
  have hharm : ∀ z ∈ D, netLaplacian G (unitCond G) f z = 0 := by
    intro z hz
    have hzK : z ∈ K := hDK hz
    have hbell : RWRS.valueExit G ξ (K : Set V) z = bellman G ξ (K : Set V) z := by
      have hle := valueExit_le_bellman hdeg ξ K hesc hzK
      have hge := bellman_le_valueExit hdeg ξ K hesc hzK
      have hpos := hDpos z hz
      rcases le_or_gt 0 (bellman G ξ (K : Set V) z) with h | h
      · rw [max_eq_right h] at hle; linarith
      · rw [max_eq_left h.le] at hle; linarith
    have hstep := exitValue_firstStep hdeg ξ D hescD hz
    have hnb : ∀ y ∈ G.neighborFinset z, vD y = RWRS.valueExit G ξ (K : Set V) y := by
      intro y hy
      by_cases hyD : y ∈ D
      · simp [hvD, hyD]
      · have := hDbdry z hz y ((SimpleGraph.mem_neighborFinset _ _ _).mp hy) hyD
        simp [hvD, hyD, this]
    have hsumv : ∑ y ∈ G.neighborFinset z, vD y
        = ∑ y ∈ G.neighborFinset z, RWRS.valueExit G ξ (K : Set V) y :=
      Finset.sum_congr rfl hnb
    have hvz : vD z = RWRS.valueExit G ξ (K : Set V) z := by simp [hvD, hz]
    have hdz : (G.degree z : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (hdeg z).ne'
    rw [netLaplacian_unit_eq, hf]
    simp only [Finset.sum_sub_distrib]
    rw [hsumv, hvz]
    rw [hbell, bellman] at *
    rw [hstep]
    field_simp
    ring
  have hle : ∀ z : V, f z ≤ 0 :=
    le_of_harmonicOn hG isCond_unitCond D ∅ f 0 hq
      (fun z hz _ => hharm z hz) (fun z hz => le_of_eq (hfout z hz)) (by simp)
  have hge : ∀ z : V, (-f) z ≤ 0 := by
    refine le_of_harmonicOn hG isCond_unitCond D ∅ (-f) 0 hq (fun z hz _ => ?_)
      (fun z hz => by simp [hfout z hz]) (by simp)
    have := hharm z hz
    have hneg : netLaplacian G (unitCond G) (-f) z = - netLaplacian G (unitCond G) f z := by
      simp only [netLaplacian, Pi.neg_apply, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun y _ => by ring
    rw [hneg, this, neg_zero]
  have hzero : f x = 0 := le_antisymm (hle x) (by have := hge x; simp only [Pi.neg_apply] at this; linarith)
  have hvx : vD x = RWRS.valueExit G ξ (K : Set V) x := by simp [hvD, hx]
  rw [hf] at hzero
  simp only [hvx] at hzero
  linarith

end RWRS.Support
