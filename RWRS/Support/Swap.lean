/-
Rearranging the masses by a permutation of finitely many vertices changes the
odometer by a bounded amount, so stabilization is an exchangeable event.

The difference of the two sceneries is a finite combination of the coboundaries
`δ_{π⁻¹ v} - δ_v`, each of which is the Laplacian of a bounded potential; by
optional stopping the payoff of a coboundary is bounded by twice the sup-norm of
its potential, uniformly over the bounded stopping times.
-/
import RWRS.Support.OptionalStopping
import RWRS.External.VoltageFunction
import RWRS.Frozen.RWInfinite
import RWRS.Support.Measurability

namespace RWRS.Support

open scoped Classical

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite] [Infinite V]

omit [Infinite V] in
theorem payoff_add (ξ η : V → ℝ) (m : ℕ) (X : ℕ → V) :
    payoff G (fun v => ξ v + η v) m X = payoff G ξ m X + payoff G η m X := by
  simp only [payoff, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

omit [Infinite V] in
theorem laplacian_finsetSum (S : Finset V) (c : V → ℝ) (f : V → V → ℝ) (x : V) :
    laplacian G (fun w => ∑ v ∈ S, c v * f v w) x
      = ∑ v ∈ S, c v * laplacian G (f v) x := by
  simp only [laplacian, ← Finset.sum_sub_distrib, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun y _ => by ring

omit [Infinite V] in
/-- The scenery moved by a permutation differs from the original by the
Laplacian of a bounded potential. -/
theorem exists_potential (hVF : RWRS.External.VoltageFunction G)
    (σ : V → ℝ) (π : Equiv.Perm V) (hfin : {i : V | π i ≠ i}.Finite) :
    ∃ F : V → ℝ, ∃ C : ℝ, 0 ≤ C ∧ (∀ x, |F x| ≤ C) ∧
      ∀ x : V, σ (π x) - σ x = laplacian G F x := by
  classical
  set S : Finset V := hfin.toFinset with hSdef
  have hmemS : ∀ v : V, v ∈ S ↔ π v ≠ v := by
    intro v; simp [hSdef]
  have hsymm_ne : ∀ v : V, v ∈ S → π.symm v ≠ v := by
    intro v hv h
    rw [hmemS] at hv
    exact hv ((Equiv.symm_apply_eq π).mp h).symm
  have hpi_mem : ∀ x : V, π x ∈ S ↔ x ∈ S := by
    intro x
    rw [hmemS, hmemS]
    exact ⟨fun h hx => h (by rw [hx]; exact hx), fun h hx => h (π.injective hx)⟩
  choose f M hM hfM hlap using fun (v : V) (hv : π.symm v ≠ v) =>
    hVF v (π.symm v) (Ne.symm hv)
  set g : V → V → ℝ := fun v => if hv : π.symm v ≠ v then f v hv else 0 with hgdef
  set Cb : V → ℝ := fun v => if hv : π.symm v ≠ v then M v hv else 0 with hCdef
  have hgbound : ∀ v w : V, 0 ≤ g v w ∧ g v w ≤ Cb v := by
    intro v w
    by_cases hv : π.symm v ≠ v
    · simp only [hgdef, hCdef, dif_pos hv]
      exact hfM v hv w
    · simp only [hgdef, hCdef, dif_neg hv]
      exact ⟨le_rfl, le_rfl⟩
  have hglap : ∀ v : V, π.symm v ≠ v → ∀ x : V,
      laplacian G (g v) x = (if x = π.symm v then (1 : ℝ) else 0) - (if x = v then 1 else 0) := by
    intro v hv x
    simp only [hgdef, dif_pos hv]
    exact hlap v hv x
  refine ⟨fun w => ∑ v ∈ S, σ v * g v w, ∑ v ∈ S, |σ v| * Cb v, ?_, ?_, ?_⟩
  · exact Finset.sum_nonneg fun v _ => mul_nonneg (abs_nonneg _)
      (le_trans (hgbound v v).1 (hgbound v v).2)
  · intro x
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun v _ => ?_)
    rw [abs_mul, abs_of_nonneg (hgbound v x).1]
    exact mul_le_mul_of_nonneg_left (hgbound v x).2 (abs_nonneg _)
  · intro x
    rw [laplacian_finsetSum]
    have hterm : ∀ v ∈ S, σ v * laplacian G (g v) x
        = σ v * ((if x = π.symm v then (1 : ℝ) else 0) - (if x = v then 1 else 0)) := by
      intro v hv
      rw [hglap v (hsymm_ne v hv)]
    rw [Finset.sum_congr rfl hterm]
    simp only [mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib]
    have hcond : ∀ v : V, (if x = π.symm v then σ v else 0) = if v = π x then σ v else 0 := by
      intro v
      by_cases h : v = π x
      · rw [if_pos h, if_pos (by rw [h]; simp)]
      · rw [if_neg h, if_neg (by intro hc; exact h (by rw [hc]; simp))]
    rw [Finset.sum_congr rfl fun v _ => hcond v, Finset.sum_ite_eq' S (π x) σ,
      Finset.sum_ite_eq S x σ]
    by_cases hx : x ∈ S
    · rw [if_pos ((hpi_mem x).mpr hx), if_pos hx]
    · rw [if_neg (fun hc => hx ((hpi_mem x).mp hc)), if_neg hx]
      have : π x = x := by
        by_contra hc
        exact hx ((hmemS x).mpr hc)
      rw [this]
      ring

omit [Infinite V] in
theorem payoff_neg (ξ : V → ℝ) (m : ℕ) (X : ℕ → V) :
    payoff G (fun v => -ξ v) m X = -payoff G ξ m X := by
  simp only [payoff, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem walkExp_abs_le (hG : G.Connected) {C : ℝ} {H : (ℕ → V) → ℝ}
    (hH : ∀ X, |H X| ≤ C) (n : ℕ) (x : V) : |walkExp G n x H| ≤ C := by
  have h1 : walkExp G n x H ≤ C := by
    refine le_trans (walkExp_mono (F' := fun _ => C) fun X => ?_) ?_
    · exact le_trans (le_abs_self _) (hH X)
    · exact le_of_eq (walkExp_const hG n x C)
  have h2 : -C ≤ walkExp G n x H := by
    refine le_trans ?_ (walkExp_mono (F := fun _ => -C) fun X => ?_)
    · exact le_of_eq (walkExp_const hG n x (-C)).symm
    · exact neg_le_of_abs_le (hH X)
  exact abs_le.mpr ⟨h2, h1⟩

/-- Rearranging the masses by a permutation of finitely many vertices changes
every bounded stopping value by at most a constant. -/
theorem perm_stop_bound (hVF : RWRS.External.VoltageFunction G) (hG : G.Connected)
    (σ : V → ℝ) (π : Equiv.Perm V) (hfin : {i : V | π i ≠ i}.Finite) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (x : V) (τ : (ℕ → V) → ℕ), IsStopping τ → (∀ X, τ X ≤ n) →
      |walkExp G n x (fun X => payoff G (excess (fun v => σ (π v))) (τ X) X)
        - walkExp G n x (fun X => payoff G (excess σ) (τ X) X)| ≤ C := by
  obtain ⟨F, C, hC0, hCb, hF⟩ := exists_potential hVF σ π hfin
  refine ⟨2 * C, by linarith, fun n x τ hτ hle => ?_⟩
  have hsplit : ∀ X : ℕ → V,
      payoff G (excess (fun v => σ (π v))) (τ X) X
        = payoff G (excess σ) (τ X) X + payoff G (laplacian G F) (τ X) X := by
    intro X
    rw [← payoff_add]
    refine Finset.sum_congr rfl fun k _ => ?_
    have := hF (X k)
    simp only [excess]
    rw [show σ (π (X k)) - 1 = (σ (X k) - 1) + (σ (π (X k)) - σ (X k)) from by ring, this]
  have hopt := walkExp_optional hG F n x τ hτ hle
  have hneg : ∀ X : ℕ → V,
      payoff G (fun v => -laplacian G F v) (τ X) X = -payoff G (laplacian G F) (τ X) X :=
    fun X => payoff_neg _ _ X
  have hval : walkExp G n x (fun X => payoff G (laplacian G F) (τ X) X)
      = walkExp G n x (fun X => F (X (τ X))) - F x := by
    have h1 : walkExp G n x (fun X => -payoff G (laplacian G F) (τ X) X
        + F (X (τ X))) = F x := by
      rw [← hopt]
      exact walkExp_congr fun X _ => by rw [hneg X]
    have h2 : walkExp G n x (fun X => -payoff G (laplacian G F) (τ X) X)
        + walkExp G n x (fun X => F (X (τ X))) = F x := by
      rw [← walkExp_add]; exact h1
    have h3 : walkExp G n x (fun X => -payoff G (laplacian G F) (τ X) X)
        = -walkExp G n x (fun X => payoff G (laplacian G F) (τ X) X) := by
      have := walkExp_add (G := G) n x (fun X => payoff G (laplacian G F) (τ X) X)
        (fun X => -payoff G (laplacian G F) (τ X) X)
      simp only [add_neg_cancel] at this
      rw [walkExp_const hG n x 0] at this
      linarith
    rw [h3] at h2
    linarith
  have hdiff : walkExp G n x (fun X => payoff G (excess (fun v => σ (π v))) (τ X) X)
      = walkExp G n x (fun X => payoff G (excess σ) (τ X) X)
        + walkExp G n x (fun X => payoff G (laplacian G F) (τ X) X) := by
    rw [← walkExp_add]
    exact walkExp_congr fun X _ => hsplit X
  rw [hdiff, hval,
    show walkExp G n x (fun X => payoff G (excess σ) (τ X) X)
        + (walkExp G n x (fun X => F (X (τ X))) - F x)
        - walkExp G n x (fun X => payoff G (excess σ) (τ X) X)
      = walkExp G n x (fun X => F (X (τ X))) - F x from by ring]
  have hb1 : |walkExp G n x (fun X => F (X (τ X)))| ≤ C :=
    walkExp_abs_le hG (fun X => hCb (X (τ X))) n x
  have hb2 : |F x| ≤ C := hCb x
  have := abs_sub (walkExp G n x (fun X => F (X (τ X)))) (F x)
  linarith

omit [Infinite V] in
theorem perm_symm_finite {π : Equiv.Perm V} (hfin : {i : V | π i ≠ i}.Finite) :
    {i : V | π.symm i ≠ i}.Finite := by
  have : {i : V | π.symm i ≠ i} = {i : V | π i ≠ i} := by
    ext i
    simp only [Set.mem_setOf_eq]
    constructor
    · intro h hc
      exact h (by rw [Equiv.symm_apply_eq]; exact hc.symm)
    · intro h hc
      exact h (by rw [← (Equiv.symm_apply_eq π).mp hc])
  rw [this]; exact hfin

/-- Rearranging the masses by a permutation of finitely many vertices changes
neither the finiteness of the odometer nor the finiteness of the mean payoff. -/
theorem perm_sup_le (hVF : RWRS.External.VoltageFunction G) (hG : G.Connected)
    (σ : V → ℝ) (π : Equiv.Perm V) (hfin : {i : V | π i ≠ i}.Finite) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : V,
      supStopValue G (excess fun v => σ (π v)) x
          ≤ supStopValue G (excess σ) x + ENNReal.ofReal C ∧
      supMeanPayoff G (excess fun v => σ (π v)) x
          ≤ supMeanPayoff G (excess σ) x + ENNReal.ofReal C := by
  obtain ⟨C, hC0, hbd⟩ := perm_stop_bound hVF hG σ π hfin
  refine ⟨C, hC0, fun x => ⟨?_, ?_⟩⟩
  · refine iSup_le fun n => iSup_le fun a => iSup_le fun ha => ?_
    obtain ⟨τ, hτ, hle, rfl⟩ := ha
    have hb := hbd n x τ hτ hle
    have hle' : walkExp G n x (fun X => payoff G (excess fun v => σ (π v)) (τ X) X)
        ≤ walkExp G n x (fun X => payoff G (excess σ) (τ X) X) + C := by
      have := abs_le.mp hb
      linarith [this.2]
    have hmem : walkExp G n x (fun X => payoff G (excess σ) (τ X) X)
        ∈ stopValues G (excess σ) n x := ⟨τ, hτ, hle, rfl⟩
    refine le_trans (ENNReal.ofReal_le_ofReal hle') (le_trans ENNReal.ofReal_add_le ?_)
    gcongr
    exact le_iSup_of_le n (le_iSup_of_le _ (le_iSup_of_le hmem le_rfl))
  · refine iSup_le fun n => ?_
    have hτ : IsStopping (fun _ : ℕ → V => n) := fun k X Y _ h => h
    have hb := hbd n x (fun _ => n) hτ (fun _ => le_rfl)
    have hle' : meanPayoff G (excess fun v => σ (π v)) n x
        ≤ meanPayoff G (excess σ) n x + C := by
      have := abs_le.mp hb
      simp only [meanPayoff] at *
      linarith [this.2]
    refine le_trans (ENNReal.ofReal_le_ofReal hle') (le_trans ENNReal.ofReal_add_le ?_)
    gcongr
    exact le_iSup (fun m => ENNReal.ofReal (meanPayoff G (excess σ) m x)) n

theorem stabilizes_perm_iff (hVF : RWRS.External.VoltageFunction G) (hG : G.Connected)
    (σ : V → ℝ) (π : Equiv.Perm V) (hfin : {i : V | π i ≠ i}.Finite) :
    Stabilizes G (fun v => σ (π v)) ↔ Stabilizes G σ := by
  obtain ⟨C, hC0, hle⟩ := perm_sup_le hVF hG σ π hfin
  obtain ⟨C', hC0', hle'⟩ := perm_sup_le hVF hG (fun v => σ (π v)) π.symm
    (perm_symm_finite hfin)
  have hback : ∀ v : V, (fun w => σ (π w)) (π.symm v) = σ v := by
    intro v; simp
  constructor
  · intro hst v
    have h1 := (hle' v).1
    rw [show (fun w => σ (π (π.symm w))) = σ from funext hback] at h1
    rw [RWRS.Frozen.rwInfinite hG σ v]
    refine ne_top_of_le_ne_top ?_ h1
    rw [← RWRS.Frozen.rwInfinite hG (fun w => σ (π w)) v]
    exact ENNReal.add_ne_top.mpr ⟨hst v, ENNReal.ofReal_ne_top⟩
  · intro hst v
    rw [RWRS.Frozen.rwInfinite hG (fun w => σ (π w)) v]
    refine ne_top_of_le_ne_top ?_ (hle v).1
    rw [← RWRS.Frozen.rwInfinite hG σ v]
    exact ENNReal.add_ne_top.mpr ⟨hst v, ENNReal.ofReal_ne_top⟩

theorem supMeanPayoff_perm_iff (hVF : RWRS.External.VoltageFunction G) (hG : G.Connected)
    (σ : V → ℝ) (π : Equiv.Perm V) (hfin : {i : V | π i ≠ i}.Finite) (o : V) :
    supMeanPayoff G (excess fun v => σ (π v)) o = ⊤ ↔ supMeanPayoff G (excess σ) o = ⊤ := by
  obtain ⟨C, hC0, hle⟩ := perm_sup_le hVF hG σ π hfin
  obtain ⟨C', hC0', hle'⟩ := perm_sup_le hVF hG (fun v => σ (π v)) π.symm
    (perm_symm_finite hfin)
  have hback : (fun w => σ (π (π.symm w))) = σ := funext fun v => by simp
  constructor
  · intro h
    have h1 := (hle o).2
    rw [h, top_le_iff] at h1
    rcases ENNReal.add_eq_top.mp h1 with h2 | h2
    · exact h2
    · exact absurd h2 ENNReal.ofReal_ne_top
  · intro h
    have h1 := (hle' o).2
    rw [hback] at h1
    rw [h, top_le_iff] at h1
    rcases ENNReal.add_eq_top.mp h1 with h2 | h2
    · exact h2
    · exact absurd h2 ENNReal.ofReal_ne_top

end RWRS.Support
