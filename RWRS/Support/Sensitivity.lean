/-
One-site sensitivity of the optimal stopping value (`lem:sensitivity`).

Changing the scenery at a single vertex changes the payoff of a stopping rule
by the value of the change times the local time at that vertex, so it changes
the walk average of the payoff by at most the value of the change times the
finite-time Green function.  Passing to the supremum over stopping rules keeps
the bound, because a supremum is `1`-Lipschitz in the family.
-/
import RWRS.Support.ShortClock
import RWRS.Support.Green
import RWRS.Support.LibraryBridge

namespace RWRS.Support

open scoped ENNReal

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

theorem walkExp_const_mul (c : ℝ) : ∀ (n : ℕ) (x : V) (F : (ℕ → V) → ℝ),
    walkExp G n x (fun X => c * F X) = c * walkExp G n x F := by
  intro n
  induction n with
  | zero => intro x F; rfl
  | succ n ih =>
      intro x F
      rw [walkExp_succ, walkExp_succ]
      rw [show (fun y => walkExp G n y (fun X => c * F (cons x X)))
          = fun y => c * walkExp G n y (fun X => F (cons x X)) from
        funext fun y => ih y _]
      rw [← Finset.mul_sum, mul_div_assoc]

theorem walkExp_sub (n : ℕ) (x : V) (F F' : (ℕ → V) → ℝ) :
    walkExp G n x (fun X => F X - F' X) = walkExp G n x F - walkExp G n x F' := by
  have h := walkExp_add (G := G) n x (fun X => F X - F' X) F'
  simp only [sub_add_cancel] at h
  linarith [h]

open scoped Classical in
/-- The one-vertex scenery `1_{u = v}`. -/
noncomputable def spike (v : V) : V → ℝ := fun u => if u = v then 1 else 0

open scoped Classical in
theorem payoff_sub_resample (ξ : V → ℝ) (v : V) (t : ℝ) (k : ℕ) (X : ℕ → V) :
    payoff G ξ k X - payoff G (resample ξ v t) k X
      = (ξ v - t) * payoff G (spike v) k X := by
  rw [payoff, payoff, payoff, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : X j = v
  · rw [h, resample, if_pos rfl, spike, if_pos rfl]
    ring
  · rw [resample, if_neg h, spike, if_neg h]
    ring

open scoped Classical in
theorem walkExp_payoff_spike [Infinite V] (hG : G.Connected) (n : ℕ) (o v : V) :
    walkExp G n o (payoff G (spike v) n) = greenTime G n o v := by
  rw [walkExp_payoff_eq hG]
  have hfun : (fun u => spike v u / (G.degree u : ℝ))
      = fun u => if u = v then 1 / (G.degree v : ℝ) else 0 := by
    funext u
    by_cases h : u = v
    · rw [spike, if_pos h, if_pos h, h]
    · rw [spike, if_neg h, if_neg h, zero_div]
  rw [hfun, Finset.sum_congr rfl fun k _ =>
    walkOp_iterate_single (G := G) v (1 / (G.degree v : ℝ)) k o]
  rw [← Finset.sum_mul, greenTime, meanLocalTime]
  ring

theorem payoff_spike_nonneg (v : V) (k : ℕ) (X : ℕ → V) :
    0 ≤ payoff G (spike v) k X := by
  classical
  refine Finset.sum_nonneg fun j _ => div_nonneg ?_ (Nat.cast_nonneg _)
  rw [spike]
  split <;> norm_num

theorem payoff_spike_mono (v : V) {k n : ℕ} (h : k ≤ n)
    (X : ℕ → V) : payoff G (spike v) k X ≤ payoff G (spike v) n X := by
  classical
  refine Finset.sum_le_sum_of_subset_of_nonneg
    (fun j hj => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hj) h))
    (fun j _ _ => div_nonneg ?_ (Nat.cast_nonneg _))
  rw [spike]
  split <;> norm_num

/-- The value of one stopping rule moves by at most the Green function times
the change in the scenery. -/
theorem abs_walkExp_payoff_sub [Infinite V] (hG : G.Connected) (ξ : V → ℝ) (v : V) (t : ℝ)
    (n : ℕ) (o : V) {τ : (ℕ → V) → ℕ} (hτ : ∀ X, τ X ≤ n) :
    |walkExp G n o (fun X => payoff G ξ (τ X) X)
        - walkExp G n o (fun X => payoff G (resample ξ v t) (τ X) X)|
      ≤ greenTime G n o v * |ξ v - t| := by
  classical
  rw [← walkExp_sub]
  rw [show (fun X => payoff G ξ (τ X) X - payoff G (resample ξ v t) (τ X) X)
      = fun X => (ξ v - t) * payoff G (spike v) (τ X) X from
    funext fun X => payoff_sub_resample ξ v t (τ X) X]
  rw [walkExp_const_mul, abs_mul]
  have hnn : 0 ≤ walkExp G n o (fun X => payoff G (spike v) (τ X) X) :=
    le_trans (le_of_eq (walkExp_const hG n o 0).symm)
      (walkExp_mono fun X => payoff_spike_nonneg v (τ X) X)
  have hle : walkExp G n o (fun X => payoff G (spike v) (τ X) X) ≤ greenTime G n o v := by
    rw [← walkExp_payoff_spike hG n o v]
    exact walkExp_mono fun X => payoff_spike_mono v (hτ X) X
  rw [abs_of_nonneg hnn, mul_comm]
  exact mul_le_mul_of_nonneg_right hle (abs_nonneg (ξ v - t))

theorem isLUB_value [Infinite V] (hG : G.Connected) (ξ : V → ℝ) (n : ℕ) (x : V) :
    IsLUB (stopValues G ξ n x) (value G ξ n x) := by
  have hex : excess (fun u => ξ u + 1) = ξ := by
    funext u; rw [excess]; ring
  have h := isLUB_odometer hG (fun u => ξ u + 1) n x
  rw [hex] at h
  have hv : value G ξ n x = odometer G (fun u => ξ u + 1) n x := by
    have := value_eq hG (fun u => ξ u + 1) n x
    rwa [hex] at this
  rw [hv]
  exact h


open scoped Classical in
theorem resample_resample (ξ : V → ℝ) (v : V) (t : ℝ) :
    resample (resample ξ v t) v (ξ v) = ξ := by
  funext u
  by_cases h : u = v
  · rw [resample, if_pos h, h]
  · rw [resample, if_neg h, resample, if_neg h]

open scoped Classical in
theorem resample_self (ξ : V → ℝ) (v : V) (t : ℝ) : resample ξ v t v = t := by
  rw [resample, if_pos rfl]

/-- One side of the sensitivity bound for the finite-horizon value. -/
theorem value_le_resample [Infinite V] (hG : G.Connected) (ζ : V → ℝ) (v : V) (s : ℝ)
    (n : ℕ) (o : V) :
    value G ζ n o ≤ value G (resample ζ v s) n o + greenTime G n o v * |ζ v - s| := by
  refine (isLUB_value hG ζ n o).2 fun a ha => ?_
  obtain ⟨τ, hτs, hτn, rfl⟩ := ha
  have ha' : walkExp G n o (fun X => payoff G (resample ζ v s) (τ X) X)
      ∈ stopValues G (resample ζ v s) n o := ⟨τ, hτs, hτn, rfl⟩
  have hb := abs_walkExp_payoff_sub hG ζ v s n o hτn
  have h1 := (abs_sub_le_iff.mp hb).1
  have h2 := (isLUB_value hG (resample ζ v s) n o).1 ha'
  linarith

/-- One side of the sensitivity bound for the infinite-horizon value. -/
theorem supStopValue_le_resample [Infinite V] (hG : G.Connected) (ζ : V → ℝ) (v : V) (s : ℝ)
    (o : V) :
    supStopValue G ζ o
      ≤ supStopValue G (resample ζ v s) o + green G o v * ENNReal.ofReal |ζ v - s| := by
  refine iSup_le fun n => iSup_le fun a => iSup_le fun ha => ?_
  obtain ⟨τ, hτs, hτn, rfl⟩ := ha
  have ha' : walkExp G n o (fun X => payoff G (resample ζ v s) (τ X) X)
      ∈ stopValues G (resample ζ v s) n o := ⟨τ, hτs, hτn, rfl⟩
  have hb := abs_walkExp_payoff_sub hG ζ v s n o hτn
  have h1 := (abs_sub_le_iff.mp hb).1
  have hstep0 : (walkExp G n o fun X => payoff G ζ (τ X) X)
      ≤ (walkExp G n o fun X => payoff G (resample ζ v s) (τ X) X)
        + greenTime G n o v * |ζ v - s| := by linarith
  have hstep : ENNReal.ofReal (walkExp G n o fun X => payoff G ζ (τ X) X)
      ≤ ENNReal.ofReal (walkExp G n o fun X => payoff G (resample ζ v s) (τ X) X)
        + ENNReal.ofReal (greenTime G n o v * |ζ v - s|) :=
    le_trans (ENNReal.ofReal_le_ofReal hstep0) ENNReal.ofReal_add_le
  refine le_trans hstep (add_le_add ?_ ?_)
  · exact le_iSup_of_le n (le_iSup_of_le _ (le_iSup_of_le ha' le_rfl))
  · rw [ENNReal.ofReal_mul (greenTime_nonneg n o v)]
    exact mul_le_mul' (ofReal_greenTime_le_green hG n o v) le_rfl

theorem green_ne_top_of_not_recurrent [Infinite V] (hG : G.Connected) {o : V}
    (h : green G o o ≠ ⊤) (v : V) : green G o v ≠ ⊤ := by
  rw [green_ne_top_iff hG]
  have h1 : (∑' k : ℕ, ENNReal.ofReal (heat G k v o)) ≠ ⊤ :=
    green_ne_top_transfer hG ((green_ne_top_iff hG o o).mp h) v
  have hdo : (0 : ℝ) < (G.degree o : ℝ) := by exact_mod_cast degree_pos hG o
  have hrev : ∀ k : ℕ, ENNReal.ofReal (heat G k o v)
      = ENNReal.ofReal ((G.degree v : ℝ) / (G.degree o : ℝ)) * ENNReal.ofReal (heat G k v o) := by
    intro k
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have hr := heat_reversible (G := G) k o v
    field_simp
    linarith [hr]
  rw [tsum_congr hrev, ENNReal.tsum_mul_left]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top h1

end RWRS.Support
