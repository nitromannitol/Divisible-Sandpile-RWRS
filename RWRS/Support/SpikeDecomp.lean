/-
The spike decomposition of `lem:moment-sharpness`.

Running the walk for a deterministic number of steps is one of the stopping
rules, so its mean payoff is below the odometer; and the mean payoff splits into
the drift, the mass at one distinguished site weighted by the finite-time Green
function, and the background from every other site.  This is `eq:spike-decomp`.
-/
import RWRS.Support.Explosion
import RWRS.Frozen.RWInfinite

namespace RWRS.Support

open scoped ENNReal Classical

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

/-- **The mean payoff at a deterministic time is below the odometer.** -/
theorem ofReal_meanPayoff_le_odometerLimit [Infinite V] (hG : G.Connected)
    (σ : V → ℝ) (n : ℕ) (o : V) :
    ENNReal.ofReal (RWRS.meanPayoff G (RWRS.excess σ) n o) ≤ RWRS.odometerLimit G σ o := by
  rw [RWRS.Frozen.rwInfinite hG σ o]
  refine le_iSup_of_le n (le_iSup_of_le (RWRS.meanPayoff G (RWRS.excess σ) n o)
    (le_iSup_of_le ⟨fun _ => n, (fun _ _ _ _ h => h), fun _ => le_rfl, rfl⟩ le_rfl))

/-- **The drift and the fluctuation of the mean payoff.**  With `μ` the mean of
the masses the payoff of `eq:dn-wn-stuff` reads `(μ-1)A_n(o)` plus the
Green-weighted centred masses. -/
theorem meanPayoff_excess_eq [Infinite V] (hG : G.Connected) (σ : V → ℝ) (μ : ℝ)
    (n : ℕ) (o : V) :
    RWRS.meanPayoff G (RWRS.excess σ) n o
      = (μ - 1) * RWRS.clock G n o
        + ∑ v ∈ reach G o n, RWRS.greenTime G n o v * (σ v - μ) := by
  have h := meanPayoff_eq_drift_add hG (RWRS.excess σ) (μ - 1) n o
  rw [h]
  congr 1
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [RWRS.excess]
  ring_nf

/-- **The spike at one site.**  The Green-weighted centred masses split into the
mass at `v` and the background from every other site. -/
theorem sum_green_split [Infinite V] (σ : V → ℝ) (μ : ℝ) (n : ℕ) (o : V)
    {v : V} (hv : v ∈ reach G o n) :
    ∑ w ∈ reach G o n, RWRS.greenTime G n o w * (σ w - μ)
      = RWRS.greenTime G n o v * (σ v - μ)
        + ∑ w ∈ (reach G o n).erase v, RWRS.greenTime G n o w * (σ w - μ) :=
  (Finset.add_sum_erase _ _ hv).symm

/-- The background at `v`: the Green-weighted centred masses of every other
site reached before time `n`. -/
noncomputable def background (G : SimpleGraph V) [G.LocallyFinite] (σ : V → ℝ) (μ : ℝ)
    (n : ℕ) (o v : V) : ℝ :=
  ∑ w ∈ (reach G o n).erase v, RWRS.greenTime G n o w * (σ w - μ)

/-- **`eq:spike-decomp`.**  The odometer at the root is at least the spike at any
reached site plus the background plus the drift. -/
theorem spike_decomp [Infinite V] (hG : G.Connected) (σ : V → ℝ) (μ : ℝ) (n : ℕ)
    (o : V) {v : V} (hv : v ∈ reach G o n) :
    ENNReal.ofReal (RWRS.greenTime G n o v * (σ v - μ) + background G σ μ n o v
        + (μ - 1) * RWRS.clock G n o)
      ≤ RWRS.odometerLimit G σ o := by
  refine le_trans (le_of_eq ?_) (ofReal_meanPayoff_le_odometerLimit hG σ n o)
  congr 1
  rw [meanPayoff_excess_eq hG σ μ n o, sum_green_split σ μ n o hv, background]
  ring

/-- The mean payoff after one step is the excess at the root. -/
theorem meanPayoff_one [Infinite V] (hG : G.Connected) (ξ : V → ℝ) (o : V) :
    RWRS.meanPayoff G ξ 1 o = ξ o / (G.degree o : ℝ) := by
  have hd : (G.degree o : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (degree_pos hG o).ne'
  rw [RWRS.meanPayoff, walkExp_succ]
  have hterm : ∀ y ∈ G.neighborFinset o,
      walkExp G 0 y (fun X => RWRS.payoff G ξ 1 (cons o X)) = ξ o / (G.degree o : ℝ) := by
    intro y _
    show RWRS.payoff G ξ 1 (cons o (fun _ => y)) = ξ o / (G.degree o : ℝ)
    rw [RWRS.payoff, Finset.sum_range_one]
    rfl
  rw [Finset.sum_congr rfl hterm, Finset.sum_const,
    SimpleGraph.card_neighborFinset_eq_degree, nsmul_eq_mul]
  field_simp

/-- **The single-site bound.**  The odometer at the root is at least the excess
there, so an infinite mean of the positive part of the mass already makes the
mean of the odometer infinite. -/
theorem ofReal_excess_le_odometerLimit [Infinite V] (hG : G.Connected) (σ : V → ℝ) (o : V) :
    ENNReal.ofReal ((σ o - 1) / (G.degree o : ℝ)) ≤ RWRS.odometerLimit G σ o := by
  refine le_trans (le_of_eq ?_) (ofReal_meanPayoff_le_odometerLimit hG σ 1 o)
  rw [meanPayoff_one hG (RWRS.excess σ) o, RWRS.excess]

end RWRS.Support
