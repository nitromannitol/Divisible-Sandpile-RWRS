/-
Elementary facts about the parallel toppling procedure: the odometer
recursion in the form `eq:u-update`, monotonicity of the odometer, and the
identity `σ_n = σ + Δu_n` used throughout Section 3 of `rwrs.tex`.
-/
import RWRS.Setting

namespace RWRS.Support

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

/-- Every vertex has positive degree, since connectedness supplies a walk to some other
vertex, hence an edge. -/
theorem degree_pos [Infinite V] (hG : G.Connected) (v : V) : 0 < G.degree v := by
  obtain ⟨u, hu⟩ := exists_ne v
  rw [G.degree_pos_iff_exists_adj]
  obtain ⟨w⟩ := hG.preconnected v u
  cases w with
  | nil => exact absurd rfl hu
  | cons h _ => exact ⟨_, h⟩

/-- **The odometer recursion `eq:u-update`**: one more round of the odometer adds the
emission at the current configuration. -/
theorem odometer_succ (σ : V → ℝ) (n : ℕ) (v : V) :
    odometer G σ (n + 1) v = odometer G σ n v + emission G (config G σ n) v :=
  Finset.sum_range_succ _ _

/-- Unfolds one step of the configuration iteration:
`config G σ (n + 1) = topple G (config G σ n)`. -/
theorem config_succ (σ : V → ℝ) (n : ℕ) :
    config G σ (n + 1) = topple G (config G σ n) :=
  Function.iterate_succ_apply' _ _ _

/-- Emission is nonnegative, being a nonnegative numerator divided by a nonnegative degree. -/
theorem emission_nonneg (σ : V → ℝ) (v : V) : 0 ≤ emission G σ v :=
  div_nonneg (le_max_right _ _) (Nat.cast_nonneg _)

/-- The odometer is nonnegative, as a sum of nonnegative emissions. -/
theorem odometer_nonneg (σ : V → ℝ) (n : ℕ) (v : V) : 0 ≤ odometer G σ n v :=
  Finset.sum_nonneg fun _ _ => emission_nonneg _ v

/-- The odometer increases by one round, since the emission added is nonnegative. -/
theorem odometer_mono (σ : V → ℝ) (n : ℕ) (v : V) :
    odometer G σ n v ≤ odometer G σ (n + 1) v := by
  rw [odometer_succ]
  linarith [emission_nonneg (G := G) (config G σ n) v]

/-- The odometer is monotone in the number of rounds `n`, by iterating `odometer_mono`. -/
theorem odometer_le_of_le (σ : V → ℝ) {m n : ℕ} (h : m ≤ n) (v : V) :
    odometer G σ m v ≤ odometer G σ n v := by
  induction n with
  | zero => simp [Nat.le_zero.mp h]
  | succ k ih =>
      rcases Nat.lt_or_ge m (k + 1) with hm | hm
      · exact le_trans (ih (Nat.lt_succ_iff.mp hm)) (odometer_mono _ _ _)
      · have : m = k + 1 := le_antisymm h hm
        subst this; exact le_rfl

/-- `walkOp` is monotone: it preserves a pointwise inequality between the fields it
averages. -/
theorem walkOp_mono {f g : V → ℝ} (h : ∀ v, f v ≤ g v) (x : V) :
    walkOp G f x ≤ walkOp G g x := by
  unfold walkOp
  gcongr with y _
  exact h y

/-- Clears the denominator in the definition of emission:
`deg(v) * emission G σ v = max (σ v - 1) 0`. -/
theorem deg_mul_emission [Infinite V] (hG : G.Connected) (σ : V → ℝ) (v : V) :
    (G.degree v : ℝ) * emission G σ v = max (σ v - 1) 0 := by
  have h : (G.degree v : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (degree_pos hG v).ne'
  rw [emission, mul_comm, div_mul_cancel₀ _ h]

/-- **The configuration identity** `config G σ n = σ + laplacian G (odometer G σ n)`, by
induction on `n` using the toppling recursion and `deg_mul_emission`. -/
theorem config_eq [Infinite V] (hG : G.Connected) (σ : V → ℝ) (n : ℕ) (v : V) :
    config G σ n v = σ v + laplacian G (odometer G σ n) v := by
  induction n generalizing v with
  | zero => simp [config, odometer, laplacian]
  | succ n ih =>
      have hdeg := deg_mul_emission (G := G) hG (config G σ n) v
      have hstep : ∀ w : V, (odometer G σ n w + emission G (config G σ n) w)
            - (odometer G σ n v + emission G (config G σ n) v)
          = (odometer G σ n w - odometer G σ n v)
            + (emission G (config G σ n) w - emission G (config G σ n) v) := by
        intro w; ring
      have hlap : laplacian G (odometer G σ (n + 1)) v
          = laplacian G (odometer G σ n) v
            + ((∑ w ∈ G.neighborFinset v, emission G (config G σ n) w)
              - (G.degree v : ℝ) * emission G (config G σ n) v) := by
        simp only [laplacian, odometer_succ, hstep, Finset.sum_add_distrib,
          Finset.sum_sub_distrib, Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree,
          nsmul_eq_mul]
      have hmin : min (config G σ n v) 1
          = config G σ n v - max (config G σ n v - 1) 0 := by
        rcases le_total (config G σ n v) 1 with h | h
        · rw [min_eq_left h, max_eq_right (by linarith)]; ring
        · rw [min_eq_right h, max_eq_left (by linarith)]; ring
      rw [config_succ, topple, hlap, hmin, hdeg]
      linarith [ih v]

/-- Rewrites the normalized Laplacian as the averaging-operator identity
`laplacian G f x / deg(x) = walkOp G f x - f x`. -/
theorem laplacian_div [Infinite V] (hG : G.Connected) (f : V → ℝ) (x : V) :
    laplacian G f x / (G.degree x : ℝ) = walkOp G f x - f x := by
  have h : (G.degree x : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (degree_pos hG x).ne'
  simp only [laplacian, walkOp, Finset.sum_sub_distrib, Finset.sum_const,
    SimpleGraph.card_neighborFinset_eq_degree, nsmul_eq_mul]
  field_simp

/-- **The Bellman recursion for the odometer**: `odometer G σ (n + 1) x` is the max of the
previous odometer value and the one-step averaged scenery term, from `config_eq` and
`laplacian_div`. -/
theorem odometer_succ_max [Infinite V] (hG : G.Connected) (σ : V → ℝ) (n : ℕ) (x : V) :
    odometer G σ (n + 1) x
      = max (walkOp G (odometer G σ n) x + scenery G σ x) (odometer G σ n x) := by
  have h : (0 : ℝ) < (G.degree x : ℝ) := Nat.cast_pos.mpr (degree_pos hG x)
  have hlap := laplacian_div (G := G) hG (odometer G σ n) x
  have he : emission G (config G σ n) x
      = max (walkOp G (odometer G σ n) x + scenery G σ x - odometer G σ n x) 0 := by
    rw [emission, config_eq hG σ n x]
    rw [show (σ x + laplacian G (odometer G σ n) x - 1)
        = (σ x - 1) + laplacian G (odometer G σ n) x by ring]
    have hmax : ∀ A : ℝ, max A 0 / (G.degree x : ℝ) = max (A / (G.degree x : ℝ)) 0 := by
      intro A
      rcases le_total A 0 with hA | hA
      · rw [max_eq_right hA, max_eq_right (div_nonpos_of_nonpos_of_nonneg hA h.le), zero_div]
      · rw [max_eq_left hA, max_eq_left (div_nonneg hA h.le)]
    rw [hmax, add_div, hlap]
    congr 1
    simp [scenery]
    ring
  rw [odometer_succ, he]
  rcases le_total (walkOp G (odometer G σ n) x + scenery G σ x) (odometer G σ n x) with hc | hc
  · rw [max_eq_right (by linarith), max_eq_right hc]; ring
  · rw [max_eq_left (by linarith), max_eq_left hc]; ring

/-- **The odometer is bounded by the Bellman value**:
`odometer G σ n x ≤ max (walkOp G (odometer G σ n) x + scenery G σ x) 0`, by induction via
`odometer_succ_max`. -/
theorem odometer_le_bellman [Infinite V] (hG : G.Connected) (σ : V → ℝ) (n : ℕ) (x : V) :
    odometer G σ n x ≤ max (walkOp G (odometer G σ n) x + scenery G σ x) 0 := by
  induction n generalizing x with
  | zero => simp [odometer]
  | succ n ih =>
      have hmono : ∀ y, odometer G σ n y ≤ odometer G σ (n + 1) y := fun y =>
        odometer_mono σ n y
      have hw : walkOp G (odometer G σ n) x ≤ walkOp G (odometer G σ (n + 1)) x :=
        walkOp_mono hmono x
      rw [odometer_succ_max hG]
      refine max_le ?_ ?_
      · exact le_trans (by linarith) (le_max_left _ _)
      · exact le_trans (ih x) (max_le_max (by linarith) le_rfl)

end RWRS.Support
