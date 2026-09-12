/-
The increments of the fluctuation over a discrete interval, and their tail.

The chaining of `prop:subcritical` cuts `W_n` into increments `W(I)` over
dyadic sub-intervals `I ⊆ [0,N)`.  Written along the trajectory the increment is
a sum over time; written along the range of the trajectory it is a weighted sum
of the centred scenery over the finitely many sites visited during `I`, whose
weights are the local times divided by the degrees, and in that form the three
parts of `lem:fuk-nagaev` apply to it site by site, the scenery being
independent of the walk.
-/
import RWRS.Support.FukNagaevWeighted
import RWRS.Support.GoodWalkMoment

namespace RWRS.Support

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

/-- The sites visited by the trajectory during the discrete interval `[a,b)`. -/
noncomputable def walkSites (a b : ℕ) (X : ℕ → V) : Finset V := (Finset.Ico a b).image X

/-- `L_I(v)`, the local time of `v` during the discrete interval `I = [a,b)`. -/
noncomputable def localTimeOn (a b : ℕ) (v : V) (X : ℕ → V) : ℕ :=
  {j ∈ Finset.Ico a b | X j = v}.card

/-- `W(I)`, the increment of the fluctuation over the discrete interval
`I = [a,b)`. -/
noncomputable def fluctOn (G : SimpleGraph V) [G.LocallyFinite] (ξ : V → ℝ) (m : ℝ) (a b : ℕ)
    (X : ℕ → V) : ℝ :=
  ∑ j ∈ Finset.Ico a b, (ξ (X j) - m) / (G.degree (X j) : ℝ)

/-- The weight the increment gives to a site: its local time over the interval,
divided by its degree. -/
noncomputable def incWeight (G : SimpleGraph V) [G.LocallyFinite] (a b : ℕ) (X : ℕ → V)
    (v : V) : ℝ :=
  (localTimeOn a b v X : ℝ) / (G.degree v : ℝ)

/-- The increment as a weighted sum of the centred scenery over the sites
visited. -/
theorem fluctOn_eq_sum_sites (ξ : V → ℝ) (m : ℝ) (a b : ℕ) (X : ℕ → V) :
    fluctOn G ξ m a b X
      = ∑ v ∈ walkSites a b X, incWeight G a b X v * (ξ v - m) := by
  unfold fluctOn walkSites incWeight localTimeOn
  rw [Finset.sum_comp (fun v : V => (ξ v - m) / (G.degree v : ℝ)) X]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [nsmul_eq_mul]
  ring

/-- The increments add along consecutive intervals. -/
theorem fluctOn_add (ξ : V → ℝ) (m : ℝ) {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) (X : ℕ → V) :
    fluctOn G ξ m a b X + fluctOn G ξ m b c X = fluctOn G ξ m a c X :=
  Finset.sum_Ico_consecutive _ hab hbc

/-- The fluctuation at time `n` is the increment over `[0,n)`. -/
theorem fluctuation_eq_fluctOn (ξ : V → ℝ) (m : ℝ) (n : ℕ)
    (X : ℕ → V) : RWRS.fluctuation G ξ m n X = fluctOn G ξ m 0 n X := by
  rw [fluctuation_eq_sum]
  unfold fluctOn
  rw [Finset.range_eq_Ico]

/-- The weights of an increment are nonnegative. -/
theorem incWeight_nonneg (a b : ℕ) (X : ℕ → V) (v : V) : 0 ≤ incWeight G a b X v :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-! ### The tail of an increment, conditionally on the walk -/

variable {ν : Measure ℝ}

/-- **The polynomial tail of an increment**, part (a) of `lem:fuk-nagaev`
applied to the sites visited during the interval, the scenery being independent
of the walk. -/
theorem meas_fluctOn_ge [IsProbabilityMeasure ν] {p Cp : ℝ}
    (hFN : ∀ {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι] (P : Measure Ω),
      IsProbabilityMeasure P → ∀ (Y : ι → Ω → ℝ), iIndepFun Y P →
        (∀ i, Integrable (Y i) P) → (∀ i, ∫ ω, Y i ω ∂P = 0) →
        ∀ Mp : ℝ, Mp = ∑ i, (∫⁻ ω, ENNReal.ofReal (|Y i ω| ^ p) ∂P).toReal →
          (∀ i, (∫⁻ ω, ENNReal.ofReal (|Y i ω| ^ p) ∂P) ≠ ⊤) →
          ∀ t : ℝ, 0 < t →
            P {ω | t ≤ |∑ i, Y i ω|} ≤ ENNReal.ofReal (Cp * Mp / t ^ p))
    (m : ℝ) (hint : Integrable (fun z : ℝ => z) ν) (hm : ∫ z, z ∂ν = m)
    (hp : 1 ≤ p) (hmom : RWRS.absMoment ν p ≠ ⊤)
    (a b : ℕ) (X : ℕ → V) (t : ℝ) (ht : 0 < t) :
    RWRS.iidLaw V ν {ξ : V → ℝ | t ≤ |fluctOn G ξ m a b X|}
      ≤ ENNReal.ofReal (Cp * (∑ v ∈ walkSites a b X,
          incWeight G a b X v ^ p * (RWRS.centeredMoment ν m p).toReal) / t ^ p) := by
  have hf : Measurable fun z : ℝ => z - m := measurable_id.sub_const m
  have hfint : Integrable (fun z : ℝ => z - m) ν := hint.sub (integrable_const m)
  have hf0 : ∫ z, (z - m) ∂ν = 0 := by
    rw [integral_sub hint (integrable_const m), hm, integral_const]
    simp
  have hfp : (∫⁻ y, ENNReal.ofReal (|y - m| ^ p) ∂ν) ≠ ⊤ := centeredMoment_ne_top ν hp hmom
  have hset : {ξ : V → ℝ | t ≤ |fluctOn G ξ m a b X|}
      = {ξ : V → ℝ | t ≤ |∑ v ∈ walkSites a b X, incWeight G a b X v * (ξ v - m)|} := by
    ext ξ
    simp only [Set.mem_setOf_eq, fluctOn_eq_sum_sites]
  have hw : ∀ v ∈ walkSites a b X,
      |incWeight G a b X v| ^ p * (RWRS.centeredMoment ν m p).toReal
        = incWeight G a b X v ^ p * (RWRS.centeredMoment ν m p).toReal := by
    intro v _
    rw [abs_of_nonneg (incWeight_nonneg a b X v)]
  rw [hset]
  refine le_trans (meas_weighted_sum_ge hFN (walkSites a b X) (incWeight G a b X) hf hfint hf0
    hfp t ht) (le_of_eq ?_)
  refine congrArg ENNReal.ofReal ?_
  refine congrArg (fun s : ℝ => Cp * s / t ^ p) ?_
  exact Finset.sum_congr rfl hw

/-! ### The weights against the local times -/

/-- The local time over `[a,b)` is the local time over `[0,b-a)` of the
trajectory started at time `a`. -/
theorem localTimeOn_eq_localTime (a b : ℕ) (v : V) (X : ℕ → V) :
    localTimeOn a b v X = RWRS.localTime (b - a) v (fun j => X (a + j)) := by
  unfold localTimeOn RWRS.localTime
  refine Finset.card_nbij' (fun j => j - a) (fun i => a + i) ?_ ?_ ?_ ?_
  · intro j hj
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_Ico, Finset.mem_range] at hj ⊢
    obtain ⟨⟨h1, h2⟩, h3⟩ := hj
    refine ⟨by omega, ?_⟩
    rw [show a + (j - a) = j by omega]
    exact h3
  · intro i hi
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_Ico, Finset.mem_range] at hi ⊢
    exact ⟨⟨by omega, by omega⟩, hi.2⟩
  · intro j hj
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_Ico] at hj
    show a + (j - a) = j
    omega
  · intro i _
    show a + i - a = i
    omega

/-- Degrees being at least one, the weight of a site is at most its local
time. -/
theorem incWeight_le_localTimeOn (hdeg : ∀ v : V, 1 ≤ G.degree v) (a b : ℕ) (X : ℕ → V)
    (v : V) : incWeight G a b X v ≤ (localTimeOn a b v X : ℝ) := by
  unfold incWeight
  refine div_le_self (Nat.cast_nonneg _) ?_
  exact_mod_cast hdeg v

/-- The `p`-th powers of the weights are dominated by those of the local
times. -/
theorem sum_incWeight_rpow_le (hdeg : ∀ v : V, 1 ≤ G.degree v) (a b : ℕ) (X : ℕ → V)
    {p : ℝ} (hp : 0 ≤ p) :
    ∑ v ∈ walkSites a b X, incWeight G a b X v ^ p
      ≤ ∑ v ∈ walkSites a b X, ((localTimeOn a b v X : ℝ)) ^ p :=
  Finset.sum_le_sum fun v _ =>
    Real.rpow_le_rpow (incWeight_nonneg a b X v) (incWeight_le_localTimeOn hdeg a b X v) hp

/-- The interval visits at most its own length of sites. -/
theorem card_walkSites_le (a b : ℕ) (X : ℕ → V) : (walkSites a b X).card ≤ b - a := by
  unfold walkSites
  refine le_trans Finset.card_image_le ?_
  rw [Nat.card_Ico]

/-- The local times over an interval add up to its length. -/
theorem sum_localTimeOn_eq (a b : ℕ) (X : ℕ → V) :
    ∑ v ∈ walkSites a b X, (localTimeOn a b v X : ℕ) = b - a := by
  unfold walkSites localTimeOn
  rw [← Finset.card_eq_sum_card_image X (Finset.Ico a b), Nat.card_Ico]

end RWRS.Support
