/-
Almost every trajectory of the walk is a walk: at time `k` it is within distance
`k` of its starting vertex.

`prop:poly-growth` uses this in the bad-walk estimate of Step 5, "on `G`, every
vertex visited by time `N` satisfies `dist(o,v) ≤ N`, so `Y_k ≤ CN^{1+β}`".  The
trajectory is driven by an i.i.d. sequence of instructions in `[0,1)`, and an
instruction in `[0,1)` selects an index below the degree, hence a genuine
neighbour; the instructions lie in `[0,1)` almost surely because that is where
their common law is carried.
-/
import RWRS.Support.SubPolyBlock
import RWRS.Support.VoltageIdentity

namespace RWRS.Support

open MeasureTheory
open scoped ENNReal

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

/-- **An instruction in `[0,1)` selects a neighbour.** -/
theorem adj_stepTo {x : V} (hx : 0 < G.degree x) {u : ℝ} (h0 : 0 ≤ u) (h1 : u < 1) :
    G.Adj x (RWRS.stepTo G x u) := by
  have hdeg : (0:ℝ) < (G.degree x : ℝ) := by exact_mod_cast hx
  have hmul : (G.degree x : ℝ) * u < (G.degree x : ℝ) := by nlinarith
  have hlt : ⌊(G.degree x : ℝ) * u⌋₊ < G.degree x :=
    (Nat.floor_lt (by positivity)).2 (by exact_mod_cast hmul)
  have hcard : ⌊(G.degree x : ℝ) * u⌋₊ < (G.neighborFinset x).card := by
    rwa [SimpleGraph.card_neighborFinset_eq_degree]
  have hmem : RWRS.stepTo G x u ∈ G.neighborFinset x :=
    LatticeProb.Graph.getD_toList_mem (G.neighborFinset x) x hcard
  exact (SimpleGraph.mem_neighborFinset _ _ _).1 hmem

/-- **Almost every driver has all its instructions in `[0,1)`.** -/
theorem ae_driverLaw_mem_Ico :
    ∀ᵐ ω ∂(RWRS.driverLaw), ∀ k : ℕ, ω k ∈ Set.Ico (0:ℝ) 1 := by
  haveI hprob : IsProbabilityMeasure (RWRS.stepLaw) := by
    constructor
    rw [RWRS.stepLaw, Measure.restrict_apply_univ, Real.volume_Ico]
    norm_num
  haveI : ∀ i : ℕ, IsProbabilityMeasure ((fun _ : ℕ => RWRS.stepLaw) i) := fun _ => hprob
  refine (MeasureTheory.ae_all_iff).2 fun k => ?_
  have hmap : (RWRS.driverLaw).map (fun ω : ℕ → ℝ => ω k) = RWRS.stepLaw :=
    Measure.infinitePi_map_eval (fun _ : ℕ => RWRS.stepLaw) k
  have hz : RWRS.stepLaw (Set.Ico (0:ℝ) 1)ᶜ = 0 := by
    rw [RWRS.stepLaw, Measure.restrict_apply' measurableSet_Ico]
    simp
  rw [MeasureTheory.ae_iff]
  have hset : {ω : ℕ → ℝ | ¬ ω k ∈ Set.Ico (0:ℝ) 1}
      = (fun ω : ℕ → ℝ => ω k) ⁻¹' (Set.Ico (0:ℝ) 1)ᶜ := rfl
  rw [hset, ← Measure.map_apply (measurable_pi_apply k) measurableSet_Ico.compl, hmap]
  exact hz

/-- **A trajectory driven by instructions in `[0,1)` is a walk.** -/
theorem edist_walkPath_le (hdeg : ∀ v : V, 0 < G.degree v) (o : V) {ω : ℕ → ℝ}
    (hω : ∀ k : ℕ, ω k ∈ Set.Ico (0:ℝ) 1) (k : ℕ) :
    G.edist (RWRS.walkPath G o ω k) o ≤ (k : ℕ∞) := by
  induction k with
  | zero =>
      have : RWRS.walkPath G o ω 0 = o := rfl
      rw [this]
      simp
  | succ k ih =>
      have hstep : RWRS.walkPath G o ω (k + 1)
          = RWRS.stepTo G (RWRS.walkPath G o ω k) (ω k) := rfl
      have hadj : G.Adj (RWRS.walkPath G o ω k) (RWRS.walkPath G o ω (k + 1)) := by
        rw [hstep]
        exact adj_stepTo (hdeg _) (hω k).1 (hω k).2
      have h1 : G.edist (RWRS.walkPath G o ω (k + 1)) (RWRS.walkPath G o ω k) = 1 :=
        SimpleGraph.edist_eq_one_iff_adj.2 hadj.symm
      have htri : G.edist (RWRS.walkPath G o ω (k + 1)) o
          ≤ G.edist (RWRS.walkPath G o ω (k + 1)) (RWRS.walkPath G o ω k)
            + G.edist (RWRS.walkPath G o ω k) o := SimpleGraph.edist_triangle
      have hcast : (1 : ℕ∞) + (k : ℕ∞) = ((k + 1 : ℕ) : ℕ∞) := by
        push_cast
        ring
      calc G.edist (RWRS.walkPath G o ω (k + 1)) o
          ≤ G.edist (RWRS.walkPath G o ω (k + 1)) (RWRS.walkPath G o ω k)
            + G.edist (RWRS.walkPath G o ω k) o := htri
        _ ≤ 1 + (k : ℕ∞) := add_le_add (le_of_eq h1) ih
        _ = ((k + 1 : ℕ) : ℕ∞) := hcast

variable [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]

/-- **Almost every trajectory of the walk started at `o` is at distance at most
`k` from `o` at time `k`.** -/
theorem ae_edist_le (hdeg : ∀ v : V, 0 < G.degree v) (o : V) :
    ∀ᵐ X ∂(RWRS.walkLaw G o), ∀ k : ℕ, G.edist (X k) o ≤ (k : ℕ∞) := by
  have hmeas : MeasurableSet {X : ℕ → V | ∀ k : ℕ, G.edist (X k) o ≤ (k : ℕ∞)} := by
    have heq : {X : ℕ → V | ∀ k : ℕ, G.edist (X k) o ≤ (k : ℕ∞)}
        = ⋂ k : ℕ, (fun X : ℕ → V => X k) ⁻¹' {v : V | G.edist v o ≤ (k : ℕ∞)} := by
      ext X
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
    rw [heq]
    exact MeasurableSet.iInter fun k =>
      (measurable_pi_apply k) (Set.to_countable _).measurableSet
  have hdl : LatticeProb.Graph.driverLaw = RWRS.driverLaw := rfl
  rw [walkLaw_eq_lib o, LatticeProb.Graph.walkLaw, hdl, MeasureTheory.ae_map_iff
    (LatticeProb.Graph.measurable_walkPath (G := G) o).aemeasurable hmeas]
  filter_upwards [ae_driverLaw_mem_Ico] with ω hω
  intro k
  have hpath : LatticeProb.Graph.walkPath G o ω k = RWRS.walkPath G o ω k :=
    (walkPath_eq_lib o ω k).symm
  rw [hpath]
  exact edist_walkPath_le hdeg o hω k

end RWRS.Support
