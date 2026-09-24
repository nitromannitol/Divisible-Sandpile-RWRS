/-
The stationary random rooted graphs and networks of `rwrs.tex`, Section 2,
after `BenjaminiCurien12`.

How the paper's objects are modelled here:

- A rooted network is a triple: for each vertex the list of its neighbours, a
  root, and `m` real marks per vertex, all on the vertex set `ℕ`.  Every
  locally finite connected rooted network has a countable vertex set and is
  isomorphic to one of these, so fixing the vertex set costs nothing, and
  encoding the graph by neighbour lists makes local finiteness automatic, which
  is a standing assumption of the paper.  The adjacency is the symmetric part
  of the list relation, so the graph is a `SimpleGraph ℕ` for every triple.
- `List ℕ` is given the discrete σ-algebra, so `Net m` carries the product
  σ-algebra of the three coordinates.  On the connected component of the root
  this is the Borel σ-algebra of the local topology, which is the σ-algebra the
  paper's "non-negative Borel function on the space of isomorphism classes"
  refers to; that a function is a function of the isomorphism class is
  `NetInvariant`.
- Stationarity is the displayed identity of `def:stationary-graph`, tested
  against every isomorphism-invariant measurable `h` with values in `[0,∞]`, so
  that no integrability side condition is needed.
- A rerooting-invariant event is a measurable set of networks that is
  isomorphism invariant and unchanged by moving the root to a neighbour.
  `invariantSigma` is the σ-algebra `I_G` of those events, and `IsErgodicNet` is
  triviality of that σ-algebra.  For a rooted NETWORK an event of `I_G` may read
  the marks: the paper says the notions of stationarity, rerooting-invariance
  and ergodicity "extend verbatim, with `h(G,v,σ)` replacing `h(G,v)`"
  (`rwrs.tex:252`).  At `m = 0` there are no marks and the definition is
  `def:ergodic-graph` for rooted graphs.
-/
import RWRS.Setting

open MeasureTheory
open scoped ENNReal

namespace RWRS

instance : MeasurableSpace (List ℕ) := ⊤

instance : DiscreteMeasurableSpace (List ℕ) := ⟨fun _ => trivial⟩

/-- A rooted network with `m` real marks per vertex: the neighbour lists, the
root, and the marks. -/
abbrev Net (m : ℕ) : Type := (ℕ → List ℕ) × ℕ × (ℕ → Fin m → ℝ)

/-- The graph of a rooted network: `i` and `j` are adjacent when each is
listed as a neighbour of the other. -/
def netGraph {m : ℕ} (N : Net m) : SimpleGraph ℕ where
  Adj i j := i ≠ j ∧ j ∈ N.1 i ∧ i ∈ N.1 j
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

noncomputable instance netLocallyFinite {m : ℕ} (N : Net m) : (netGraph N).LocallyFinite :=
  fun v => Set.Finite.fintype
    (Set.Finite.subset (N.1 v).finite_toSet (fun _ hj => hj.2.1))

/-- The root of a rooted network. -/
def netRoot {m : ℕ} (N : Net m) : ℕ := N.2.1

/-- The marks of a rooted network. -/
def netMark {m : ℕ} (N : Net m) : ℕ → Fin m → ℝ := N.2.2

/-- The single mark of a one-mark network, read as a sandpile configuration. -/
def netConfig (N : Net 1) : ℕ → ℝ := fun i => netMark N i 0

/-- The network rerooted at `y`. -/
def netReroot {m : ℕ} (N : Net m) (y : ℕ) : Net m := (N.1, y, N.2.2)

/-- The rooted network is connected; on a vertex set equal to `ℕ` this makes it
infinite, which is the paper's standing assumption. -/
def NetGood {m : ℕ} (N : Net m) : Prop := (netGraph N).Connected

/-- Two rooted networks are isomorphic: a bijection of the vertex sets carrying
the root to the root, the adjacency to the adjacency, and the marks to the
marks. -/
def NetIso {m : ℕ} (N N' : Net m) : Prop :=
  ∃ φ : ℕ ≃ ℕ, (∀ i j, (netGraph N).Adj i j ↔ (netGraph N').Adj (φ i) (φ j)) ∧
    φ (netRoot N) = netRoot N' ∧ ∀ i, netMark N i = netMark N' (φ i)

/-- A function of rooted networks that depends only on the isomorphism class. -/
def NetInvariant {m : ℕ} (h : Net m → ℝ≥0∞) : Prop := ∀ N N', NetIso N N' → h N = h N'

/-- A set of rooted networks that depends only on the isomorphism class. -/
def NetInvariantSet {m : ℕ} (A : Set (Net m)) : Prop := ∀ N N', NetIso N N' → (N ∈ A ↔ N' ∈ A)

/-- A set of rooted networks unchanged by moving the root to a neighbour. -/
def RerootInvariant {m : ℕ} (A : Set (Net m)) : Prop :=
  ∀ (N : Net m) (y : ℕ), (netGraph N).Adj (netRoot N) y → (N ∈ A ↔ netReroot N y ∈ A)

/-- A set of rooted networks that depends on the graph and the root only.  At
`m = 0` this is exactly measurability, the mark coordinate being a
subsingleton; at `m ≥ 1` it is the mark-blind restriction, which the paper
imposes on the `I_G` of `rwrs.tex:244` and not on the invariant events of a
marked network. -/
def GraphMeasurableSet {m : ℕ} (A : Set (Net m)) : Prop :=
  ∃ B : Set ((ℕ → List ℕ) × ℕ), MeasurableSet B ∧ A = (fun N : Net m => (N.1, N.2.1)) ⁻¹' B

/-- The σ-algebra of rerooting-invariant events of the marked object.  At
`m = 0` it is the `I_G` of `rwrs.tex:244`; at `m ≥ 1` its events may read the
marks, the paper's notions extending "verbatim, with `h(G,v,σ)` replacing
`h(G,v)`" (`rwrs.tex:252`). -/
@[reducible] def invariantSigma (m : ℕ) : MeasurableSpace (Net m) where
  MeasurableSet' A := MeasurableSet A ∧ NetInvariantSet A ∧ RerootInvariant A
  measurableSet_empty :=
    ⟨MeasurableSet.empty, fun _ _ _ => Iff.rfl, fun _ _ _ => Iff.rfl⟩
  measurableSet_compl := by
    rintro A ⟨hA, hiso, hre⟩
    exact ⟨hA.compl, fun N N' h => not_congr (hiso N N' h),
      fun N y h => not_congr (hre N y h)⟩
  measurableSet_iUnion := by
    intro f hf
    refine ⟨MeasurableSet.iUnion fun i => (hf i).1, ?_, ?_⟩
    · intro N N' h; simp only [Set.mem_iUnion]
      exact exists_congr fun i => (hf i).2.1 N N' h
    · intro N y h; simp only [Set.mem_iUnion]
      exact exists_congr fun i => (hf i).2.2 N y h

/-- The rooted graph underlying a rooted network: the neighbour lists and the
root are kept and the marks are forgotten. -/
def forgetMarks {m : ℕ} (N : Net m) : Net 0 := (N.1, N.2.1, fun _ j => Fin.elim0 j)

/-- The σ-algebra `I_G` of `rwrs.tex:244` read on networks with `m` marks: the
rerooting-invariant events of the UNDERLYING ROOTED GRAPH, pulled back along
`forgetMarks`.  Its events are exactly the measurable, isomorphism-invariant,
rerooting-invariant sets that are also `GraphMeasurableSet`, so at `m = 0` it is
`invariantSigma 0`, and at `m ≥ 1` it is strictly smaller than
`invariantSigma m`: on the rooted line with i.i.d. marks the event that every
mark vanishes is invariant but not graph-measurable.  This is the σ-algebra the
paper conditions on in `lem:01-stationary` and in the proof of
`thm:stationary-phase`, where it insists that `I_G ⊆ σ(G,ρ)` (`rwrs.tex:337`)
and that the conditioning event is graph-measurable (`rwrs.tex:347`). -/
@[reducible] def graphInvariantSigma (m : ℕ) : MeasurableSpace (Net m) :=
  MeasurableSpace.comap (@forgetMarks m) (invariantSigma 0)

/-- The stationarity identity of `def:stationary-graph`, extended to networks:
the law of `(G,ρ)` is the law of `(G,X_1)` for a uniform neighbour `X_1` of the
root. -/
def IsStationaryNet {m : ℕ} (P : Measure (Net m)) : Prop :=
  ∀ h : Net m → ℝ≥0∞, Measurable h → NetInvariant h →
    ∫⁻ N, h N ∂P
      = ∫⁻ N, (∑ y ∈ (netGraph N).neighborFinset (netRoot N), h (netReroot N y))
          / ((netGraph N).degree (netRoot N) : ℝ≥0∞) ∂P

/-- Ergodicity of `def:ergodic-graph`: every rerooting-invariant event has
probability `0` or `1`. -/
def IsErgodicNet {m : ℕ} (P : Measure (Net m)) : Prop :=
  ∀ A : Set (Net m), (invariantSigma m).MeasurableSet' A → P A = 0 ∨ P A = 1

/-- The one-mark network obtained by decorating the rooted graph `N` with an
i.i.d. field of marks with common law `ν`, sampled independently. -/
noncomputable def markIid (Q : Measure (Net 0)) (ν : Measure ℝ) : Measure (Net 1) :=
  (Q.prod (iidLaw ℕ ν)).map (fun p => (p.1.1, p.1.2.1, fun i (_ : Fin 1) => p.2 i))

/-- The two-mark network `(G,ρ,σ_k,u_k)` after `k` rounds of parallel toppling. -/
noncomputable def netTopple (N : Net 1) (k : ℕ) : Net 2 :=
  (N.1, N.2.1, fun i j =>
    if j = 0 then config (netGraph N) (netConfig N) k i
    else odometer (netGraph N) (netConfig N) k i)

/-- The degree-weighted mass at the root, `σ(ρ)/deg(ρ)`. -/
noncomputable def netWeightedMass (N : Net 1) : ℝ :=
  netConfig N (netRoot N) / ((netGraph N).degree (netRoot N) : ℝ)

/-- The degree-weighted mass at the root after `k` rounds, `σ_k(ρ)/deg(ρ)`. -/
noncomputable def netWeightedMassAt (N : Net 1) (k : ℕ) : ℝ :=
  config (netGraph N) (netConfig N) k (netRoot N) / ((netGraph N).degree (netRoot N) : ℝ)

end RWRS
