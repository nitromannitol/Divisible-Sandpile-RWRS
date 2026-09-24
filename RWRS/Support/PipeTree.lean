/-
The tree of pipes of `rwrs.tex`, Sections 6.4 to 6.6: the rooted `B`-ary tree
with each edge between generations `j-1` and `j` replaced by a path of length
`L_j`, the gadgets `H(m)`, and the combs `D_{w,n}`.

A site is a pair `(w, i)`.  The site `(w, 0)` is the branching vertex indexed by
the word `w`, the root being `([], 0)`, and `(w, i)` for `1 ≤ i ≤ L_{|w|} - 1`
is the `i`-th interior vertex of the pipe joining the branching vertex of the
parent of `w` to the branching vertex of `w`, numbered from the parent end.  A
pipe of length `L` therefore has `L` edges and `L - 1` interior sites.
`pipePred` is the neighbour one step nearer the root and the graph is the
symmetrization of that function, restricted to the sites that carry a meaning.
The pair `([], 1)` is not such a site, and it is exactly the extra boundary
vertex the comb may carry when it is embedded in a larger network: the flag `e`
turns it on, and then it is joined to the root by a single edge and to nothing
else, which is the paper's "extra boundary edge of unit resistance".
-/
import RWRS.Setting

namespace RWRS

/-- The site of the tree of pipes one step nearer the root. -/
def pipePred (B : ℕ) (L : ℕ → ℕ) : List (Fin B) × ℕ → List (Fin B) × ℕ
  | (w, 0) =>
      if w = [] then ([], 0)
      else if 2 ≤ L w.length then (w, L w.length - 1) else (w.dropLast, 0)
  | (w, i + 1) => if i = 0 then (w.dropLast, 0) else (w, i)

/-- The sites of the tree of pipes: the branching vertices and the interior
vertices of the pipes. -/
def PipeValid (B : ℕ) (L : ℕ → ℕ) (v : List (Fin B) × ℕ) : Prop :=
  v.2 = 0 ∨ (v.1 ≠ [] ∧ 1 ≤ v.2 ∧ v.2 ≤ L v.1.length - 1)

/-- The sites of the tree of pipes, together with the extra boundary vertex
`([], 1)` when the flag `e` is on. -/
def PipeValidPlus (B : ℕ) (L : ℕ → ℕ) (e : Bool) (v : List (Fin B) × ℕ) : Prop :=
  PipeValid B L v ∨ (e = true ∧ v = ([], 1))

/-- The tree of pipes over the rooted `B`-ary tree with pipe lengths `L`, with
the extra boundary edge at the root when `e` is on. -/
def pipeGraph (B : ℕ) (L : ℕ → ℕ) (e : Bool) : SimpleGraph (List (Fin B) × ℕ) where
  Adj u v := PipeValidPlus B L e u ∧ PipeValidPlus B L e v ∧ u ≠ v ∧
    (v = pipePred B L u ∨ u = pipePred B L v)
  symm := ⟨fun _ _ h => ⟨h.2.1, h.1, h.2.2.1.symm, h.2.2.2.symm⟩⟩
  loopless := ⟨fun _ h => h.2.2.1 rfl⟩

/-- A finite list containing every neighbour of a site. -/
def pipeNbrList (B : ℕ) (L : ℕ → ℕ) (v : List (Fin B) × ℕ) :
    List (List (Fin B) × ℕ) :=
  pipePred B L v :: (v.1, v.2 + 1) :: (v.1, 0) ::
    (List.finRange B).flatMap fun c => [(v.1 ++ [c], 0), (v.1 ++ [c], 1)]

theorem pipe_nbr_subset (B : ℕ) (L : ℕ → ℕ) (e : Bool) (v : List (Fin B) × ℕ) :
    (pipeGraph B L e).neighborSet v ⊆ {u | u ∈ pipeNbrList B L v} := by
  rintro ⟨w, i⟩ ⟨-, -, hne, hadj⟩
  simp only [Set.mem_setOf_eq, pipeNbrList, List.mem_cons, List.mem_flatMap,
    List.mem_finRange, true_and]
  rcases hadj with h | h
  · exact Or.inl h
  · refine Or.inr ?_
    match i, h with
    | 0, h =>
        by_cases hw : w = []
        · subst hw
          simp only [pipePred] at h
          exact absurd h hne
        · simp only [pipePred, if_neg hw] at h
          by_cases hL : 2 ≤ L w.length
          · rw [if_pos hL] at h
            subst h
            exact Or.inr (Or.inl rfl)
          · rw [if_neg hL] at h
            subst h
            obtain ⟨l, c, rfl⟩ : ∃ l c, w = l ++ [c] := by
              rcases List.eq_nil_or_concat w with h' | ⟨l, c, h'⟩
              · exact absurd h' hw
              · exact ⟨l, c, by simpa using h'⟩
            exact Or.inr (Or.inr ⟨c, by simp⟩)
    | i + 1, h =>
        by_cases hi : i = 0
        · subst hi
          simp only [pipePred] at h
          subst h
          by_cases hw : w = []
          · subst hw; exact Or.inl (by simp)
          · obtain ⟨l, c, rfl⟩ : ∃ l c, w = l ++ [c] := by
              rcases List.eq_nil_or_concat w with h' | ⟨l, c, h'⟩
              · exact absurd h' hw
              · exact ⟨l, c, by simpa using h'⟩
            exact Or.inr (Or.inr ⟨c, by simp⟩)
        · simp only [pipePred, if_neg hi] at h
          subst h
          exact Or.inl rfl

noncomputable instance pipeLocallyFinite (B : ℕ) (L : ℕ → ℕ) (e : Bool) :
    (pipeGraph B L e).LocallyFinite := fun v =>
  Set.Finite.fintype
    (Set.Finite.subset (pipeNbrList B L v).finite_toSet (pipe_nbr_subset B L e v))

/-! ### The pipe lengths, the gadgets and the combs -/

/-- The pipe lengths `L_j = ⌊B^{αj}⌋` of `ssec:comb-estimates`. -/
noncomputable def combLen (B : ℕ) (α : ℝ) (j : ℕ) : ℕ := ⌊(B : ℝ) ^ (α * j)⌋₊

/-- The conditions `eq:comb-B-cond` on `B` and `α`. -/
def CombCond (B : ℕ) (α : ℝ) : Prop :=
  2 ≤ B ∧ 1 / 2 < α ∧ α < 1 ∧ 4 ≤ (B : ℝ) ^ α ∧ 2 * (B : ℝ) ^ α ≤ (B : ℝ) - 1 ∧
    2 * (B : ℝ) ^ (1 - 2 * α) < 1 ∧ 1 < (B : ℝ) ^ (2 * α - 1) / 4

/-- `λ = B^{2α-1}/4` of `eq:comb-B-cond`. -/
noncomputable def combLambda (B : ℕ) (α : ℝ) : ℝ := (B : ℝ) ^ (2 * α - 1) / 4

/-- The root of the tree of pipes. -/
def pipeRoot (B : ℕ) : List (Fin B) × ℕ := ([], 0)

/-- `R_m = ∑_{j=1}^m L_j`, the distance from the root of `H(m)` to a
generation-`m` leaf. -/
def gadgetRadius (L : ℕ → ℕ) (m : ℕ) : ℕ := ∑ j ∈ Finset.Icc 1 m, L j

/-- `N_m = ∑_{j=1}^m B^j L_j`, the number of non-root vertices of `H(m)`. -/
def gadgetSize (B : ℕ) (L : ℕ → ℕ) (m : ℕ) : ℕ := ∑ j ∈ Finset.Icc 1 m, B ^ j * L j

/-- The sites of the gadget `H(m)`, the tree of pipes truncated at depth `m`. -/
def gadgetSites (B : ℕ) (L : ℕ → ℕ) (m : ℕ) : Set (List (Fin B) × ℕ) :=
  {v | PipeValid B L v ∧ v.1.length ≤ m}

/-- The gadget `H(m)`. -/
def gadgetGraph (B : ℕ) (L : ℕ → ℕ) (m : ℕ) : SimpleGraph (gadgetSites B L m) :=
  (pipeGraph B L false).induce (gadgetSites B L m)

/-- The comb `D_{w,n}`: the trunk from the root to the terminal pipe indexed by
`w`, together with the sibling pipes at each trunk branching vertex, with the
far endpoints excluded. -/
def combSet (B : ℕ) (L : ℕ → ℕ) (n : ℕ) (w : List (Fin B)) : Set (List (Fin B) × ℕ) :=
  {v | PipeValid B L v ∧ v.1.length ≤ n ∧ v.1.dropLast <+: w ∧
    (1 ≤ v.2 ∨ (v.1 <+: w ∧ v.1.length < n))}

/-- The first half of the terminal pipe `P_w`, the sites at distance at least
`L_n/2` from its far endpoint. -/
def combFirstHalf (B : ℕ) (L : ℕ → ℕ) (n : ℕ) (w : List (Fin B)) : Set (List (Fin B) × ℕ) :=
  {v | v.1 = w ∧ 1 ≤ v.2 ∧ 2 * v.2 ≤ L n}

/-- The root of the gadget `H(m)`. -/
def gadgetRoot (B : ℕ) (L : ℕ → ℕ) (m : ℕ) : gadgetSites B L m :=
  ⟨pipeRoot B, Or.inl rfl, Nat.zero_le m⟩

/-- The Pareto law with tail exponent `q`, `P(Y ≥ t) = t^{-q}` for `t ≥ 1`. -/
def IsPareto (ν : MeasureTheory.Measure ℝ) (q : ℝ) : Prop :=
  ∀ t : ℝ, 1 ≤ t → ν {z : ℝ | t ≤ z} = ENNReal.ofReal (t ^ (-q))

/-- The graph `G` with root `o` is the ray with the gadgets `H(m_k)` attached at
the ray vertices `r_{s_k}`, as in `sec:recurrent-nonstab`. -/
structure RayGadget {V : Type} (G : SimpleGraph V) (o : V) (B : ℕ) (L : ℕ → ℕ)
    (m s : ℕ → ℕ) (ray : ℕ → V) (φ : ∀ k, gadgetSites B L (m k) → V) : Prop where
  rayRoot : ray 0 = o
  rayInj : Function.Injective ray
  embInj : ∀ k, Function.Injective (φ k)
  attach : ∀ k, φ k (gadgetRoot B L (m k)) = ray (s k)
  meetsRay : ∀ (k : ℕ) (v : gadgetSites B L (m k)),
    φ k v ∈ Set.range ray → v = gadgetRoot B L (m k)
  disjoint : ∀ (k l : ℕ) (v : gadgetSites B L (m k)) (w : gadgetSites B L (m l)),
    k ≠ l → φ k v = φ l w → v = gadgetRoot B L (m k) ∧ w = gadgetRoot B L (m l)
  adj : ∀ x y : V, G.Adj x y ↔
    ((∃ i, x = ray i ∧ y = ray (i + 1)) ∨ (∃ i, y = ray i ∧ x = ray (i + 1)) ∨
      (∃ (k : ℕ) (v w : gadgetSites B L (m k)),
        (gadgetGraph B L (m k)).Adj v w ∧ x = φ k v ∧ y = φ k w))
  cover : ∀ x : V, x ∈ Set.range ray ∨ ∃ (k : ℕ) (v : gadgetSites B L (m k)), x = φ k v

/-- The voltage `g = g_{D_{w,n}}(b_0, ·)` on the comb. -/
noncomputable def combVoltage (B : ℕ) (L : ℕ → ℕ) (e : Bool) (n : ℕ) (w : List (Fin B))
    (v : List (Fin B) × ℕ) : ℝ :=
  killedGreenReal (pipeGraph B L e) (combSet B L n w) (pipeRoot B) v

/-- The trunk branching vertex `b_j`. -/
def combBranch (B : ℕ) (w : List (Fin B)) (j : ℕ) : List (Fin B) × ℕ := (w.take j, 0)

/-- The voltage `V_j = g(b_j)` at the `j`-th trunk branching vertex. -/
noncomputable def combV (B : ℕ) (L : ℕ → ℕ) (e : Bool) (n : ℕ) (w : List (Fin B)) (j : ℕ) : ℝ :=
  combVoltage B L e n w (combBranch B w j)

/-- The current `I_j` through the `j`-th trunk pipe, which for unit
conductances is the voltage drop across its first edge. -/
noncomputable def combI (B : ℕ) (L : ℕ → ℕ) (e : Bool) (n : ℕ) (w : List (Fin B)) (j : ℕ) : ℝ :=
  combVoltage B L e n w (combBranch B w (j - 1)) -
    combVoltage B L e n w (if 2 ≤ L j then (w.take j, 1) else (w.take j, 0))

/-- The effective resistance `R_j` from `b_j` to the boundary through the chosen
continuation branch, defined by Ohm's law `V_j = I_{j+1} R_j`. -/
noncomputable def combR (B : ℕ) (L : ℕ → ℕ) (e : Bool) (n : ℕ) (w : List (Fin B)) (j : ℕ) : ℝ :=
  combV B L e n w j / combI B L e n w (j + 1)

end RWRS
