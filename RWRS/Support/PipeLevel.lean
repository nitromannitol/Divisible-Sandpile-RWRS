import RWRS.Support.PipeEnergy
import RWRS.Support.TrGood

namespace RWRS.Support

open scoped Classical

variable {B : ℕ} {L : ℕ → ℕ}

/-- The sites whose word has length `n`, inside the pipe of that level. -/
noncomputable def pipeLevelFinset (B : ℕ) (L : ℕ → ℕ) (n : ℕ) : Finset (List (Fin B) × ℕ) :=
  (wordsEq B n) ×ˢ Finset.range (L n + 1)

theorem mem_pipeLevelFinset {v : List (Fin B) × ℕ} (hv : PipeValid B L v) :
    v ∈ pipeLevelFinset B L v.1.length := by
  refine Finset.mem_product.2 ⟨mem_wordsEq rfl, Finset.mem_range.2 ?_⟩
  rcases hv with h0 | ⟨-, -, h2⟩
  · omega
  · omega

theorem card_pipeLevelFinset (n : ℕ) :
    (pipeLevelFinset B L n).card = B ^ n * (L n + 1) := by
  rw [pipeLevelFinset, Finset.card_product, card_wordsEq, Finset.card_range]

theorem length_of_mem_pipeLevelFinset {n : ℕ} {v : List (Fin B) × ℕ}
    (h : v ∈ pipeLevelFinset B L n) : v.1.length = n :=
  length_of_mem_wordsEq (Finset.mem_product.1 h).1

/-- **The sum of a function of the level over any finite set of sites** is at
most the sum over the levels it meets, weighted by the number of sites at each
level. -/
theorem sum_level_le (S : Finset (List (Fin B) × ℕ)) (hS : ∀ v ∈ S, PipeValid B L v)
    (g : ℕ → ℝ) (hg : ∀ n, 0 ≤ g n) (N : ℕ) (hN : ∀ v ∈ S, v.1.length ≤ N) :
    ∑ v ∈ S, g v.1.length
      ≤ ∑ n ∈ Finset.range (N + 1), ((B ^ n * (L n + 1) : ℕ) : ℝ) * g n := by
  classical
  set T : Finset (List (Fin B) × ℕ) :=
    (Finset.range (N + 1)).biUnion (pipeLevelFinset B L) with hT
  have hsub : S ⊆ T := by
    intro v hv
    exact Finset.mem_biUnion.2 ⟨v.1.length, Finset.mem_range.2 (by have := hN v hv; omega),
      mem_pipeLevelFinset (hS v hv)⟩
  have hdisj : (↑(Finset.range (N + 1)) : Set ℕ).PairwiseDisjoint (pipeLevelFinset B L) := by
    intro a _ b _ hab
    refine Finset.disjoint_left.2 ?_
    intro v hva hvb
    exact hab ((length_of_mem_pipeLevelFinset hva).symm.trans
      (length_of_mem_pipeLevelFinset hvb))
  calc ∑ v ∈ S, g v.1.length
      ≤ ∑ v ∈ T, g v.1.length :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun v _ _ => hg _)
    _ = ∑ n ∈ Finset.range (N + 1), ∑ v ∈ pipeLevelFinset B L n, g v.1.length :=
        Finset.sum_biUnion hdisj
    _ = ∑ n ∈ Finset.range (N + 1), ((B ^ n * (L n + 1) : ℕ) : ℝ) * g n := by
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [Finset.sum_congr rfl (fun v hv => by rw [length_of_mem_pipeLevelFinset hv]),
          Finset.sum_const, card_pipeLevelFinset, nsmul_eq_mul]

/-! ### The energy of the unit flow is finite -/

variable {α : ℝ}

/-- The ratio `B^{α-1}` of the geometric bound. -/
noncomputable def pipeRatio (B : ℕ) (α : ℝ) : ℝ := (B : ℝ) ^ α / (B : ℝ)

theorem pipeRatio_pos (hc : CombCond B α) : 0 < pipeRatio B α := by
  have hB : (2 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hc.1
  exact div_pos (Real.rpow_pos_of_pos (by linarith) _) (by linarith)

theorem pipeRatio_lt_one (hc : CombCond B α) : pipeRatio B α < 1 := by
  have hB : (2 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hc.1
  have hB1 : (1 : ℝ) < (B : ℝ) := by linarith
  have hlt : (B : ℝ) ^ α < (B : ℝ) ^ (1 : ℝ) :=
    Real.rpow_lt_rpow_left_iff hB1 |>.2 hc.2.2.1
  rw [Real.rpow_one] at hlt
  rw [pipeRatio, div_lt_one (by linarith)]
  exact hlt

theorem term_le (hc : CombCond B α) (n : ℕ) :
    ((B ^ n * (combLen B α n + 1) : ℕ) : ℝ) * (2 * (((B : ℝ) ^ n) ^ 2)⁻¹)
      ≤ 4 * (pipeRatio B α) ^ n := by
  have hB : (2 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hc.1
  have hBpos : (0 : ℝ) < (B : ℝ) := by linarith
  have ha : (0 : ℝ) < (B : ℝ) ^ n := pow_pos hBpos n
  have h4 : (4 : ℝ) ≤ (B : ℝ) ^ α := hc.2.2.2.1
  have hone : (1 : ℝ) ≤ ((B : ℝ) ^ α) ^ n := one_le_pow₀ (by linarith)
  have hL : (combLen B α n : ℝ) ≤ ((B : ℝ) ^ α) ^ n := combLen_le hc n
  have hcast : ((B ^ n * (combLen B α n + 1) : ℕ) : ℝ)
      = (B : ℝ) ^ n * ((combLen B α n : ℝ) + 1) := by push_cast; ring
  rw [hcast, pipeRatio, div_pow]
  rw [show (4 : ℝ) * (((B : ℝ) ^ α) ^ n / (B : ℝ) ^ n)
      = (4 * ((B : ℝ) ^ α) ^ n) / (B : ℝ) ^ n by ring]
  rw [le_div_iff₀ ha]
  have hkey : (B : ℝ) ^ n * ((combLen B α n : ℝ) + 1) * (2 * (((B : ℝ) ^ n) ^ 2)⁻¹)
      * (B : ℝ) ^ n = 2 * ((combLen B α n : ℝ) + 1) := by
    field_simp
  rw [hkey]
  linarith

theorem sum_term_le (hc : CombCond B α) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1),
        ((B ^ n * (combLen B α n + 1) : ℕ) : ℝ) * (2 * (((B : ℝ) ^ n) ^ 2)⁻¹)
      ≤ 4 * (1 - pipeRatio B α)⁻¹ := by
  have hr0 : 0 < pipeRatio B α := pipeRatio_pos hc
  have hr1 : pipeRatio B α < 1 := pipeRatio_lt_one hc
  have hsum : Summable (fun n : ℕ => (pipeRatio B α) ^ n) :=
    summable_geometric_of_lt_one hr0.le hr1
  calc ∑ n ∈ Finset.range (N + 1),
        ((B ^ n * (combLen B α n + 1) : ℕ) : ℝ) * (2 * (((B : ℝ) ^ n) ^ 2)⁻¹)
      ≤ ∑ n ∈ Finset.range (N + 1), 4 * (pipeRatio B α) ^ n :=
        Finset.sum_le_sum fun n _ => term_le hc n
    _ = 4 * ∑ n ∈ Finset.range (N + 1), (pipeRatio B α) ^ n := by rw [Finset.mul_sum]
    _ ≤ 4 * ∑' n : ℕ, (pipeRatio B α) ^ n := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        exact hsum.sum_le_tsum _ (fun n _ => pow_nonneg hr0.le n)
    _ = 4 * (1 - pipeRatio B α)⁻¹ := by rw [tsum_geometric_of_lt_one hr0.le hr1]

/-- **The energy of the unit flow over a finite set of sites** is bounded by any
bound for the level sums.  This is the finite-energy flow behind Thomson's
principle. -/
theorem flowEnergyOn_pipe_le_aux (hB : 1 ≤ B) (hL : ∀ j, 1 ≤ j → 1 ≤ L j)
    (hL2 : ∀ j, 1 ≤ j → 2 ≤ L j) (E : ℝ)
    (hE : ∀ N : ℕ, ∑ n ∈ Finset.range (N + 1),
      ((B ^ n * (L n + 1) : ℕ) : ℝ) * (2 * (((B : ℝ) ^ n) ^ 2)⁻¹) ≤ E)
    (S : Finset (pipeSites B L)) :
    LatticeProb.Network.flowEnergyOn (pipeSub B L)
        (LatticeProb.Network.unitCond (pipeSub B L)) S (pipeFlow B L) ≤ E := by
  classical
  have hnode : ∀ x : pipeSites B L,
      ∑ y ∈ (pipeSub B L).neighborFinset x,
          pipeFlow B L x y ^ 2 / LatticeProb.Network.unitCond (pipeSub B L) x y
        = pipeNodeEnergy B L (x : List (Fin B) × ℕ) := by
    intro x
    have hone : ∀ y ∈ (pipeSub B L).neighborFinset x,
        pipeFlow B L x y ^ 2 / LatticeProb.Network.unitCond (pipeSub B L) x y
          = pipeFlowAmb B L (x : List (Fin B) × ℕ) (y : List (Fin B) × ℕ) ^ 2 := by
      intro y hy
      have hadj : (pipeSub B L).Adj x y := (SimpleGraph.mem_neighborFinset _ _ _).1 hy
      rw [LatticeProb.Network.unitCond, if_pos hadj, div_one, pipeFlow]
    rw [Finset.sum_congr rfl hone]
    exact sum_neighborFinset_pipeSub x
      (fun y => pipeFlowAmb B L (x : List (Fin B) × ℕ) y ^ 2)
  rw [LatticeProb.Network.flowEnergyOn, Finset.sum_congr rfl (fun x _ => hnode x)]
  have himg : ∑ x ∈ S, pipeNodeEnergy B L (x : List (Fin B) × ℕ)
      = ∑ v ∈ S.image Subtype.val, pipeNodeEnergy B L v :=
    (Finset.sum_image (fun a _ b _ h => Subtype.ext h)).symm
  rw [himg]
  have hvalid : ∀ v ∈ S.image Subtype.val, PipeValid B L v := by
    intro v hv
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hv
    exact x.2
  calc ∑ v ∈ S.image Subtype.val, pipeNodeEnergy B L v
      ≤ ∑ v ∈ S.image Subtype.val, 2 * (((B : ℝ) ^ v.1.length) ^ 2)⁻¹ :=
        Finset.sum_le_sum fun v hv => pipeNodeEnergy_le hL hL2 hB (hvalid v hv)
    _ ≤ ∑ n ∈ Finset.range ((S.image Subtype.val).sup
          (fun v : List (Fin B) × ℕ => v.1.length) + 1),
          ((B ^ n * (L n + 1) : ℕ) : ℝ) * (2 * (((B : ℝ) ^ n) ^ 2)⁻¹) := by
        refine sum_level_le (S.image Subtype.val) hvalid
          (fun n => 2 * (((B : ℝ) ^ n) ^ 2)⁻¹) (fun n => by positivity) _
          (fun v hv => Finset.le_sup (f := fun v : List (Fin B) × ℕ => v.1.length) hv)
    _ ≤ E := hE _

/-- The unit flow of the tree of pipes has energy at most `4/(1-B^{α-1})`. -/
theorem flowEnergyOn_pipe_le (hc : CombCond B α) (S : Finset (pipeSites B (combLen B α))) :
    LatticeProb.Network.flowEnergyOn (pipeSub B (combLen B α))
        (LatticeProb.Network.unitCond (pipeSub B (combLen B α))) S (pipeFlow B (combLen B α))
      ≤ 4 * (1 - pipeRatio B α)⁻¹ :=
  flowEnergyOn_pipe_le_aux (le_trans (by norm_num) hc.1)
    (fun j _ => one_le_combLen hc j) (fun j hj => two_le_combLen hc hj) _
    (fun N => sum_term_le hc N) S

end RWRS.Support
