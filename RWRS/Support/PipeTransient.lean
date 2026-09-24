import RWRS.Support.PipeLevel
import RWRS.Support.Transience

namespace RWRS.Support

open scoped Classical

variable {B : ℕ} {α : ℝ}

/-- **The tree of pipes is transient.**  Thomson's principle against the unit
flow that sends current `B^{-n}` through every level-`n` pipe: its energy is the
convergent series `∑ L_n/B^n`. -/
theorem not_recurrent_pipeSub (hc : CombCond B α) :
    ¬ RWRS.Recurrent (pipeSub B (combLen B α)) (pipeRootSub B (combLen B α)) := by
  classical
  have hB : 1 ≤ B := le_trans (by norm_num) hc.1
  have hL : ∀ j, 1 ≤ j → 1 ≤ combLen B α j := fun j _ => one_le_combLen hc j
  have hL2 : ∀ j, 1 ≤ j → 2 ≤ combLen B α j := fun j hj => two_le_combLen hc hj
  haveI : Infinite (pipeSites B (combLen B α)) := pipeSites_infinite hB
  have hG : (pipeSub B (combLen B α)).Connected := pipeSub_connected hL
  refine not_recurrent_of_killedGreen_bound hG _ (2 * (1 - pipeRatio B α)⁻¹) ?_
  intro C ho hesc
  obtain ⟨q, -, hq⟩ := hesc (pipeRootSub B (combLen B α))
  have hthom := LatticeProb.Network.effRes_le_flowEnergy hG C ho hq
    (pipeFlow B (combLen B α)) (isFlow_pipeFlow hL)
    (fun x _ => by
      by_cases h : x = pipeRootSub B (combLen B α)
      · rw [if_pos h, h]
        exact divergence_pipeFlow_root hL hL2 hB
      · rw [if_neg h]
        exact divergence_pipeFlow_of_ne hL hL2 hB h)
  have henergy := flowEnergyOn_pipe_le hc
    (LatticeProb.Network.nbhd (pipeSub B (combLen B α)) C)
  have heq : RWRS.killedGreenReal (pipeSub B (combLen B α)) (C : Set _)
      (pipeRootSub B (combLen B α)) (pipeRootSub B (combLen B α))
      = LatticeProb.Network.effRes (pipeSub B (combLen B α)) C
        (pipeRootSub B (combLen B α)) := by
    rw [LatticeProb.Network.effRes, killedGreenReal_eq_lib]
  rw [heq]
  linarith

end RWRS.Support
