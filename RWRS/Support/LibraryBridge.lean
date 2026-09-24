/-
The identification of the walk objects of this repository with the shared
library's, and the first-passage facts of the library restated in this
repository's vocabulary.

The two developments define the transition kernel by the same first-step
recursion, so the identification is an induction on the number of steps; every
other object is built from the kernel and follows at once.
-/
import RWRS.Support.HeatBasic
import LatticeProb.Network.FirstPassage

namespace RWRS.Support

open scoped ENNReal

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

/-! ### The identification -/

theorem heat_eq_lib : ∀ (k : ℕ) (x y : V), heat G k x y = LatticeProb.Graph.heat G k x y := by
  intro k
  induction k with
  | zero => intro x y; rfl
  | succ k ih =>
      intro x y
      rw [heat_succ, LatticeProb.Graph.heat_succ, walkOp, LatticeProb.Graph.walkOp]
      exact congrArg (· / (G.degree x : ℝ)) (Finset.sum_congr rfl fun z _ => ih z y)

theorem meanLocalTime_eq_lib (n : ℕ) (x y : V) :
    meanLocalTime G n x y = LatticeProb.Graph.meanLocalTime G n x y :=
  Finset.sum_congr rfl fun k _ => heat_eq_lib k x y

theorem greenTime_eq_lib (n : ℕ) (x y : V) :
    greenTime G n x y = LatticeProb.Graph.greenTime G n x y :=
  congrArg (· / (G.degree y : ℝ)) (meanLocalTime_eq_lib n x y)

theorem supGreenTime_eq_lib (n : ℕ) (x : V) :
    supGreenTime G n x = LatticeProb.Graph.supGreenTime G n x :=
  iSup_congr fun v => congrArg ENNReal.ofReal (greenTime_eq_lib n x v)

/-! ### The library's first-passage facts -/

theorem heat_reversible (k : ℕ) (x y : V) :
    (G.degree x : ℝ) * heat G k x y = (G.degree y : ℝ) * heat G k y x := by
  rw [heat_eq_lib, heat_eq_lib]
  exact LatticeProb.Network.heat_reversible k x y

theorem meanLocalTime_nonneg (n : ℕ) (x y : V) : 0 ≤ meanLocalTime G n x y := by
  rw [meanLocalTime_eq_lib]; exact LatticeProb.Network.meanLocalTime_nonneg n x y

theorem meanLocalTime_mono (n : ℕ) (x y : V) :
    meanLocalTime G n x y ≤ meanLocalTime G (n + 1) x y := by
  rw [meanLocalTime_eq_lib, meanLocalTime_eq_lib]
  exact LatticeProb.Network.meanLocalTime_mono n x y

open scoped Classical in
theorem meanLocalTime_succ (n : ℕ) (x y : V) :
    meanLocalTime G (n + 1) x y
      = (if x = y then 1 else 0) + walkOp G (fun z => meanLocalTime G n z y) x := by
  rw [meanLocalTime_eq_lib, LatticeProb.Network.meanLocalTime_succ, walkOp,
    LatticeProb.Graph.walkOp]
  exact congrArg _ (congrArg (· / (G.degree x : ℝ))
    (Finset.sum_congr rfl fun z _ => (meanLocalTime_eq_lib n z y).symm))

theorem meanLocalTime_le_self (n : ℕ) (x y : V) :
    meanLocalTime G n x y ≤ meanLocalTime G n y y := by
  rw [meanLocalTime_eq_lib, meanLocalTime_eq_lib]
  exact LatticeProb.Network.meanLocalTime_le_self n x y

theorem greenTime_le_diag [Nontrivial V] (hG : G.Connected) (n : ℕ) (o v : V) :
    greenTime G n o v ≤ greenTime G n o o := by
  rw [greenTime_eq_lib, greenTime_eq_lib]
  exact LatticeProb.Network.greenTime_le_diag hG n o v

theorem supGreenTime_le [Nontrivial V] (hG : G.Connected) (n : ℕ) (o : V) :
    supGreenTime G n o ≤ ENNReal.ofReal (greenTime G n o o) := by
  rw [supGreenTime_eq_lib, greenTime_eq_lib]
  exact LatticeProb.Network.supGreenTime_le hG n o

theorem meanLocalTime_reversible (n : ℕ) (x y : V) :
    (G.degree x : ℝ) * meanLocalTime G n x y = (G.degree y : ℝ) * meanLocalTime G n y x := by
  rw [meanLocalTime_eq_lib, meanLocalTime_eq_lib]
  exact LatticeProb.Network.meanLocalTime_reversible n x y

/-- The finite-time Green function read from the reversed walk. -/
theorem greenTime_eq_meanLocalTime [Infinite V] (hG : G.Connected) (n : ℕ) (o v : V) :
    greenTime G n o v = meanLocalTime G n v o / (G.degree o : ℝ) := by
  have hdo : (0 : ℝ) < (G.degree o : ℝ) := by exact_mod_cast degree_pos hG o
  have hdv : (0 : ℝ) < (G.degree v : ℝ) := by exact_mod_cast degree_pos hG v
  rw [greenTime, div_eq_div_iff hdv.ne' hdo.ne']
  linarith [meanLocalTime_reversible (G := G) n o v]

end RWRS.Support
