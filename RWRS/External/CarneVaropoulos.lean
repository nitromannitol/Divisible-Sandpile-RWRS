/-
The pointwise Carne--Varopoulos transition bound for simple random walk.
Sources: Carne (1985), Varopoulos (1985), and Lyons and Peres, *Probability
on Trees and Networks*, Theorem 13.4 (the citation at `rwrs.tex:143-149`). On a connected,
nontrivial, locally finite graph with the discrete measurable structure,
`P_x(X_n = y) ≤ 2 sqrt(deg(y)/deg(x)) exp(-dist(x,y)^2/(2n))` for `n ≥ 1`.
-/
import RWRS.Setting

-- FROZEN-STATEMENT-BEGIN
/-- The pointwise Carne--Varopoulos bound for simple random walk on a connected,
nontrivial, locally finite graph with measurable singletons. Sources: Carne
(1985), Varopoulos (1985), Lyons--Peres, Theorem 13.4 (`rwrs.tex:143-149`). -/
def RWRS.External.CarneVaropoulos {V : Type*} (G : SimpleGraph V) [G.LocallyFinite]
    [MeasurableSpace V] : Prop :=
  MeasurableSingletonClass V → Nontrivial V → G.Connected →
    ∀ (x y : V) (n : ℕ), 1 ≤ n →
      RWRS.walkLaw G x {X : ℕ → V | X n = y} ≤
        ENNReal.ofReal (2 * Real.sqrt ((G.degree y : ℝ) / G.degree x) *
          Real.exp (-((G.dist x y : ℝ) ^ 2) / (2 * n)))
-- FROZEN-STATEMENT-END
