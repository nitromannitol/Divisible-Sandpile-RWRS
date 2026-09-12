/-
Proposition 5.17 of `rwrs.tex`, frozen.  `rwrs.tex:1229-1241` (label
`prop:poly-growth`):

  "Let $G=(V,E)$ be an infinite, locally finite, connected graph with degree
   bounded by $d$.  Assume:
   (H1) (Volume growth) $|B(o,r)|\leq C_{\mathrm{vol}}r^{d_f}$ for some $o\in V$,
   $d_f>0$, and all $r\geq1$.
   (H2) (Spectral dimension) $\sup_{x\in V}\P_x(X_n=x)\leq An^{-d_s/2}$ for all
   $n\geq1$, for some $d_s\in(0,2)$ and $A<\infty$.
   (H3) (Walk dimension) For all $x\in V$, all $n\geq1$, and all $r\geq1$,
   $\P_x(\tau_{B(x,r)}\leq n)\leq C_{\mathrm{disp}}
     \exp(-c_{\mathrm{disp}}(r^{d_w}/n)^{1/(d_w-1)})$, for some $d_w\geq2$ and
   constants $C_{\mathrm{disp}},c_{\mathrm{disp}}>0$.
   Let $(\xi(v))_{v\in V}$ be i.i.d. and independent of the walk with
   $\E[\xi]\in[-\infty,0)$ and $\E[(\xi^+)^p]<\infty$ for some
   $p>\max(2d_f/(d_wd_s),1)$.  Then $\sup_\tau\E_o[S_\tau\mid\xi]<\infty$
   almost surely."

The three hypotheses are `VolumeGrowthUpper`, `SpectralDimensionBound` and
`WalkDimensionBound`; the vertex `o` of (H1) is the vertex of the conclusion.
The supremum over bounded stopping times is taken in `[0,∞]`.

The vertex set carries the discrete measurable structure, as `ssec:notation`
supplies it in substance and as `lem:dyadic`, `lem:good-walk` and
`prop:subcritical` already carry it: the proof reads the scenery along the
trajectory, and `(ξ,X) ↦ ξ(X_j)` is measurable exactly when the singletons of
the vertex set are.
-/
import RWRS.Support.SubPolyFinal

open MeasureTheory
open scoped ENNReal

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

-- The convention excluding the indeterminate mean is carried but not referred
-- to: the negativity of the mean already forces the positive part to be finite,
-- which is what the proof uses.
set_option linter.unusedVariables false in
-- FROZEN-STATEMENT-BEGIN
theorem RWRS.Frozen.polyGrowth [Infinite V] [MeasurableSpace V] [MeasurableSingletonClass V]
    (hG : G.Connected)
    (d : ℕ) (hd : RWRS.BoundedDegree G d) (o : V)
    (C_vol d_f : ℝ) (hdf : 0 < d_f) (hH1 : RWRS.VolumeGrowthUpper G o C_vol d_f)
    (d_s A : ℝ) (hds0 : 0 < d_s) (hds2 : d_s < 2)
    (hH2 : RWRS.SpectralDimensionBound G d_s A)
    (d_w C_disp c_disp : ℝ) (hdw : 2 ≤ d_w) (hCd : 0 < C_disp) (hcd : 0 < c_disp)
    (hH3 : RWRS.WalkDimensionBound G d_w C_disp c_disp)
    (ν : Measure ℝ) (hν : IsProbabilityMeasure ν) (hdet : RWRS.HasExtMean ν)
    (hmean : RWRS.extMean ν < 0)
    (p : ℝ) (hp : max (2 * d_f / (d_w * d_s)) 1 < p) (hmom : RWRS.posMoment ν p ≠ ⊤) :
    ∀ᵐ ξ ∂(RWRS.iidLaw V ν), RWRS.supStopValue G ξ o ≠ ⊤
-- FROZEN-STATEMENT-END
:= by
  haveI := hν
  haveI : Countable V := RWRS.Support.countable_of_connected hG
  exact RWRS.Support.ae_supStopValue_ne_top_poly hG d hd hdf o hH1 hds0 hds2 hH2 hdw hCd hcd
    hH3 ν hmean hp hmom
