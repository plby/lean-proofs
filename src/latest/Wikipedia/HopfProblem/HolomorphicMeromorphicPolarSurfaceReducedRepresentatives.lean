import Wikipedia.HopfProblem.HolomorphicMeromorphicPolarStalk

/-!
# Native holomorphic sections in centered surface coordinates

A genuine local holomorphic section is expressed in the given manifold
chart, centered at its base point and identified with `ℂ × ℂ` by the supplied
continuous complex-linear equivalence. The resulting analytic germ is
exactly the image under the existing original-stalk equivalence.
-/

open Set Filter Topology TopologicalSpace
open scoped Manifold ContDiff
open Wikipedia.HopfProblem.CuspNormalization.Germs

namespace Wikipedia.HopfProblem.HolomorphicMeromorphic.PolarSurfaceReduced

variable {E H M : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  [TopologicalSpace M] [ChartedSpace H M]

/-- The actual section extension composed with the genuine centered chart
inverse; this is not an abstract representative chosen from a germ. -/
noncomputable def surfaceSectionRepresentative (e : (ℂ × ℂ) ≃L[ℂ] E)
    (x : M) (U : Opens M) (A : HolomorphicFunctionSheaf.Section I M U) : ℂ × ℂ → ℂ :=
  fun z => HolomorphicFunctionSheaf.extendManifoldSection I U A
    ((extChartAt I x).symm (extChartAt I x x + e z))

variable [I.Boundaryless]

theorem surfaceSectionRepresentative_analyticAt (e : (ℂ × ℂ) ≃L[ℂ] E)
    (x : M) (U : Opens M) (hx : x ∈ U)
    (A : HolomorphicFunctionSheaf.Section I M U) :
    AnalyticAt ℂ (surfaceSectionRepresentative I e x U A) 0 := by
  have hcoord : AnalyticAt ℂ
      (fun z : ℂ × ℂ => extChartAt I x x + e z) 0 :=
    analyticAt_const.add (e.analyticAt 0)
  exact (HolomorphicFunctionSheaf.chartSectionRepresentative_analyticAt I x U A hx).comp_of_eq
    hcoord (by simp)

variable [IsManifold I ω M]

/-- The image of every native section germ is the literal centered-chart
representative, with no representative-compatibility premise. -/
theorem surfaceStalkEquiv_germ (e : (ℂ × ℂ) ≃L[ℂ] E)
    (x : M) (U : Opens M) (hx : x ∈ U)
    (A : HolomorphicFunctionSheaf.Section I M U) :
    PolarStalk.surfaceStalkEquiv I M e x
        ((HolomorphicFunctionSheaf.presheaf I M).germ U x hx A) =
      ofAnalytic (surfaceSectionRepresentative I e x U A)
        (surfaceSectionRepresentative_analyticAt I e x U hx A) := by
  rw [PolarStalk.surfaceStalkEquiv, RingEquiv.trans_apply,
    HolomorphicFunctionSheaf.chartStalkEquiv_germ,
    Coordinates.affinePullbackEquiv_ofAnalytic]
  apply (ofAnalytic_eq_iff _ _ _ _).mpr
  exact Eventually.of_forall fun z => by
    simp only [sub_zero, HolomorphicFunctionSheaf.chartSectionRepresentative,
      Function.comp_apply, surfaceSectionRepresentative]

end Wikipedia.HopfProblem.HolomorphicMeromorphic.PolarSurfaceReduced
