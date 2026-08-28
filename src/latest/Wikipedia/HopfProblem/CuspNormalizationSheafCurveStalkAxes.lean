import Wikipedia.HopfProblem.CuspNormalizationSheafCurveStalkBasic
import Wikipedia.HopfProblem.CuspNormalizationSheafLocalCoordinates
import Wikipedia.HopfProblem.CuspNormalizationSheafManifoldStalk

/-!
# Actual curve stalks in their genuine centered axis charts

The actual axis parametrization belongs to the existing analytic atlas
on the actual double curve. Its inverse gives a canonical comparison of
the actual categorical holomorphic stalk with one-variable analytic
germs at zero. The representative is literal composition with the axis
parametrization at the translated coordinate.
-/

noncomputable section

open Set Filter Topology TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspNormalization.SheafCurveStalk

open CuspQuotient ToricCharts ToricSpace ToricFan NormalizationCurves
  NormalizationLocalCoordinates SheafResolution SheafGermComplex

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
  (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε)

/-- The actual ring-valued holomorphic presheaf on the source-ordered
double curve, in its already constructed analytic structure. -/
abbrev curveRingPresheaf (k : Fin 3) :
    TopCat.Presheaf CommRingCat (TopCat.of (sourceDoubleCurve C ε hε k)) :=
  letI := curveChartedSpace C ε hε hε1 hC hR (sourceEdgeIndex k)
  HolomorphicFunctionSheaf.presheaf 𝓘(ℂ, ℂ) (sourceDoubleCurve C ε hε k)

/-- Literal holomorphic sections on an open set of the actual double curve. -/
abbrev CurveSection (k : Fin 3) (U : Opens (sourceDoubleCurve C ε hε k)) : Type :=
  letI := curveChartedSpace C ε hε hε1 hC hR (sourceEdgeIndex k)
  HolomorphicFunctionSheaf.Section 𝓘(ℂ, ℂ) (sourceDoubleCurve C ε hε k) U

variable (s : Triangle) (k : Fin 3) (t : ℂ)

local notation "α" => axisParametrization C ε hε hε1 hC hR s (sourceEdgeIndex k)
local notation "d" => axisSection C ε hε s (sourceEdgeIndex k) t

/-- The actual categorical curve stalk in the genuine centered axis chart. -/
def axisStalkEquiv :
    (curveRingPresheaf C ε hε hε1 hC hR k).stalk d ≃+* AxisGerm := by
  letI := curveChartedSpace C ε hε hε1 hC hR (sourceEdgeIndex k)
  letI := curve_isManifold C ε hε hε1 hC hR (sourceEdgeIndex k)
  exact SheafManifoldStalk.centeredChartEquiv (α).symm
    (axisParametrization_mem_maximalAtlas C ε hε hε1 hC hR s (sourceEdgeIndex k))
    d (axisSection_mem_target C ε hε hε1 hC hR s (sourceEdgeIndex k) t)

/-- A section in its literal centered axis coordinate. -/
def axisSectionRepresentative (U : Opens (sourceDoubleCurve C ε hε k))
    (f : CurveSection C ε hε hε1 hC hR k U) : ℂ → ℂ := by
  letI := curveChartedSpace C ε hε hε1 hC hR (sourceEdgeIndex k)
  exact fun z => HolomorphicFunctionSheaf.extendManifoldSection 𝓘(ℂ, ℂ) U f
    (axisSection C ε hε s (sourceEdgeIndex k) (t + z))

/-- The generic centered-chart representative is exactly the literal
translated axis representative. -/
theorem centeredRepresentative_axis (U : Opens (sourceDoubleCurve C ε hε k))
    (f : CurveSection C ε hε hε1 hC hR k U) :
    letI := curveChartedSpace C ε hε hε1 hC hR (sourceEdgeIndex k)
    SheafManifoldStalk.centeredRepresentative (α).symm d U f =
      axisSectionRepresentative C ε hε hε1 hC hR s k t U f := by
  let := curveChartedSpace C ε hε hε1 hC hR (sourceEdgeIndex k)
  funext z
  change HolomorphicFunctionSheaf.extendManifoldSection 𝓘(ℂ, ℂ) U f
      ((α) ((α).symm d + z)) =
    HolomorphicFunctionSheaf.extendManifoldSection 𝓘(ℂ, ℂ) U f
      (axisSection C ε hε s (sourceEdgeIndex k) (t + z))
  rw [axisParametrization_symm_apply, axisParametrization_apply]

/-- The literal representative is genuinely analytic at the origin. -/
theorem axisSectionRepresentative_analyticAt (U : Opens (sourceDoubleCurve C ε hε k))
    (f : CurveSection C ε hε hε1 hC hR k U) (hdU : d ∈ U) :
    AnalyticAt ℂ (axisSectionRepresentative C ε hε hε1 hC hR s k t U f) 0 := by
  let := curveChartedSpace C ε hε hε1 hC hR (sourceEdgeIndex k)
  have h := SheafManifoldStalk.centeredRepresentative_analyticAt (α).symm
    (axisParametrization_mem_maximalAtlas C ε hε hε1 hC hR s (sourceEdgeIndex k))
    d (axisSection_mem_target C ε hε hε1 hC hR s (sourceEdgeIndex k) t) U f hdU
  rw [centeredRepresentative_axis] at h
  exact h

@[simp] theorem axisSectionRepresentative_zero (U : Opens (sourceDoubleCurve C ε hε k))
    (f : CurveSection C ε hε hε1 hC hR k U) (hdU : d ∈ U) :
    axisSectionRepresentative C ε hε hε1 hC hR s k t U f 0 = f ⟨d, hdU⟩ := by
  let := curveChartedSpace C ε hε hε1 hC hR (sourceEdgeIndex k)
  change HolomorphicFunctionSheaf.extendManifoldSection 𝓘(ℂ, ℂ) U f
    (axisSection C ε hε s (sourceEdgeIndex k) (t + 0)) = _
  rw [add_zero, HolomorphicFunctionSheaf.extendManifoldSection_apply]

/-- The actual categorical germ maps to the actual analytic germ of
the section in the literal translated axis coordinate. -/
@[simp] theorem axisStalkEquiv_germ (U : Opens (sourceDoubleCurve C ε hε k))
    (hdU : d ∈ U) (f : CurveSection C ε hε hε1 hC hR k U) :
    axisStalkEquiv C ε hε hε1 hC hR s k t
        ((curveRingPresheaf C ε hε hε1 hC hR k).germ U d hdU f) =
      Germs.ofAnalytic (axisSectionRepresentative C ε hε hε1 hC hR s k t U f)
        (axisSectionRepresentative_analyticAt C ε hε hε1 hC hR s k t U f hdU) := by
  let := curveChartedSpace C ε hε hε1 hC hR (sourceEdgeIndex k)
  let := curve_isManifold C ε hε hε1 hC hR (sourceEdgeIndex k)
  have h := SheafManifoldStalk.centeredChartEquiv_germ (α).symm
    (axisParametrization_mem_maximalAtlas C ε hε hε1 hC hR s (sourceEdgeIndex k))
    d (axisSection_mem_target C ε hε hε1 hC hR s (sourceEdgeIndex k) t) U hdU f
  refine h.trans ((Germs.ofAnalytic_eq_iff _ _ _ _).mpr ?_)
  exact Eventually.of_forall fun z =>
    congrFun (centeredRepresentative_axis C ε hε hε1 hC hR s k t U f) z

/-- The centered analytic germ has the original actual section value
as its evaluation at the origin. -/
@[simp] theorem eval_axisStalkEquiv_germ (U : Opens (sourceDoubleCurve C ε hε k))
    (hdU : d ∈ U) (f : CurveSection C ε hε hε1 hC hR k U) :
    Germs.eval (0 : ℂ) (axisStalkEquiv C ε hε hε1 hC hR s k t
        ((curveRingPresheaf C ε hε hε1 hC hR k).germ U d hdU f)) = f ⟨d, hdU⟩ := by
  rw [axisStalkEquiv_germ, Germs.eval_ofAnalytic, axisSectionRepresentative_zero]

end Wikipedia.HopfProblem.CuspNormalization.SheafCurveStalk
