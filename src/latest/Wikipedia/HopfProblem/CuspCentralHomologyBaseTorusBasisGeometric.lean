import Wikipedia.HopfProblem.CuspCentralHomologyBaseTorusBasisCoordinates
import Wikipedia.HopfProblem.CuspCentralHomologyBaseTorusBasisCurveHomeomorph

/-!
# The named double curves and the base section give the geometric basis

This final identification uses fundamental classes in the integral
homology of the literal named double curves, followed by their literal
inclusions. Together with the actual base-torus section class they are
the already proved four-element integral basis. The curve orientations
are the explicit suspension/connecting-map orientations fixed earlier.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspCentralHomology

open Module ToricSpace CuspRetraction SingularMayerVietoris PeriodTorusHigherHomology

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)

/-- The literal named double-curve inclusion into the actual central fibre. -/
def centralDoubleCurveCentralInclusion (j : Fin 3) :
    C(CuspQuotient.doubleCurve C r hr j, QuotientCentralFibre C r) :=
  (centralBoundaryInclusion C r hr).comp (centralDoubleCurveIntoBoundary C r hr j)

@[simp] theorem centralDoubleCurveCentralInclusion_coe (j : Fin 3)
    (q : CuspQuotient.doubleCurve C r hr j) :
    (centralDoubleCurveCentralInclusion C r hr j q).1 = q.1 := rfl

variable (hr1 : r < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))
    (hR : SmallDrift C r)

/-- Each ambient curve class is the pushforward of a generator of the
named curve's own second integral homology. -/
@[simp] theorem centralDoubleCurveCentralInclusion_fundamentalClass (j : Fin 3) :
    singularHomologyMap (centralDoubleCurveCentralInclusion C r hr j) 2
      (centralDoubleCurveOrientedFundamentalClass C r hr hr1 hC hR j) =
        centralDoubleCurveH2Class C r hr hr1 hC hR j := by
  rw [centralDoubleCurveCentralInclusion, singularHomologyMap_comp, LinearMap.comp_apply,
    centralDoubleCurveOrientedFundamentalClass_inclusion]
  rfl

/-- The first three basis vectors are the actual named double-curve
fundamental classes, not merely coordinates supported somewhere on `D`. -/
theorem baseTorusH2Basis_namedCurve (j : Fin 3) :
    baseTorusH2Basis C r hr hr1 hC hR j.castSucc =
      singularHomologyMap (centralDoubleCurveCentralInclusion C r hr j) 2
        (centralDoubleCurveOrientedFundamentalClass C r hr hr1 hC hR j) := by
  rw [baseTorusH2Basis_first, centralDoubleCurveCentralInclusion_fundamentalClass]

/-- The four specifically named geometric classes, in source order. -/
def namedCurveAndBaseClasses : Fin 4 → SingularHomology (QuotientCentralFibre C r) 2 :=
  ![singularHomologyMap (centralDoubleCurveCentralInclusion C r hr 0) 2
      (centralDoubleCurveOrientedFundamentalClass C r hr hr1 hC hR 0),
    singularHomologyMap (centralDoubleCurveCentralInclusion C r hr 1) 2
      (centralDoubleCurveOrientedFundamentalClass C r hr hr1 hC hR 1),
    singularHomologyMap (centralDoubleCurveCentralInclusion C r hr 2) 2
      (centralDoubleCurveOrientedFundamentalClass C r hr hr1 hC hR 2),
    baseTorusH2Class C r hr]

theorem namedCurveAndBaseClasses_eq_basis :
    namedCurveAndBaseClasses C r hr hr1 hC hR = baseTorusH2Basis C r hr hr1 hC hR := by
  funext j
  fin_cases j
  · exact (baseTorusH2Basis_namedCurve C r hr hr1 hC hR 0).symm
  · exact (baseTorusH2Basis_namedCurve C r hr hr1 hC hR 1).symm
  · exact (baseTorusH2Basis_namedCurve C r hr hr1 hC hR 2).symm
  · exact (baseTorusH2Basis_last C r hr hr1 hC hR).symm

theorem namedCurveAndBaseClasses_linearIndependent :
    LinearIndependent ℤ (namedCurveAndBaseClasses C r hr hr1 hC hR) := by
  rw [namedCurveAndBaseClasses_eq_basis]
  exact (baseTorusH2Basis C r hr hr1 hC hR).linearIndependent

theorem namedCurveAndBaseClasses_span :
    Submodule.span ℤ (Set.range (namedCurveAndBaseClasses C r hr hr1 hC hR)) = ⊤ := by
  rw [namedCurveAndBaseClasses_eq_basis]
  exact (baseTorusH2Basis C r hr hr1 hC hR).span_eq

end Wikipedia.HopfProblem.CuspCentralHomology
