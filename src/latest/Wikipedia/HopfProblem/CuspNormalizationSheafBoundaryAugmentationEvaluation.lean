import Wikipedia.HopfProblem.CuspNormalizationSheafBoundaryAugmentationGeometry
import Wikipedia.HopfProblem.CuspNormalizationSheafTripleStalk

/-!
# Actual curve-stalk evaluations are analytic augmentation coefficients

The actual chart-selected curve point over a triple point is its actual
source-ordered triple point. Consequently evaluation of its genuine
centered analytic germ is precisely the scalar coefficient of the
actual sheaf evaluation morphism. Applying this to the actual finite
biproduct stalk comparison identifies every augmentation coefficient.
-/

noncomputable section

open Set TopologicalSpace CategoryTheory CategoryTheory.Limits
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspNormalization.SheafBoundaryAugmentation

open CuspQuotient ToricCharts ToricSpace ToricFan NormalizationCurves
  NormalizationLocalCoordinates SheafResolution SheafCurveStalk

attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
  (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε)

local notation "Base" => TopCat.of (CentralSpace C ε)
local notation "p" => triplePoint C ε hε

/-- The actual triple-point curve evaluation homomorphism is the actual
scalar stalk evaluation at the original point of the curve. -/
theorem curveStalkEvaluationHom_eq_scalarEvaluation (k : Fin 3) (t : Fin 2)
    (φ : (curveSheaf C ε hε hε1 hC hR k).presheaf.stalk (p t)) :
    letI := curveChartedSpace C ε hε hε1 hC hR (sourceEdgeIndex k)
    curveStalkEvaluationHom C ε hε hε1 hC hR k t φ =
      SheafEvaluation.stalkEvaluationAt 𝓘(ℂ, ℂ) (sourceCurveMap C ε hε k)
        (curveTriplePoint C ε hε k t) (p t)
        (sourceCurveMap_curveTriplePoint C ε hε k t) φ := by
  let := curveChartedSpace C ε hε hε1 hC hR (sourceEdgeIndex k)
  exact SheafEvaluation.evaluationAt_stalk 𝓘(ℂ, ℂ) (sourceCurveMap C ε hε k)
    (curveTriplePoint C ε hε k t) (p t)
    (sourceCurveMap_curveTriplePoint C ε hε k t) φ

private theorem curveScalarEvaluation_congr (k : Fin 3)
    (y z : sourceDoubleCurve C ε hε k) (x : CentralSpace C ε)
    (hy : sourceCurveMap C ε hε k y = x) (hz : sourceCurveMap C ε hε k z = x)
    (hyz : y = z) :
    letI := curveChartedSpace C ε hε hε1 hC hR (sourceEdgeIndex k)
    SheafEvaluation.stalkEvaluationAt 𝓘(ℂ, ℂ) (sourceCurveMap C ε hε k) y x hy =
      SheafEvaluation.stalkEvaluationAt 𝓘(ℂ, ℂ) (sourceCurveMap C ε hε k) z x hz := by
  subst z
  rfl

variable (a : Tube (disc ε)) (s : Triangle)

local notation "e" => normalizationChart C ε hε hε1 hC hR a s

/-- At an actual triple point, the actual analytic curve-stalk
comparison preserves the actual curve-evaluation coefficient. -/
theorem eval_curveStalkEquivAt_triplePoint (t : Fin 2)
    (hx : (p t).val ∈ (e).source) (k : Fin 3)
    (hk : sourcePair s k ⊆ Germs.activeBranches ((e) (p t).val))
    (φ : (curveSheaf C ε hε hε1 hC hR k).presheaf.stalk (p t)) :
    Germs.eval (0 : ℂ)
        (curveStalkEquivAt C ε hε hε1 hC hR a s (p t) hx k hk φ) =
      curveStalkEvaluationHom C ε hε hε1 hC hR k t φ := by
  let := curveChartedSpace C ε hε hε1 hC hR (sourceEdgeIndex k)
  let b := (e) (p t).val
  have hb : b ∈ (e).target := (e).map_source hx
  have hxb : (p t).val = (e).symm b := ((e).left_inv hx).symm
  let d := chartCurvePoint C ε hε hε1 hC hR a s b hb k hk
  have hd : sourceCurveMap C ε hε k d = p t :=
    chartCurvePoint_map C ε hε hε1 hC hR a s b hb (p t) hxb k hk
  have heq : d = curveTriplePoint C ε hε k t :=
    chartCurvePoint_eq_curveTriplePoint C ε hε hε1 hC hR a s b hb
      (p t) hxb k hk t rfl
  have hval := eval_curveStalkEquiv C ε hε hε1 hC hR a s b hb (p t) hxb k hk φ
  have hcongr := curveScalarEvaluation_congr C ε hε hε1 hC hR k
    d (curveTriplePoint C ε hε k t) (p t) hd
    (sourceCurveMap_curveTriplePoint C ε hε k t) heq
  exact hval.trans ((congrArg (fun f => f φ) hcongr).trans
    (curveStalkEvaluationHom_eq_scalarEvaluation C ε hε hε1 hC hR k t φ).symm)

/-- Each scalar coefficient of the actual boundary-stalk analytic
comparison equals the actual curve-evaluation coefficient on the
corresponding original finite-biproduct stalk factor. -/
theorem boundaryStalkEquivAt_eval_at_triplePoint (t : Fin 2)
    (hx : (p t).val ∈ (e).source)
    (β : (boundarySheaf C ε hε hε1 hC hR).presheaf.stalk (p t))
    (k : SheafBoundaryStalk.ActiveCurves s ((e) (p t).val)) :
    Germs.eval (0 : ℂ)
        (SheafBoundaryStalk.boundaryStalkEquivAt C ε hε hε1 hC hR a s (p t) hx β k) =
      curveStalkEvaluationHom C ε hε hε1 hC hR k.val t
        (SheafBiproduct.finiteStalkEquiv Base (curveSheaf C ε hε hε1 hC hR) (p t) β k.val) :=
  eval_curveStalkEquivAt_triplePoint C ε hε hε1 hC hR a s t hx k.val k.property
    (SheafBiproduct.finiteStalkEquiv Base (curveSheaf C ε hε hε1 hC hR) (p t) β k.val)

end Wikipedia.HopfProblem.CuspNormalization.SheafBoundaryAugmentation
