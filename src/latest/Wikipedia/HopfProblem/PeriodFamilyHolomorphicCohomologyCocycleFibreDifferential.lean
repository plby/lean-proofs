import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyCocycleFibreSections
import Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomologyGlobalFourierOperators

/-!
# Actual constant native differentials on the original fibres

The negative local primitives on the actual restricted family cover
all have the restriction of the same genuine constant pair of native
smooth sections as their original Dolbeault differential. This pair
is closed, and its native Haar-mean coordinates are exactly the
negative marked antiholomorphic coefficients. No comparison of an
extension class with a Dolbeault class is asserted in this file.
-/

noncomputable section

open CategoryTheory TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.CocycleFibre

open HolomorphicFunctionSheaf.SphereH1

variable {V : Type*} {B : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B]

/-- The actual global constant pair of native smooth sections on the
original fibre, with the negative marked differential coefficients. -/
def fibreConstantPair (P : HolomorphicPeriodMap V B) (b : B)
    (a : Cocycle.Coefficients V B) :
    PeriodTorusHolomorphicCohomology.Dolbeault.PairSection (P.point b) ⊤ :=
  PeriodTorusHolomorphicCohomology.GlobalFourier.constantPairSection (P.point b)
    (-MarkedLinear.dbarLinear (P.point b) (fun j => a j b))

/-- The genuine constant pair is closed for the actual top native
Dolbeault differential. -/
theorem fibreConstantPair_closed (P : HolomorphicPeriodMap V B) (b : B)
    (a : Cocycle.Coefficients V B) :
    PeriodTorusHolomorphicCohomology.Dolbeault.topSection (P.point b) ⊤
      (fibreConstantPair P b a) = 0 :=
  PeriodTorusHolomorphicCohomology.GlobalFourier.top_constantPairSection (P.point b)
    (-MarkedLinear.dbarLinear (P.point b) (fun j => a j b))

/-- The coordinates here are the literal normalized Haar means of the
actual native global coefficients, with no transported scalar action. -/
theorem fibreConstantPair_mean (P : HolomorphicPeriodMap V B) (b : B)
    (a : Cocycle.Coefficients V B) :
    PeriodTorusHolomorphicCohomology.GlobalFourier.pairMean (P.point b)
      (fibreConstantPair P b a) = -MarkedLinear.dbarLinear (P.point b) (fun j => a j b) :=
  PeriodTorusHolomorphicCohomology.GlobalFourier.pairMean_constant (P.point b)
    (-MarkedLinear.dbarLinear (P.point b) (fun j => a j b))

variable [IsManifold (modelWithCornersSelf ℂ V) ω B]

/-- Pointwise differentiation of the actual negative primitive gives
the negative literal marked coefficient, at every actual cover point. -/
theorem derivativeSection_fibreNegativeSection_apply (P : HolomorphicPeriodMap V B)
    (b : B) (a : Cocycle.Coefficients V B) (i : B × ComplexPlane₂) (k : Fin 2)
    (t : fibreCover P b i) :
    PeriodTorusHolomorphicCohomology.Dolbeault.derivativeSection (P.point b) k
      (fibreCover P b i) (fibreNegativeSection P b a i) t =
        -MarkedLinear.dbarLinear (P.point b) (fun j => a j b) k :=
  derivativeSection_negativeLocalSection_apply (P.point b) (fun j => a j b)
    (fibreCover P b i) (fibreLift P b i) (fibreLift_holomorphic P b i)
    (fun _ ht => fibreLift_project P b i ht) k t

/-- The actual native Dolbeault differential of every local primitive
is the actual restriction of the same original global coefficient pair. -/
theorem fibreNegativeSection_differential (P : HolomorphicPeriodMap V B) (b : B)
    (a : Cocycle.Coefficients V B) (i : B × ComplexPlane₂) :
    PeriodTorusHolomorphicCohomology.Dolbeault.differentialSection (P.point b)
        (fibreCover P b i) (fibreNegativeSection P b a i) =
      PeriodTorusHolomorphicCohomology.Dolbeault.pairRestriction (P.point b) le_top
        (fibreConstantPair P b a) := by
  apply Prod.ext
  · apply ContMDiffMap.ext
    intro t
    exact derivativeSection_fibreNegativeSection_apply P b a i 0 t
  · apply ContMDiffMap.ext
    intro t
    exact derivativeSection_fibreNegativeSection_apply P b a i 1 t

/-- The same equality stated with the genuine differential sheaf map
and the genuine sheaf restriction of its original global pair. -/
theorem fibreNegativeSection_differential_sheaf (P : HolomorphicPeriodMap V B) (b : B)
    (a : Cocycle.Coefficients V B) (i : B × ComplexPlane₂) :
    (PeriodTorusHolomorphicCohomology.Dolbeault.differential (P.point b)).hom.app
        (Opposite.op (fibreCover P b i)) (fibreNegativeSection P b a i) =
      res (PeriodTorusHolomorphicCohomology.Dolbeault.pairSheaf (P.point b)) le_top
        (fibreConstantPair P b a) :=
  fibreNegativeSection_differential P b a i

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.CocycleFibre
