import Wikipedia.HopfProblem.PeriodFamilyHigherDirectImageGlobalStalk
import Wikipedia.HopfProblem.PeriodFamilyHigherDirectImageFibreComparison
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyCechConnectingFamily
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyMarkedLinearFrame

/-!
# Actual period-character germs in the native higher-direct-image stalk

The original global period-character Ext classes define genuine stalk
germs of the native first higher direct image. Their fibre evaluations
have exactly the original negative Dolbeault coordinates. No local
generation or local-freeness assertion about the higher-direct-image
sheaf is made here.
-/

noncomputable section

open CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage

open PeriodFamilyHolomorphicCohomology
open CuspNormalization.SheafCohomologyFinitePushforward
open FibreGeometry

variable {V : Type*} {B : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B] [IsManifold (modelWithCornersSelf ℂ V) ω B]

/-- The genuine higher-direct-image stalk germ of the actual global period class. -/
def periodStalkClass (P : HolomorphicPeriodMap V B) (b : B) :
    Cocycle.Coefficients V B →+ ↥(higherDirectImageStalk P b 1) :=
  (GlobalRestriction.globalStalkClass (Zero.projectionMap P) (Zero.totalAdditiveSheaf P) b 1).comp
    (Cocycle.periodClassHom P)

@[simp] theorem periodStalkClass_apply (P : HolomorphicPeriodMap V B) (b : B)
    (a : Cocycle.Coefficients V B) :
    periodStalkClass P b a =
      GlobalRestriction.globalStalkClass (Zero.projectionMap P) (Zero.totalAdditiveSheaf P) b 1
        (Cocycle.periodClass P a) := rfl

/-- Constant marked period values give literal bundled holomorphic base functions. -/
def constantPeriodCoefficients : (Fin 4 → ℂ) →ₗ[ℂ] Cocycle.Coefficients V B where
  toFun a j := ContMDiffMap.const (a j)
  map_add' a a' := by
    funext j
    apply ContMDiffMap.ext
    intro b
    rfl
  map_smul' c a := by
    funext j
    apply ContMDiffMap.ext
    intro b
    rfl

omit [IsManifold (modelWithCornersSelf ℂ V) ω B] in
@[simp] theorem constantPeriodCoefficients_apply (a : Fin 4 → ℂ) (j : Fin 4) (b : B) :
    constantPeriodCoefficients (V := V) (B := B) a j b = a j := rfl

/-- The first two original marked constant characters give actual stalk classes. -/
def firstPeriodStalkClass (P : HolomorphicPeriodMap V B) (b : B) :
    (Fin 2 → ℂ) →+ ↥(higherDirectImageStalk P b 1) :=
  (periodStalkClass P b).comp
    (constantPeriodCoefficients.toAddMonoidHom.comp
      MarkedLinear.firstCoefficients.toAddMonoidHom)

@[simp] theorem firstPeriodStalkClass_apply (P : HolomorphicPeriodMap V B) (b : B)
    (c : Fin 2 → ℂ) :
    firstPeriodStalkClass P b c =
      periodStalkClass P b (constantPeriodCoefficients (MarkedLinear.firstCoefficients c)) := rfl

variable [T2Space B]

/-- Fibre evaluation of a period germ is the actual coefficient restriction
of its original global extension class. -/
theorem fibreEvaluation_periodStalkClass (P : HolomorphicPeriodMap V B) (b : B)
    (a : Cocycle.Coefficients V B) :
    fibreEvaluation P b 1 (periodStalkClass P b a) =
      cohomologyEquiv (fibreMap P b) (fibreMap_isClosedMap P b) (fibreMap_finite_fibres P b)
        (PeriodTorusHolomorphicCohomology.holomorphicSheaf (P.point b)) 1
        (CategoryTheory.Sheaf.H.map (coefficientPullback P b) 1 (Cocycle.periodClass P a)) :=
  GlobalRestriction.derivedStalkEvaluation_global (Zero.projectionMap P) (Zero.totalAdditiveSheaf P)
    b 1 (fibreMap P b) (fibreMap_isClosedMap P b) (fibreMap_finite_fibres P b)
    (coefficientPullback P b) (projection_fibreMap_apply P b) (Cocycle.periodClass P a)

/-- The actual fibre coordinates of the genuine stalk class retain the
negative sign imposed by the original Čech convention. -/
theorem oneFibreCoordinates_periodStalkClass (P : HolomorphicPeriodMap V B) (b : B)
    (a : Cocycle.Coefficients V B) :
    oneFibreCoordinates P b (periodStalkClass P b a) =
      -MarkedLinear.dbarLinear (P.point b) (fun j => a j b) :=
  (congrArg (PeriodTorusHolomorphicCohomology.h1Equiv (P.point b))
    (fibreEvaluation_periodStalkClass P b a)).trans
      (CechConnecting.periodClass_fibre_coordinates P b a)

/-- The two original constant characters evaluate by the actual invertible
native Dolbeault marking, with no chosen replacement fibre basis. -/
theorem oneFibreCoordinates_firstPeriodStalkClass (P : HolomorphicPeriodMap V B) (b : B)
    (c : Fin 2 → ℂ) :
    oneFibreCoordinates P b (firstPeriodStalkClass P b c) =
      -MarkedLinear.firstDbarEquiv (P.point b) c :=
  oneFibreCoordinates_periodStalkClass P b
    (constantPeriodCoefficients (MarkedLinear.firstCoefficients c))

end Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage
