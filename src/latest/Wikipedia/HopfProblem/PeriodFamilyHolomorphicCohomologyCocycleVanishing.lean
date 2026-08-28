import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyCocycleClass
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyCocyclePrimitive
import Wikipedia.HopfProblem.HolomorphicPicardCechExtensionClassZero

/-!
# Actual coboundaries of holomorphic linear period characters

If a character is obtained by evaluating a holomorphically varying
complex-linear form on the original period columns, its covering
primitive is that actual holomorphic form. Composing with the original
holomorphic local lifts supplies literal holomorphic zero-cochains.
The constructed period cocycle is their actual coboundary, so its
genuine native extension class vanishes.
-/

noncomputable section

open CategoryTheory TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.Cocycle

open HolomorphicFunctionSheaf.SphereH1

variable {V : Type*} {B : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B]

local notation "IT" => modelWithCornersSelf ℂ (V × ComplexPlane₂)

/-- The original period-column evaluation of holomorphic complex-linear
forms is an actual complex-linear map of coefficient spaces. -/
def linearCoefficientsLinearMap (P : HolomorphicPeriodMap V B) :
    LinearCoefficients V B →ₗ[ℂ] Coefficients V B where
  toFun := linearCoefficients P
  map_add' := linearCoefficients_add P
  map_smul' := linearCoefficients_smul P

@[simp] theorem linearCoefficientsLinearMap_apply (P : HolomorphicPeriodMap V B)
    (l : LinearCoefficients V B) :
    linearCoefficientsLinearMap P l = linearCoefficients P l := rfl

/-- The literal complex-linear primitive is holomorphic on the original
upstairs product manifold. -/
theorem linearPrimitive_holomorphic (l : LinearCoefficients V B) :
    letI := coverChartedSpace (V := V) (B := B)
    ContMDiff IT 𝓘(ℂ) ω (linearPrimitive l) := by
  let := coverChartedSpace (V := V) (B := B)
  rw [modelWithCornersSelf_prod]
  apply contMDiff_finsetSum
  intro k _
  exact ((l k).contMDiff.comp contMDiff_fst).mul
    (contMDiff_pi_space.mp contMDiff_snd k)

variable [IsManifold (modelWithCornersSelf ℂ V) ω B]

/-- The actual holomorphic local primitive on an original quotient-cover
open, in the original family atlas. -/
def linearLocalSection (P : HolomorphicPeriodMap V B) (l : LinearCoefficients V B)
    (i : B × ComplexPlane₂) : NativeSection P (coverOpen P i) := by
  let := coverChartedSpace (V := V) (B := B)
  letI := P.totalChartedSpace
  exact ⟨fun x => linearPrimitive l (liftOn P i x),
    (linearPrimitive_holomorphic l).comp (liftOn_holomorphic P i)⟩

@[simp] theorem linearLocalSection_apply (P : HolomorphicPeriodMap V B)
    (l : LinearCoefficients V B) (i : B × ComplexPlane₂) (x : coverOpen P i) :
    linearLocalSection P l i x = linearPrimitive l (lift P i x) := rfl

/-- The cocycle of a holomorphic complex-linear period character is
the coboundary of its literal local holomorphic primitives. -/
theorem cocycle_linearCoefficients_eq_coboundary (P : HolomorphicPeriodMap V B)
    (l : LinearCoefficients V B) :
    cocycle P (linearCoefficients P l) = HolomorphicPicard.Cech.coboundary
      (PeriodFamilyHigherDirectImage.Zero.totalAdditiveSheaf P) (coverOpen P)
      (linearLocalSection P l) := by
  let := P.totalChartedSpace
  apply HolomorphicPicard.Cech.cocycle_ext
  intro i j
  apply ContMDiffMap.ext
  intro x
  change primitive P (linearCoefficients P l) (lift P i x) -
      primitive P (linearCoefficients P l) (lift P j x) =
    linearPrimitive l (lift P i x) - linearPrimitive l (lift P j x)
  rw [primitive_linearCoefficients_apply, primitive_linearCoefficients_apply]

/-- The actual overlap equation has the exhibited native holomorphic
local sections as a solution. -/
theorem cocycle_linearCoefficients_solvable (P : HolomorphicPeriodMap V B)
    (l : LinearCoefficients V B) : (cocycle P (linearCoefficients P l)).Solvable := by
  refine ⟨linearLocalSection P l, ?_⟩
  intro i j
  exact (congrArg (fun c => c.value i j)
    (cocycle_linearCoefficients_eq_coboundary P l)).symm

/-- Holomorphic complex-linear period characters have zero genuine
native first cohomology class. -/
@[simp] theorem periodClass_linearCoefficients (P : HolomorphicPeriodMap V B)
    (l : LinearCoefficients V B) : periodClass P (linearCoefficients P l) = 0 :=
  HolomorphicPicard.CechExtension.classOf_eq_zero_of_solvable
    (cocycle P (linearCoefficients P l)) (coverOpen_covers P)
    (cocycle_linearCoefficients_solvable P l)

/-- A pointwise original-column condition suffices: no equality to a
replacement cohomology model is assumed. -/
theorem periodClass_eq_zero_of_linear_periods (P : HolomorphicPeriodMap V B)
    (a : Coefficients V B) (l : LinearCoefficients V B)
    (h : ∀ j b, a j b = ∑ k, l k b * (P.periodEquiv b (Pi.single j 1)) k) :
    periodClass P a = 0 := by
  have ha : a = linearCoefficients P l := by
    funext j
    exact ContMDiffMap.ext (h j)
  exact (congrArg (periodClass P) ha).trans (periodClass_linearCoefficients P l)

/-- The genuine coefficient-to-`Ext` linear map kills the actual period
columns of all holomorphic complex-linear forms. -/
theorem periodClassLinearMap_comp_linearCoefficientsLinearMap
    (P : HolomorphicPeriodMap V B) :
    letI := totalCohomologyModule P 1
    (periodClassLinearMap P).comp (linearCoefficientsLinearMap P) = 0 := by
  let := totalCohomologyModule P 1
  apply LinearMap.ext
  intro l
  exact periodClass_linearCoefficients P l

/-- Adding such a holomorphic linear period character does not change
the original native cohomology class. -/
theorem periodClass_add_linearCoefficients (P : HolomorphicPeriodMap V B)
    (a : Coefficients V B) (l : LinearCoefficients V B) :
    periodClass P (a + linearCoefficients P l) = periodClass P a :=
  (periodClass_add P a (linearCoefficients P l)).trans
    ((congrArg (fun x => periodClass P a + x) (periodClass_linearCoefficients P l)).trans
      (add_zero _))

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.Cocycle
