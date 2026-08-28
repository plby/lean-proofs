import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyCocycleSections
import Wikipedia.HopfProblem.HolomorphicPicardCechSheafMap

/-!
# Actual additive Čech cocycles of holomorphic period characters

The values are the proved genuine holomorphic overlap sections in the
original total-space atlas. Their triple-overlap identity is literal
telescoping. Coefficient addition is pointwise addition of the actual
cocycles, and coefficient scalars act through the original scalar sheaf
endomorphism. No cohomology comparison is used in this construction.
-/

noncomputable section

open CategoryTheory TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.Cocycle

open HolomorphicFunctionSheaf.SphereH1

variable {V : Type*} {B : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B]
  [IsManifold (modelWithCornersSelf ℂ V) ω B]

/-- The genuine additive cocycle of the actual period primitive, with
the fixed orientation `c_ij = L(lift_i) - L(lift_j)`. -/
def cocycle (P : HolomorphicPeriodMap V B) (a : Coefficients V B) :
    CechOneCocycle (PeriodFamilyHigherDirectImage.Zero.totalAdditiveSheaf P) (coverOpen P) := by
  letI := P.totalChartedSpace
  refine { value := overlapSection P a, condition := ?_ }
  intro i j k
  apply ContMDiffMap.ext
  intro x
  change difference P a i j x + difference P a j k x = difference P a i k x
  simp only [difference]
  abel

@[simp] theorem cocycle_value (P : HolomorphicPeriodMap V B) (a : Coefficients V B)
    (i j : B × ComplexPlane₂) : (cocycle P a).value i j = overlapSection P a i j := rfl

@[simp] theorem cocycle_value_apply (P : HolomorphicPeriodMap V B) (a : Coefficients V B)
    (i j : B × ComplexPlane₂) (x : ↥(coverOpen P i ⊓ coverOpen P j)) :
    Subtype.val
      ((cocycle P a).value i j : NativeSection P (coverOpen P i ⊓ coverOpen P j)) x =
      primitive P a (lift P i x) - primitive P a (lift P j x) := rfl

@[simp] theorem cocycle_zero (P : HolomorphicPeriodMap V B) :
    cocycle P (0 : Coefficients V B) = 0 := by
  let := P.totalChartedSpace
  apply HolomorphicPicard.Cech.cocycle_ext
  intro i j
  apply ContMDiffMap.ext
  intro x
  exact difference_zero P i j x

/-- Addition of original coefficients gives addition of actual holomorphic cocycles. -/
theorem cocycle_add (P : HolomorphicPeriodMap V B) (a a' : Coefficients V B) :
    cocycle P (a + a') = cocycle P a + cocycle P a' := by
  let := P.totalChartedSpace
  apply HolomorphicPicard.Cech.cocycle_ext
  intro i j
  apply ContMDiffMap.ext
  intro x
  exact difference_add P a a' i j x

/-- The construction is an actual additive map into the literal-section cocycles. -/
def cocycleHom (P : HolomorphicPeriodMap V B) :
    Coefficients V B →+
      CechOneCocycle (PeriodFamilyHigherDirectImage.Zero.totalAdditiveSheaf P) (coverOpen P) where
  toFun := cocycle P
  map_zero' := cocycle_zero P
  map_add' := cocycle_add P

/-- Coefficient complex multiplication is induced by the original scalar map
of the actual native total-space holomorphic sheaf. -/
theorem cocycle_smul_map (P : HolomorphicPeriodMap V B) (c : ℂ) (a : Coefficients V B) :
    cocycle P (c • a) = HolomorphicPicard.Cech.mapCocycle
      (PeriodFamilyHigherDirectImage.Zero.totalScalarEnd P c) (cocycle P a) := by
  let := P.totalChartedSpace
  apply HolomorphicPicard.Cech.cocycle_ext
  intro i j
  apply ContMDiffMap.ext
  intro x
  exact difference_smul P c a i j x

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.Cocycle
