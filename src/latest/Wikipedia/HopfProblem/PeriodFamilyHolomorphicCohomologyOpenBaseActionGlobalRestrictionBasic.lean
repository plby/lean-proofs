import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenBaseActionActions

/-!
# Literal restriction of global base multipliers to original neighborhood coefficients

Restricting a global holomorphic base function means evaluating the same
function on the original base-open subtype. Its global multiplier on
the actual total sheaf and its local multiplier on the original full
preimage commute with the genuine holomorphic open-restriction sheaf
isomorphism. The coefficient square is proved on the original sections.
-/

noncomputable section

open CategoryTheory TopologicalSpace Opposite
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenBaseAction.GlobalRestriction

open PeriodFamilyHigherDirectImage HolomorphicSheafCohomology

variable {V : Type*} {B : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B]

local notation "IB" => modelWithCornersSelf ℂ V
local notation "IT" => modelWithCornersSelf ℂ (V × ComplexPlane₂)

/-- Literal restriction of an actual global base function to the original base open. -/
def restrictBaseFunction (P : HolomorphicPeriodMap V B) (U : Opens B) :
    BaseFunctionAction.BaseFunction V B →ₐ[ℂ] Zero.BaseSection P U where
  toFun g := ⟨fun x => g x, g.contMDiff.comp contMDiff_subtype_val⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp] theorem restrictBaseFunction_apply (P : HolomorphicPeriodMap V B) (U : Opens B)
    (g : BaseFunctionAction.BaseFunction V B) (b : U) :
    restrictBaseFunction P U g b = g b := rfl

/-- This is exactly the original sheaf restriction after adding the global-open wrapper. -/
theorem restrictBaseFunction_eq_baseRestriction (P : HolomorphicPeriodMap V B)
    (U : Opens B) (g : BaseFunctionAction.BaseFunction V B) :
    restrictBaseFunction P U g =
      Zero.baseRestriction P (show U ≤ ⊤ from le_top)
        (HolomorphicFunctionSheaf.mapToGlobalSection IB B g) := rfl

variable [IsManifold (modelWithCornersSelf ℂ V) ω B]

/-- The actual ambient global multiplier and the literal restricted
base multiplier commute with the original holomorphic coefficient isomorphism. -/
@[reassoc] theorem sheafIso_baseMultiply (P : HolomorphicPeriodMap V B) (U : Opens B)
    (g : BaseFunctionAction.BaseFunction V B) :
    letI := P.totalChartedSpace
    (OpenRestriction.restriction (X := TopCat.of P.TotalSpace) (Zero.basePreimage P U)).map
        (BaseFunctionAction.baseMultiplyEnd P g) ≫
      (HolomorphicRestriction.sheafIso IT (Zero.basePreimage P U)).hom =
    (HolomorphicRestriction.sheafIso IT (Zero.basePreimage P U)).hom ≫
      preimageMultiplyEnd P U (restrictBaseFunction P U g) := by
  let := P.totalChartedSpace
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext W
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro s
  apply ContMDiffMap.ext
  intro x
  rfl

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenBaseAction.GlobalRestriction
