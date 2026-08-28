import Wikipedia.HopfProblem.SheafCupProductScalarsNaturality
import Wikipedia.HopfProblem.CuspNormalizationSheafConstantsAdditiveMaps
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyScalarResolutionBasic

/-!
# The actual complex constants in the sheaves used by the construction

Holomorphic and reduced holomorphic functions have their original
constant functions as global coefficients.  The corresponding scalar
endomorphisms agree with the original pointwise scalar endomorphisms,
before passing to cohomology.  The genuine constant sheaf uses the
sheafification unit, and its original maps into the two function sheaves
preserve these coefficients.
-/

noncomputable section

open CategoryTheory TopologicalSpace Opposite
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SheafCupProduct

open GodementRing CuspNormalization

section Constant

/-- Literal constant representatives in the actual sheafified constant sheaf. -/
def constantCoefficients (X : TopCat.{0}) : Scalars.Coefficients (SheafConstants.complexSheaf X) :=
  ((SheafConstants.unit X).app (op ⊤)).hom

theorem restricted_constantCoefficients (X : TopCat.{0}) (U : (Opens X)ᵒᵖ) (z : ℂ) :
    Scalars.restricted (constantCoefficients X) U z = (SheafConstants.unit X).app U z := by
  exact (ConcreteCategory.congr_hom
    ((SheafConstants.unit X).naturality
      (homOfLE (show U.unop ≤ ⊤ from le_top)).op) z).symm

/-- The scalar action on the actual constant additive sheaf is multiplication
by its actual constant sections. -/
def constantScalarEnd (X : TopCat.{0}) :
    ℂ →+* End (SheafConstants.complexAdditiveSheaf X) :=
  Scalars.scalarEnd (constantCoefficients X)

theorem constantScalarEnd_apply (X : TopCat.{0}) (z : ℂ)
    (U : (Opens X)ᵒᵖ) (s : (SheafConstants.complexSheaf X).obj.obj U) :
    (constantScalarEnd X z).hom.app U s = (SheafConstants.unit X).app U z * s := by
  change Scalars.restricted (constantCoefficients X) U z * s = _
  rw [restricted_constantCoefficients]

end Constant

section Holomorphic

variable {E B : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace B] (I : ModelWithCorners ℂ E B)
  (M : Type) [TopologicalSpace M] [ChartedSpace B M]

/-- The original constant holomorphic functions on the entire manifold. -/
def holomorphicCoefficients : Scalars.Coefficients (HolomorphicFunctionSheaf.sheaf I M) :=
  algebraMap ℂ ((HolomorphicFunctionSheaf.sheaf I M).presheaf.obj (op ⊤))

theorem restricted_holomorphicCoefficients (U : (Opens (TopCat.of M))ᵒᵖ) (z : ℂ) :
    Scalars.restricted (holomorphicCoefficients I M) U z =
      algebraMap ℂ ((HolomorphicFunctionSheaf.sheaf I M).presheaf.obj U) z := rfl

/-- The coefficient construction recovers the original scalar sheaf map. -/
theorem scalarEnd_holomorphicCoefficients :
    Scalars.scalarEnd (holomorphicCoefficients I M) =
      SheafCohomology.holomorphicScalarEnd I M := by
  apply RingHom.ext
  intro z
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro s
  apply ContMDiffMap.ext
  intro x
  rfl

/-- The original constant-to-holomorphic map preserves the actual coefficients. -/
theorem holomorphicMap_coefficients :
    Scalars.pushCoefficients (SheafConstants.holomorphicMap I M)
        (constantCoefficients (TopCat.of M)) = holomorphicCoefficients I M := by
  apply RingHom.ext
  intro z
  apply ContMDiffMap.ext
  intro x
  exact SheafConstants.holomorphicMap_unit I M ⊤ z x

end Holomorphic

section Reduced

variable {E B : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace B] {M : Type} [TopologicalSpace M] [ChartedSpace B M]
  (I : ModelWithCorners ℂ E B) (S : Set M)

/-- The original constant functions in the independently defined reduced sheaf. -/
def reducedCoefficients : Scalars.Coefficients (SheafReduced.sheaf I S) :=
  SheafReduced.constant I S ⊤

theorem restricted_reducedCoefficients (U : (Opens (TopCat.of S))ᵒᵖ) (z : ℂ) :
    Scalars.restricted (reducedCoefficients I S) U z =
      SheafReduced.constant I S U.unop z := rfl

/-- Multiplication by these coefficients is the original reduced scalar action. -/
theorem scalarEnd_reducedCoefficients :
    Scalars.scalarEnd (reducedCoefficients I S) =
      SheafCohomologyScalarResolution.reducedScalarEnd I S := by
  apply RingHom.ext
  intro z
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro s
  apply SheafReduced.Section.ext
  intro x
  rfl

/-- The actual constant-to-reduced map preserves literal complex constants. -/
theorem reducedMap_coefficients :
    Scalars.pushCoefficients (SheafConstants.reducedMap I S)
        (constantCoefficients (TopCat.of S)) = reducedCoefficients I S := by
  apply RingHom.ext
  intro z
  apply SheafReduced.Section.ext
  intro x
  exact SheafConstants.reducedMap_unit I S ⊤ z x

end Reduced

end Wikipedia.HopfProblem.SheafCupProduct
