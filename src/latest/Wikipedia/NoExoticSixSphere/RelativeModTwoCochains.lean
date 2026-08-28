import Wikipedia.NoExoticSixSphere.ModTwoDualComplex
import Wikipedia.NoExoticSixSphere.ModTwoCochainPullback
import Wikipedia.NoExoticSixSphere.RelativeCoefficientCycleRepresentatives

/-!
# Actual relative mod-two cochains

Relative cochains are additive homomorphisms from the original relative
integral singular chains. Precomposition with the quotient projection
gives absolute cochains that vanish on the actual subspace chains.
-/

noncomputable section

open CategoryTheory Limits
open Wikipedia.HopfProblem FirstHurewicz SingularMayerVietoris

namespace NoExoticSixSphere.RelativeModTwoCochains

variable {X : Type} [TopologicalSpace X] (U : Set X)

/-- Cochains on the actual integral relative quotient. -/
abbrev Cochain (n : ℕ) := (RelativeCoefficients.complex (ModuleCat.of ℤ ℤ) U).X n →+ ZMod 2

/-- The original relative additive dual with integer scalars. -/
abbrev complex := ModTwoDualComplex.complex (RelativeCoefficients.complex (ModuleCat.of ℤ ℤ) U)

/-- Precomposition by the original quotient projection. -/
def toAbsoluteMap : complex U ⟶ ModTwoCapProduct.cochainComplex X :=
  ModTwoDualComplex.map (RelativeCoefficients.projection (ModuleCat.of ℤ ℤ) U)

abbrev toAbsolute (p : ℕ) : Cochain U p →ₗ[ℤ] ModTwoCapProduct.Cochain X p :=
  ((toAbsoluteMap U).f p).hom

theorem toAbsolute_apply (p : ℕ) (α : Cochain U p) (c : Chains X p) :
    toAbsolute U p α c = α (RelativeCoefficients.quotientMap (ModuleCat.of ℤ ℤ) U p c) := rfl

/-- The original quotient surjectivity makes precomposition injective. -/
theorem toAbsolute_injective (p : ℕ) : Function.Injective (toAbsolute U p) := by
  intro α β he
  apply AddMonoidHom.ext
  intro c
  obtain ⟨d, rfl⟩ := RelativeCoefficients.quotientMap_surjective (ModuleCat.of ℤ ℤ) U p c
  exact congrArg (fun γ : ModTwoCapProduct.Cochain X p => γ d) he

/-- Relative cochains restrict to zero on the original subspace complex. -/
theorem pullback_toAbsolute (p : ℕ) (α : Cochain U p) :
    ModTwoCapProduct.pullback (subtypeInclusion U) p (toAbsolute U p α) = 0 := by
  apply AddMonoidHom.ext
  intro c
  change α (RelativeCoefficients.quotientMap (ModuleCat.of ℤ ℤ) U p
    (((RelativeCoefficients.inclusion (ModuleCat.of ℤ ℤ) U).f p).hom c)) = 0
  have he := congrArg (fun f => (f.f p).hom c)
    (cokernel.condition (RelativeCoefficients.inclusion (ModuleCat.of ℤ ℤ) U))
  exact (congrArg α he).trans α.map_zero

/-- The actual relative coboundary. -/
def coboundary {p : ℕ} (α : Cochain U p) : Cochain U (p + 1) :=
  ((complex U).d p (p + 1)).hom α

theorem toAbsolute_coboundary (p : ℕ) (α : Cochain U p) :
    toAbsolute U (p + 1) (coboundary U α) = ModTwoCapProduct.coboundary (toAbsolute U p α) :=
  (congrArg (fun f => f.hom α) ((toAbsoluteMap U).comm p (p + 1))).symm

theorem coboundary_squared (p : ℕ) (α : Cochain U p) :
    coboundary U (coboundary U α) = 0 :=
  congrArg (fun f : (complex U).X p ⟶ (complex U).X (p + 2) => f.hom α)
    ((complex U).d_comp_d p (p + 1) (p + 2))

end NoExoticSixSphere.RelativeModTwoCochains
