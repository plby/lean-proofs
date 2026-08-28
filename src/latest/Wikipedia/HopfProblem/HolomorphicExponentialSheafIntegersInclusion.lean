import Wikipedia.HopfProblem.HolomorphicExponentialSheafIntegersLocal
import Wikipedia.HopfProblem.HolomorphicFunctionSheafCohomologyZeroBasic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The integer inclusion into the holomorphic function sheaf

For the ordinary complex exponential, the integer inclusion sends `n` to
the actual holomorphic constant `n * (2 * π * I)`. The map is extended
from the constant presheaf by the genuine sheafification adjunction.
Its injectivity is proved using actual local integer representatives;
no connectedness or local-constancy hypothesis is imposed on the space.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicExponentialSheaf

/-- The additive integer period map for the ordinary complex exponential. -/
def integerScalarHom : ℤ →+ ℂ where
  toFun n := (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)
  map_zero' := by simp
  map_add' m n := by simp only [Int.cast_add, add_mul]

@[simp] theorem integerScalarHom_apply (n : ℤ) :
    integerScalarHom n = (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := rfl

theorem integerScalarHom_injective : Function.Injective integerScalarHom := by
  have hperiod : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  intro m n h
  exact Int.cast_injective (mul_right_cancel₀ hperiod h)

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  (M : Type) [TopologicalSpace M] [ChartedSpace H M]

/-- Literal integer periods as holomorphic constant sections, before
applying the actual sheafification universal property. -/
def integerPresheafInclusion :
    integerPresheaf (TopCat.of M) ⟶ (HolomorphicFunctionSheaf.additiveSheaf I M).obj where
  app U := AddCommGrpCat.ofHom <|
    ((algebraMap ℂ (HolomorphicFunctionSheaf.Section I M U.unop)).toAddMonoidHom).comp
      integerScalarHom
  naturality _ _ _ := by ext n; rfl

/-- The native sheaf map from the actual constant integer sheaf to
the actual additive holomorphic function sheaf. -/
def integerInclusion :
    integerSheaf (TopCat.of M) ⟶ HolomorphicFunctionSheaf.additiveSheaf I M :=
  integerLift (HolomorphicFunctionSheaf.additiveSheaf I M) (integerPresheafInclusion I M)

/-- On a genuine sheafification-unit representative, the inclusion is
the holomorphic constant with the ordinary-exponential period. -/
@[simp] theorem integerInclusion_app_unit (U : Opens M) (n : ℤ) :
    (integerInclusion I M).hom.app (op U)
        ((integerUnit (TopCat.of M)).app (op U) n) =
      algebraMap ℂ (HolomorphicFunctionSheaf.Section I M U)
        ((n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) :=
  integerLift_app_unit (HolomorphicFunctionSheaf.additiveSheaf I M)
    (integerPresheafInclusion I M) U n

@[simp] theorem integerInclusion_app_unit_apply (U : Opens M) (n : ℤ) (x : U) :
    (fun f : HolomorphicFunctionSheaf.Section I M U => f x)
        ((integerInclusion I M).hom.app (op U)
          ((integerUnit (TopCat.of M)).app (op U) n)) =
      (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
  rw [integerInclusion_app_unit]
  rfl

/-- Every actual integer section maps locally to an actual holomorphic
constant integer period. -/
theorem integerInclusion_locally_constant (U : Opens M)
    (s : (integerSheaf (TopCat.of M)).obj.obj (op U)) (x : M) (hx : x ∈ U) :
    ∃ (V : Opens M) (hVU : V ≤ U) (n : ℤ), x ∈ V ∧
      (HolomorphicFunctionSheaf.additiveSheaf I M).obj.map (homOfLE hVU).op
          ((integerInclusion I M).hom.app (op U) s) =
        algebraMap ℂ (HolomorphicFunctionSheaf.Section I M V)
          ((n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) :=
  integerLift_locally_constant (HolomorphicFunctionSheaf.additiveSheaf I M)
    (integerPresheafInclusion I M) U s x hx

/-- Injectivity holds on all actual sections, also on disconnected
or empty open sets. -/
theorem integerInclusion_app_injective (U : Opens M) :
    Function.Injective ((integerInclusion I M).hom.app (op U)) := by
  apply integerLift_app_injective_of_constants
  intro V x m n hmn
  apply integerScalarHom_injective
  exact congrArg (fun f : HolomorphicFunctionSheaf.Section I M V => f x) hmn

/-- The ordinary-exponential integer inclusion is a monomorphism of
the actual sheaves of abelian groups. -/
instance integerInclusion_mono : Mono (integerInclusion I M) :=
  CategoryTheory.Sheaf.mono_of_injective _ fun U =>
    integerInclusion_app_injective I M U.unop

end Wikipedia.HopfProblem.HolomorphicExponentialSheaf
