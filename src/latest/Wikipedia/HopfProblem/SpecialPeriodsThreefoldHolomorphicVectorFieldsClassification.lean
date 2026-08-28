import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicVectorFieldsClassificationCharacters
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicVectorFieldsClassificationDetection
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicVectorFieldsClassificationElliptic
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicVectorFieldsClassificationCuspRegular
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# The space of global holomorphic vector fields has dimension one

The genuine regular vertical coefficients extend holomorphically across
the actual elliptic roots and have actual analytic cusp germs. Their first
component has the homogeneous special-period character and hence vanishes
by the constructed generator's exact divisor and cusp pole. The second
component is then invariant and constant. Native tangent pullback and
density identify the original field with a unique constant multiple of
the actual flow generator.

The resulting linear equivalence concerns all analytic sections of the
original tangent bundle, not a selected space of invariant coefficients.
No direct-image local-freeness or automorphism Lie-group theorem is used.
-/

noncomputable section

open UpperHalfPlane
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicVectorFields.Classification

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold
  HolomorphicForms.RegularCover.coverChartedSpace HolomorphicForms.RegularCover.cover_isManifold

theorem verticalExtension_cuspRegular (v : Threefold.HolomorphicVectorFields.Field)
    (i : Fin 2) : MuTorsor.CuspRegular (fun z => verticalExtension v z i) :=
  regularVertical_cuspRegular v (verticalExtension v) (verticalExtension_restrict v) i

/-- The actual homogeneous μ divisor has elliptic orders two and one
and a simple cusp pole; division and compact vanishing kill this component. -/
theorem verticalExtension_first_eq_zero (v : Threefold.HolomorphicVectorFields.Field) :
    (fun z : ℍ => verticalExtension v z 0) = 0 :=
  homogeneous_eq_zero_of_generator_laws
    ((ContinuousLinearMap.proj 0 : ComplexPlane₂ →L[ℂ] ℂ).contMDiff.comp
      (verticalExtension_holomorphic v))
    (first_covariant_generator₁ (verticalExtension_group v))
    (first_covariant_generator₂ (verticalExtension_group v))
    (verticalExtension_cuspRegular v 0)

/-- With the first component zero, the actual second-column identity
makes the remaining coefficient invariant and therefore constant. -/
theorem verticalExtension_second_const (v : Threefold.HolomorphicVectorFields.Field) :
    ∃ c : ℂ, ∀ z : ℍ, verticalExtension v z 1 = c :=
  invariant_eq_const_of_cuspRegular
    ((ContinuousLinearMap.proj 1 : ComplexPlane₂ →L[ℂ] ℂ).contMDiff.comp
      (verticalExtension_holomorphic v))
    (second_invariant_of_first_zero (verticalExtension_group v)
      (congrFun (verticalExtension_first_eq_zero v)))
    (verticalExtension_cuspRegular v 1)

/-- The original regular coefficients are exactly one constant e₂ direction. -/
theorem regularVertical_eq_constant_e₂ (v : Threefold.HolomorphicVectorFields.Field) :
    ∃ c : ℂ, ∀ z : TriangleRegularPoint, regularVertical v z = (![0, c] : ComplexPlane₂) := by
  obtain ⟨c, hc⟩ := verticalExtension_second_const v
  refine ⟨c, fun z => ?_⟩
  rw [← verticalExtension_restrict v z]
  funext i
  fin_cases i
  · exact congrFun (verticalExtension_first_eq_zero v) z.val
  · exact hc z.val

/-- Every genuine global holomorphic tangent field is a scalar multiple
of the actual globally constructed vertical flow generator. -/
theorem exists_eq_smul_generator (v : Threefold.HolomorphicVectorFields.Field) :
    ∃ c : ℂ, v = c • VerticalAction.generator := by
  obtain ⟨c, hc⟩ := regularVertical_eq_constant_e₂ v
  exact ⟨c, field_eq_smul_generator_of_regularVertical v c hc⟩

theorem existsUnique_eq_smul_generator (v : Threefold.HolomorphicVectorFields.Field) :
    ∃! c : ℂ, v = c • VerticalAction.generator := by
  obtain ⟨c, hc⟩ := exists_eq_smul_generator v
  exact ⟨c, hc, fun d hd => smul_generator_injective (hd.symm.trans hc)⟩

/-- Multiplication by the original native generator as a genuine linear map. -/
def generatorLinearMap : ℂ →ₗ[ℂ] Threefold.HolomorphicVectorFields.Field where
  toFun c := c • VerticalAction.generator
  map_add' c d := add_smul c d VerticalAction.generator
  map_smul' c d := (smul_smul c d VerticalAction.generator).symm

/-- The full space of native global holomorphic fields is a complex line. -/
def generatorLinearEquiv : ℂ ≃ₗ[ℂ] Threefold.HolomorphicVectorFields.Field :=
  LinearEquiv.ofBijective generatorLinearMap
    ⟨smul_generator_injective, fun v => by
      obtain ⟨c, hc⟩ := exists_eq_smul_generator v
      exact ⟨c, hc.symm⟩⟩

@[simp] theorem generatorLinearEquiv_apply (c : ℂ) :
    generatorLinearEquiv c = c • VerticalAction.generator := rfl

/-- The inverse scalar is the actual second fibre coefficient at any
point of the original regular vector cover. -/
theorem generatorLinearEquiv_symm_apply (v : Threefold.HolomorphicVectorFields.Field)
    (x : HolomorphicForms.RegularCover.Cover) :
    generatorLinearEquiv.symm v = (regularCoefficients v x).2 1 := by
  have h := congrArg
    (fun w : Threefold.HolomorphicVectorFields.Field => (regularCoefficients w x).2 1)
    (generatorLinearEquiv.apply_symm_apply v)
  simpa only [generatorLinearEquiv_apply, regularCoefficients_smul,
    regularCoefficients_generator, Prod.smul_snd, Pi.smul_apply, smul_eq_mul,
    Matrix.cons_val_one, Matrix.cons_val_zero, mul_one] using h

/-- Proposition 9.23's h⁰(TX)=1 for the original native tangent bundle. -/
theorem finrank_field_eq_one :
    Module.finrank ℂ Threefold.HolomorphicVectorFields.Field = 1 := by
  rw [← generatorLinearEquiv.finrank_eq]
  exact Module.finrank_self ℂ

theorem field_finiteDimensional :
    FiniteDimensional ℂ Threefold.HolomorphicVectorFields.Field :=
  FiniteDimensional.of_finrank_eq_succ (n := 0) finrank_field_eq_one

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicVectorFields.Classification
