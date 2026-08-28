import Wikipedia.NoExoticSixSphere.RelativeSmallUnionQuotient
import Wikipedia.NoExoticSixSphere.RelativeIntegralChainsFree

/-!
# Degreewise splitting of the actual small-relative integral quotient

The original small-chain comparison identifies the kernel with the span
of simplices contained in either subset. Deleting exactly those basis
generators factors through the native quotient and gives its section.
This is a degreewise splitting, not a chain-map splitting.
-/

noncomputable section

open CategoryTheory
open Wikipedia.HopfProblem FirstHurewicz SingularMayerVietoris

namespace NoExoticSixSphere.SmallRelativeIntegral

variable {X : Type} [TopologicalSpace X] (U V : Set X) (n : ℕ)

abbrev complex := RelativeCoefficients.smallRelativeComplex (ModuleCat.of ℤ ℤ) U V

/-- The original ambient-to-small-relative quotient in a fixed degree. -/
abbrev quotientMap : Chains X n →ₗ[ℤ] (complex U V).X n :=
  ((RelativeCoefficients.smallRelativeProjection (ModuleCat.of ℤ ℤ) U V).f n).hom

theorem quotientMap_surjective : Function.Surjective (quotientMap U V n) := by
  have := (RelativeCoefficients.smallPairSequence_shortExact (ModuleCat.of ℤ ℤ) U V).epi_g
  exact (ModuleCat.epi_iff_surjective _).mp
    (inferInstanceAs (Epi ((RelativeCoefficients.smallPairSequence
      (ModuleCat.of ℤ ℤ) U V).g.f n)))

/-- The actual quotient kernel is exactly the original small-chain submodule. -/
theorem quotientMap_ker : LinearMap.ker (quotientMap U V n) = smallChainSubmodule U V n := by
  have hs := (RelativeCoefficients.smallPairSequence_shortExact
    (ModuleCat.of ℤ ℤ) U V).exact.map
      (HomologicalComplex.eval (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) n)
  let e := ((HomologicalComplex.eval (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) n).mapIso
    (SingularSubcomplex.integralSmallIso U V)).toLinearEquiv
  have he : (smallChainSubmodule U V n).subtype.comp e.toLinearMap =
      (((SimplicialCoefficients.chains (ModuleCat.of ℤ ℤ)).map
        (SingularSubcomplex.smallInclusion U V)).f n).hom :=
    congrArg (fun f => (f.f n).hom) (SingularSubcomplex.integralSmallIso_inclusion U V)
  have hr := LinearMap.range_comp_of_range_eq_top
    (smallChainSubmodule U V n).subtype (LinearEquiv.range e)
  rw [he, Submodule.range_subtype] at hr
  exact hs.moduleCat_range_eq_ker.symm.trans hr

theorem quotientMap_eq_zero_iff (c : Chains X n) :
    quotientMap U V n c = 0 ↔ c ∈ smallChainSubmodule U V n := by
  change c ∈ LinearMap.ker (quotientMap U V n) ↔ _
  rw [quotientMap_ker]

/-- Delete precisely the original simplex generators small for this two-set cover. -/
def removeSmall : Chains X n →ₗ[ℤ] Chains X n := by
  classical
  exact chainLift X n (fun σ => if Set.range σ ⊆ U ∨ Set.range σ ⊆ V
    then 0 else simplexChain X n σ)

open Classical in
theorem removeSmall_simplex (σ : SingularSimplex X n) :
    removeSmall U V n (simplexChain X n σ) =
      if Set.range σ ⊆ U ∨ Set.range σ ⊆ V then 0 else simplexChain X n σ :=
  chainLift_simplex X n _ σ

theorem small_le_ker_removeSmall :
    smallChainSubmodule U V n ≤ LinearMap.ker (removeSmall U V n) := by
  rw [smallChainSubmodule_eq_span]
  apply Submodule.span_le.mpr
  rintro _ ⟨σ, hσ, rfl⟩
  change Set.range σ ⊆ U ∨ Set.range σ ⊆ V at hσ
  change removeSmall U V n (simplexChain X n σ) = 0
  rw [removeSmall_simplex, if_pos hσ]

/-- Deletion preserves the actual quotient, on every original chain. -/
theorem quotientMap_removeSmall :
    (quotientMap U V n).comp (removeSmall U V n) = quotientMap U V n := by
  classical
  apply chainMap_ext X n
  intro σ
  rw [LinearMap.comp_apply, removeSmall_simplex]
  by_cases hσ : Set.range σ ⊆ U ∨ Set.range σ ⊆ V
  · rw [if_pos hσ, map_zero]
    exact ((quotientMap_eq_zero_iff U V n _).mpr
      (simplexChain_mem_small U V n σ hσ)).symm
  · rw [if_neg hσ]

/-- The literal deletion map descends to a section of the original small-relative quotient. -/
def quotientSection : (complex U V).X n →ₗ[ℤ] Chains X n :=
  ConstantSheafSingularComparison.addHomToIntLinearMap
    ((quotientMap U V n).toAddMonoidHom.liftOfSurjective (quotientMap_surjective U V n)
      ⟨(removeSmall U V n).toAddMonoidHom, fun c hc =>
        small_le_ker_removeSmall U V n ((quotientMap_eq_zero_iff U V n c).mp hc)⟩)

theorem quotientSection_quotientMap (c : Chains X n) :
    quotientSection U V n (quotientMap U V n c) = removeSmall U V n c :=
  AddMonoidHom.liftOfRightInverse_comp_apply (quotientMap U V n).toAddMonoidHom
    (Function.surjInv (quotientMap_surjective U V n))
    (Function.rightInverse_surjInv (quotientMap_surjective U V n))
    ⟨(removeSmall U V n).toAddMonoidHom, fun c hc =>
      small_le_ker_removeSmall U V n ((quotientMap_eq_zero_iff U V n c).mp hc)⟩ c

theorem quotientMap_section (c : (complex U V).X n) :
    quotientMap U V n (quotientSection U V n c) = c := by
  obtain ⟨b, rfl⟩ := quotientMap_surjective U V n c
  rw [quotientSection_quotientMap]
  exact LinearMap.congr_fun (quotientMap_removeSmall U V n) b

theorem quotientSection_injective : Function.Injective (quotientSection U V n) :=
  Function.LeftInverse.injective (quotientMap_section U V n)

/-- Every original small-relative integral chain module is free. -/
theorem chains_free : Module.Free ℤ ((complex U V).X n) := by
  let : Module.Free ℤ (Chains X n) := Module.Free.of_basis (chainBasis X n)
  let s := quotientSection U V n
  let : Module ℤ (LinearMap.range s) := (LinearMap.range s).module
  let : Module.Free ℤ (LinearMap.range s) :=
    SingularCohomologyFreeEvaluation.submodule_free_int (LinearMap.range s)
  exact Module.Free.of_equiv (LinearEquiv.ofInjective s (quotientSection_injective U V n)).symm

end NoExoticSixSphere.SmallRelativeIntegral
