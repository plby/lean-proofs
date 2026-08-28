import Wikipedia.NoExoticSixSphere.RelativeSingularHomology
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonCochainBasic

/-!
# Degreewise splitting of the actual relative integral chains

Delete simplex generators supported in the subspace. This actual ambient
chain map in a fixed degree annihilates the relative quotient kernel and
preserves its quotient. Its factorization is therefore a genuine section
of that quotient. No compatibility with the differential is asserted.
-/

noncomputable section

open Wikipedia.HopfProblem FirstHurewicz SingularMayerVietoris

namespace NoExoticSixSphere.RelativeSingularHomology

variable {X : Type} [TopologicalSpace X] (U : Set X) (n : ℕ)

/-- Delete precisely the simplex generators wholly contained in the subspace. -/
def removeSupported : Chains X n →ₗ[ℤ] Chains X n := by
  classical
  exact chainLift X n (fun σ => if Set.range σ ⊆ U then 0 else simplexChain X n σ)

open Classical in
theorem removeSupported_simplex (σ : SingularSimplex X n) :
    removeSupported U n (simplexChain X n σ) =
      if Set.range σ ⊆ U then 0 else simplexChain X n σ := by
  classical
  exact chainLift_simplex X n _ σ

theorem supported_le_ker_removeSupported :
    supportedChainSubmodule U n ≤ LinearMap.ker (removeSupported U n) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨σ, hσ, rfl⟩
  change Set.range σ ⊆ U at hσ
  change removeSupported U n (simplexChain X n σ) = 0
  rw [removeSupported_simplex, if_pos hσ]

/-- Deleting supported generators leaves the original relative quotient unchanged. -/
theorem quotientMap_removeSupported :
    (quotientMap U n).comp (removeSupported U n) = quotientMap U n := by
  classical
  apply chainMap_ext X n
  intro σ
  rw [LinearMap.comp_apply, removeSupported_simplex]
  by_cases hσ : Set.range σ ⊆ U
  · rw [if_pos hσ, map_zero]
    exact ((quotientMap_eq_zero_iff U n _).mpr (simplexChain_mem_supported U n σ hσ)).symm
  · rw [if_neg hσ]

/-- Factor deletion through the actual relative quotient to obtain its section. -/
def quotientSection : (complex U).X n →ₗ[ℤ] Chains X n :=
  ConstantSheafSingularComparison.addHomToIntLinearMap
    ((quotientMap U n).toAddMonoidHom.liftOfSurjective (quotientMap_surjective U n)
      ⟨(removeSupported U n).toAddMonoidHom, fun c hc =>
        supported_le_ker_removeSupported U n ((quotientMap_eq_zero_iff U n c).mp hc)⟩)

theorem quotientSection_quotientMap (c : Chains X n) :
    quotientSection U n (quotientMap U n c) = removeSupported U n c :=
  AddMonoidHom.liftOfRightInverse_comp_apply (quotientMap U n).toAddMonoidHom
    (Function.surjInv (quotientMap_surjective U n))
    (Function.rightInverse_surjInv (quotientMap_surjective U n))
    ⟨(removeSupported U n).toAddMonoidHom, fun c hc =>
      supported_le_ker_removeSupported U n ((quotientMap_eq_zero_iff U n c).mp hc)⟩ c

/-- This is a section of the original relative chain projection, not an abstract splitting. -/
theorem quotientMap_section (c : (complex U).X n) :
    quotientMap U n (quotientSection U n c) = c := by
  obtain ⟨b, rfl⟩ := quotientMap_surjective U n c
  rw [quotientSection_quotientMap]
  exact LinearMap.congr_fun (quotientMap_removeSupported U n) b

theorem quotientSection_injective : Function.Injective (quotientSection U n) :=
  Function.LeftInverse.injective (quotientMap_section U n)

end NoExoticSixSphere.RelativeSingularHomology
