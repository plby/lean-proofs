import Wikipedia.NoExoticSixSphere.RelativeSimplexCycles

/-!
# Relative simplex classes are invariant under homotopies of pairs

The homotopy need only keep the boundary in the subspace. Its actual
singular prism gives the relative boundary between the two original
simplex cycles, with the side prisms supported in the subspace.
-/

noncomputable section

open scoped unitInterval
open Wikipedia.HopfProblem FirstHurewicz SingularMayerVietoris
open SecondHurewicz.SimplyConnected

namespace NoExoticSixSphere.RelativeSimplexCycles

open RelativeSingularHomology

variable {X : Type} [TopologicalSpace X] (U : Set X)

theorem homologyClass_eq_of_homotopy (n : ℕ) (smp₀ smp₁ : RelativeSimplex U (n + 1))
    (H : smp₀.val.Homotopy smp₁.val)
    (hU : ∀ t s, s ∈ simplexBoundary (n + 1) → H (t, s) ∈ U) :
    homologyClass U n smp₁ = homologyClass U n smp₀ := by
  apply (ModuleHomology.cycleClass_eq_iff (complex U) (n + 1) _ _).mpr
  refine ⟨quotientMap U (n + 2) (simplexPrism (n + 1) H.toContinuousMap), ?_⟩
  have hz : quotientMap U (n + 1)
      (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        simplexPrism n (H.toContinuousMap.comp
          ((ContinuousMap.id I).prodMap (simplexFace n i)))) = 0 := by
    apply (quotientMap_eq_zero_iff U (n + 1) _).mpr
    apply Submodule.sum_mem
    intro i _
    apply (supportedChainSubmodule U (n + 1)).toAddSubgroup.zsmul_mem
    apply SimplexHomotopyChainSupport.simplexPrism_mem
    intro p
    exact hU p.1 (simplexFace n i p.2) (simplexFace_mem_boundary n i p.2)
  have h₀ : timeSlice H.toContinuousMap 0 = smp₀.val := by
    ext s
    exact H.apply_zero s
  have h₁ : timeSlice H.toContinuousMap 1 = smp₁.val := by
    ext s
    exact H.apply_one s
  change ((complex U).d (n + 2) (n + 1)).hom _ =
    quotientMap U (n + 1) (simplexChain X (n + 1) smp₁.val) -
      quotientMap U (n + 1) (simplexChain X (n + 1) smp₀.val)
  rw [boundary_quotientMap, simplexPrism_boundary, map_sub, map_sub, hz,
    sub_zero, h₁, h₀]

end NoExoticSixSphere.RelativeSimplexCycles
