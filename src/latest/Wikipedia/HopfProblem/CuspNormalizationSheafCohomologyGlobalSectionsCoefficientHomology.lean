import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyGlobalSectionsCoefficientExact
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyResolutionHomology

/-!
# The actual categorical homology of the coefficient complex

These are isomorphisms of Mathlib's kernels, homology objects, and
cokernels. The class formulas retain the two curve-cycle coordinates
and the P-minus-Q quotient coordinate.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyGlobalSections

open SheafCohomologyResolution

/-- The kernel of the first, zero arrow is the actual first coefficient space. -/
def coefficientKernelIso : kernel coefficientComplex.f ≅ ModuleCat.of ℂ ℂ :=
  kernelZeroIsoSource

/-- A zero arrow followed by the identity is exact. -/
theorem coefficientCycleQuotient_exact :
    (ShortComplex.mk (0 : ModuleCat.of ℂ ℂ ⟶ ModuleCat.of ℂ (Fin 2 → ℂ))
      (𝟙 _) (by simp only [zero_comp])).Exact :=
  (ShortComplex.exact_iff_mono _ rfl).mpr inferInstance

/-- The explicit two-parameter cycles give actual left homology data. -/
def coefficientHomologyData : coefficientComplex.LeftHomologyData := by
  letI := coefficientCycles_mono
  exact leftHomologyDataOfExact coefficientComplex
    (K := ModuleCat.of ℂ (Fin 2 → ℂ)) (H := ModuleCat.of ℂ (Fin 2 → ℂ))
    (ModuleCat.ofHom coefficientCycles) 0 (𝟙 _)
    coefficientKernelComplex.zero (by simp only [zero_comp]) (by simp only [zero_comp])
    coefficientKernelComplex_exact coefficientCycleQuotient_exact

/-- Actual homology is complex-linearly the space of the first and third curve values. -/
def coefficientHomologyIso : coefficientComplex.homology ≅ ModuleCat.of ℂ (Fin 2 → ℂ) :=
  coefficientHomologyData.homologyIso

/-- The homology class of the cycle `(u, u+v, v)` has coordinates `(u,v)`. -/
theorem coefficientHomologyIso_class :
    coefficientHomologyData.cyclesIso.inv ≫ coefficientComplex.homologyπ ≫
      coefficientHomologyIso.hom = 𝟙 _ := by
  have := coefficientCycles_mono
  exact leftHomologyDataOfExact_class coefficientComplex
    (K := ModuleCat.of ℂ (Fin 2 → ℂ)) (H := ModuleCat.of ℂ (Fin 2 → ℂ))
    (ModuleCat.ofHom coefficientCycles) 0 (𝟙 _)
    coefficientKernelComplex.zero (by simp only [zero_comp]) (by simp only [zero_comp])
    coefficientKernelComplex_exact coefficientCycleQuotient_exact

/-- The actual cokernel is measured by the difference between the P and Q coordinates. -/
def coefficientCokernelIso : cokernel coefficientComplex.g ≅ ModuleCat.of ℂ ℂ := by
  letI : Epi coefficientCokernelComplex.g := coefficientDifference_epi
  exact IsColimit.coconePointUniqueUpToIso
    (cokernelIsCokernel coefficientComplex.g) coefficientCokernelComplex_exact.gIsCokernel

/-- The quotient map is literally the P-minus-Q coordinate. -/
theorem coefficientCokernelIso_class :
    cokernel.π coefficientComplex.g ≫ coefficientCokernelIso.hom =
      ModuleCat.ofHom coefficientDifference := by
  have : Epi coefficientCokernelComplex.g := coefficientDifference_epi
  exact IsColimit.comp_coconePointUniqueUpToIso_hom
    (cokernelIsCokernel coefficientComplex.g)
    coefficientCokernelComplex_exact.gIsCokernel WalkingParallelPair.one

theorem coefficientKernel_finrank : Module.finrank ℂ ↥(kernel coefficientComplex.f) = 1 :=
  coefficientKernelIso.toLinearEquiv.finrank_eq.trans (Module.finrank_self ℂ)

theorem coefficientHomology_finrank : Module.finrank ℂ coefficientComplex.homology = 2 :=
  coefficientHomologyIso.toLinearEquiv.finrank_eq.trans (Module.finrank_fin_fun ℂ)

theorem coefficientCokernel_finrank : Module.finrank ℂ ↥(cokernel coefficientComplex.g) = 1 :=
  coefficientCokernelIso.toLinearEquiv.finrank_eq.trans (Module.finrank_self ℂ)

end Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyGlobalSections
