import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyGlobalSectionsLinearComplex
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyGlobalSectionsCoefficientHomology

/-!
# Kernel, homology, and cokernel of the actual global normalization complex

Every object here is computed from the global sections of the actual
normalization sheaf resolution. These statements concern that global
complex; identifying it with higher sheaf cohomology additionally requires
the separately proved analytic acyclicity of the resolution terms.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyGlobalSections

open SheafResolution SheafCohomologyResolution CuspQuotient ToricCharts ToricSpace

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
  (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε)

/-- The actual first global kernel is complex-linearly one dimensional. -/
def globalKernelIso : kernel (globalLinearComplex C ε hε hε1 hC hR).f ≅ ModuleCat.of ℂ ℂ :=
  kernel.mapIso (globalLinearComplex C ε hε hε1 hC hR).f coefficientComplex.f
    (normalizationGlobalLinearEquiv C ε hε).toModuleIso
    (boundaryGlobalLinearEquiv C ε hε hε1 hC hR).toModuleIso
    (globalCoefficientComplexIso C ε hε hε1 hC hR).hom.comm₁₂.symm ≪≫ coefficientKernelIso

/-- The actual middle global homology has the two explicit curve-cycle coordinates. -/
def globalHomologyIso :
    (globalLinearComplex C ε hε hε1 hC hR).homology ≅ ModuleCat.of ℂ (Fin 2 → ℂ) :=
  ShortComplex.homologyMapIso (globalCoefficientComplexIso C ε hε hε1 hC hR) ≪≫
    coefficientHomologyIso

/-- The actual last global cokernel is the P-minus-Q quotient. -/
def globalCokernelIso :
    cokernel (globalLinearComplex C ε hε hε1 hC hR).g ≅ ModuleCat.of ℂ ℂ :=
  cokernel.mapIso (globalLinearComplex C ε hε hε1 hC hR).g coefficientComplex.g
    (boundaryGlobalLinearEquiv C ε hε hε1 hC hR).toModuleIso
    (tripleGlobalLinearEquiv C ε hε).toModuleIso
    (globalCoefficientComplexIso C ε hε hε1 hC hR).hom.comm₂₃.symm ≪≫ coefficientCokernelIso

theorem globalKernel_finrank :
    Module.finrank ℂ ↥(kernel (globalLinearComplex C ε hε hε1 hC hR).f) = 1 :=
  (globalKernelIso C ε hε hε1 hC hR).toLinearEquiv.finrank_eq.trans (Module.finrank_self ℂ)

theorem globalHomology_finrank :
    Module.finrank ℂ (globalLinearComplex C ε hε hε1 hC hR).homology = 2 :=
  (globalHomologyIso C ε hε hε1 hC hR).toLinearEquiv.finrank_eq.trans
    (Module.finrank_fin_fun ℂ)

theorem globalCokernel_finrank :
    Module.finrank ℂ ↥(cokernel (globalLinearComplex C ε hε hε1 hC hR).g) = 1 :=
  (globalCokernelIso C ε hε hε1 hC hR).toLinearEquiv.finrank_eq.trans (Module.finrank_self ℂ)

end Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyGlobalSections
