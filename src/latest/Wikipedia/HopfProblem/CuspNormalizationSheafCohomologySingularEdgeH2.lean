import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologySingularEdgeH2Factor

/-!
# Source Lemma 9.12(iii): the actual singular H² kernel is holomorphic H²

The old additive kernel equivalence is linear for the scalar action
restricted through the original singular kernel inclusion. Its forward
map is exactly the original constants-induced H² map on that kernel.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspNormalization.SheafCohomologySingularEdge

open CuspQuotient ToricSpace SheafResolution ConstantSheafSingularComparison
open SheafCohomology SheafCohomologyConstantEdge

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
  (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε)

/-- The literal singular normalization kernel is complex-linearly
the original reduced structure sheaf's native H². -/
def singularH2KernelHolomorphicLinearEquiv :
    letI := singularNormalizationH2KernelModule C ε hε
    singularNormalizationH2Kernel C ε hε ≃ₗ[ℂ]
      CategoryTheory.Sheaf.H.{0} (reducedSheaf C ε hε hε1 hC hR) 2 := by
  letI := singularCohomologyModule (CentralSpace C ε) 2
  letI := singularCohomologyModule (rayDivisor 0) 2
  have hmap := singularH2HolomorphicLinearMap_asHom C ε hε hε1 hC hR
  have hi := congrArg (fun g => kernel.ι (singularNormalizationH2Map C ε hε) ≫ g)
    hmap.symm
  have he := (singularH2KernelHolomorphicIso_hom C ε hε hε1 hC hR).trans hi
  exact SingularEdgeKernel.linearEquivFromKernel (singularNormalizationH2Map C ε hε)
    (singularNormalizationH2Map_smul C ε hε)
    (singularH2KernelHolomorphicIso C ε hε hε1 hC hR)
    (singularH2HolomorphicLinearMap C ε hε hε1 hC hR) he

/-- The linear equivalence keeps exactly the original composed additive isomorphism. -/
@[simp] theorem singularH2KernelHolomorphicLinearEquiv_toAddEquiv :
    letI := singularNormalizationH2KernelModule C ε hε
    (singularH2KernelHolomorphicLinearEquiv C ε hε hε1 hC hR).toAddEquiv =
      (singularH2KernelHolomorphicIso C ε hε hε1 hC hR).addCommGroupIsoToAddEquiv := rfl

/-- The forward map is the original full H² map restricted by the actual inclusion. -/
theorem singularH2KernelHolomorphicLinearEquiv_apply
    (a : singularNormalizationH2Kernel C ε hε) :
    letI := singularCohomologyModule (CentralSpace C ε) 2
    letI := singularNormalizationH2KernelModule C ε hε
    singularH2KernelHolomorphicLinearEquiv C ε hε hε1 hC hR a =
      singularH2HolomorphicLinearMap C ε hε hε1 hC hR
        (kernel.ι (singularNormalizationH2Map C ε hε) a) :=
  ConcreteCategory.congr_hom (singularH2KernelHolomorphicIso_hom C ε hε hε1 hC hR) a

/-- The corresponding linear-map square retains the literal singular kernel inclusion. -/
theorem singularH2KernelHolomorphicLinearEquiv_toLinearMap :
    letI := singularCohomologyModule (CentralSpace C ε) 2
    letI := singularNormalizationH2KernelModule C ε hε
    (singularH2KernelHolomorphicLinearEquiv C ε hε hε1 hC hR).toLinearMap =
      (singularH2HolomorphicLinearMap C ε hε hε1 hC hR).comp
        (singularNormalizationH2KernelιLinearMap C ε hε) := by
  let := singularCohomologyModule (CentralSpace C ε) 2
  let := singularNormalizationH2KernelModule C ε hε
  apply LinearMap.ext
  intro a
  exact singularH2KernelHolomorphicLinearEquiv_apply C ε hε hε1 hC hR a

/-- On an original native constant edge class, the result is precisely
the old constants-to-holomorphic edge isomorphism. -/
theorem singularH2KernelHolomorphicLinearEquiv_of_constant
    (a : constantH2EdgeKernel C ε hε) :
    letI := singularNormalizationH2KernelModule C ε hε
    singularH2KernelHolomorphicLinearEquiv C ε hε hε1 hC hR
        ((normalizationH2KernelIso C ε hε hε1 hC hR).hom a) =
      (constantsH2EdgeIso C ε hε hε1 hC hR).hom a := by
  have h := (normalizationH2KernelIso C ε hε hε1 hC hR).hom_inv_id_apply a
  exact congrArg (constantsH2EdgeIso C ε hε hε1 hC hR).hom h

end Wikipedia.HopfProblem.CuspNormalization.SheafCohomologySingularEdge
