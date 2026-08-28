import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologySingularEdgeConstants
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologySingularEdgeComparison
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologySingularEdgeKernel
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologySingularEdgeSingularLinear

/-!
# The original singular normalization map and holomorphic H² map

The singular kernel is the literal categorical kernel of the original
normalization pullback. Its scalars are the restriction of the existing
singular-cohomology scalars through its original inclusion. The full map
to holomorphic H² is the original constants inclusion under the proved
canonical comparison.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspNormalization.SheafCohomologySingularEdge

open CuspQuotient ToricSpace SheafResolution ConstantSheafSingularComparison
open SheafCohomology

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)

/-- The literal singular pullback along the original normalization map. -/
def singularNormalizationH2Map :
    (singularCochainComplex (CentralSpace C ε) (AddCommGrpCat.of ℂ)).homology 2 ⟶
      (singularCochainComplex (rayDivisor 0) (AddCommGrpCat.of ℂ)).homology 2 :=
  HomologicalComplex.homologyMap
    (singularPullback (AddCommGrpCat.of ℂ) (normalizationMap C ε hε).hom) 2

/-- The actual categorical kernel, with no replacement cohomology object. -/
abbrev singularNormalizationH2Kernel : AddCommGrpCat.{0} :=
  kernel (singularNormalizationH2Map C ε hε)

/-- The original singular normalization map respects the original scalars. -/
theorem singularNormalizationH2Map_smul (c : ℂ)
    (a : (singularCochainComplex (CentralSpace C ε) (AddCommGrpCat.of ℂ)).homology 2) :
    letI := singularCohomologyModule (CentralSpace C ε) 2
    letI := singularCohomologyModule (rayDivisor 0) 2
    singularNormalizationH2Map C ε hε (c • a) =
      c • singularNormalizationH2Map C ε hε a :=
  singularPullback_homology_smul (normalizationMap C ε hε).hom 2 c a

/-- Only restriction through the actual kernel inclusion defines this action. -/
@[instance_reducible] def singularNormalizationH2KernelModule :
    Module ℂ (singularNormalizationH2Kernel C ε hε) := by
  letI := singularCohomologyModule (CentralSpace C ε) 2
  letI := singularCohomologyModule (rayDivisor 0) 2
  exact SingularEdgeKernel.kernelModule (singularNormalizationH2Map C ε hε)
    (singularNormalizationH2Map_smul C ε hε)

/-- The actual kernel inclusion is complex-linear for the restricted action. -/
def singularNormalizationH2KernelιLinearMap :
    letI := singularCohomologyModule (CentralSpace C ε) 2
    letI := singularNormalizationH2KernelModule C ε hε
    singularNormalizationH2Kernel C ε hε →ₗ[ℂ]
      (singularCochainComplex (CentralSpace C ε) (AddCommGrpCat.of ℂ)).homology 2 := by
  letI := singularCohomologyModule (CentralSpace C ε) 2
  letI := singularCohomologyModule (rayDivisor 0) 2
  exact SingularEdgeKernel.kernelιLinearMap (singularNormalizationH2Map C ε hε)
    (singularNormalizationH2Map_smul C ε hε)

/-- The linear inclusion has the original categorical inclusion as its value. -/
@[simp] theorem singularNormalizationH2KernelιLinearMap_apply
    (a : singularNormalizationH2Kernel C ε hε) :
    letI := singularCohomologyModule (CentralSpace C ε) 2
    letI := singularNormalizationH2KernelModule C ε hε
    singularNormalizationH2KernelιLinearMap C ε hε a =
      kernel.ι (singularNormalizationH2Map C ε hε) a := rfl

variable (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε)

/-- The full original singular-to-holomorphic H² map induced by constants. -/
def singularH2HolomorphicMap :
    (singularCochainComplex (CentralSpace C ε) (AddCommGrpCat.of ℂ)).homology 2 ⟶
      AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0} (reducedSheaf C ε hε hε1 hC hR) 2) :=
  (cuspComplexSheafH2Iso C ε hε hε1 hC hR).inv ≫
    (CategoryTheory.Sheaf.functorH _ 2).map (reducedConstantsMap C ε hε hε1 hC hR)

/-- The same full cohomology map is linear for the existing actual actions. -/
def singularH2HolomorphicLinearMap :
    letI := singularCohomologyModule (CentralSpace C ε) 2
    (singularCochainComplex (CentralSpace C ε) (AddCommGrpCat.of ℂ)).homology 2 →ₗ[ℂ]
      CategoryTheory.Sheaf.H.{0} (reducedSheaf C ε hε hε1 hC hR) 2 := by
  letI : Module ℂ (CategoryTheory.Sheaf.H.{0} (constantSheaf C ε) 2) :=
    SheafCupProduct.constantCohomologyModule (TopCat.of (CentralSpace C ε)) 2
  letI := singularCohomologyModule (CentralSpace C ε) 2
  exact (constantsCohomologyLinearMap C ε hε hε1 hC hR 2).comp
    (cuspConstantH2LinearEquiv C ε hε hε1 hC hR).symm.toLinearMap

/-- Forgetting linearity recovers the unchanged original induced map. -/
@[simp] theorem singularH2HolomorphicLinearMap_asHom :
    letI := singularCohomologyModule (CentralSpace C ε) 2
    AddCommGrpCat.ofHom (singularH2HolomorphicLinearMap C ε hε hε1 hC hR).toAddMonoidHom =
      singularH2HolomorphicMap C ε hε hε1 hC hR := rfl

/-- On each class this is the actual constants map after the canonical comparison. -/
@[simp] theorem singularH2HolomorphicLinearMap_apply
    (a : (singularCochainComplex (CentralSpace C ε) (AddCommGrpCat.of ℂ)).homology 2) :
    letI := singularCohomologyModule (CentralSpace C ε) 2
    singularH2HolomorphicLinearMap C ε hε hε1 hC hR a =
      CategoryTheory.Sheaf.H.map (reducedConstantsMap C ε hε hε1 hC hR) 2
        ((cuspComplexSheafH2Iso C ε hε hε1 hC hR).inv a) := rfl

end Wikipedia.HopfProblem.CuspNormalization.SheafCohomologySingularEdge
