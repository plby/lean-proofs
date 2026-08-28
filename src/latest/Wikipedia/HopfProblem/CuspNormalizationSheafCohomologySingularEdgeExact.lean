import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologySingularEdgeH2
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologySingularEdgeExactBasic

/-!
# Surjectivity and the literal zero criterion in source Lemma 9.12(iii)

The full original singular H² map is surjective and is injective on the
zero fibre of the actual normalization pullback. These are consequences
of the proved kernel equivalence, with no additional assumptions on
cohomology, scalar actions, or comparison maps.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspNormalization.SheafCohomologySingularEdge

open CuspQuotient ToricSpace SheafResolution ConstantSheafSingularComparison

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
  (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε)

/-- The original full singular H² to holomorphic H² map is surjective. -/
theorem singularH2HolomorphicLinearMap_surjective :
    letI := singularCohomologyModule (CentralSpace C ε) 2
    Function.Surjective (singularH2HolomorphicLinearMap C ε hε hε1 hC hR) :=
  Exact.surjective_of_kernel_iso (singularNormalizationH2Map C ε hε)
    (singularH2HolomorphicMap C ε hε hε1 hC hR)
    (singularH2KernelHolomorphicIso C ε hε hε1 hC hR)
    (singularH2KernelHolomorphicIso_hom C ε hε hε1 hC hR)

/-- The same original full map is injective on the literal singular normalization kernel. -/
theorem singularH2HolomorphicLinearMap_injective_on_kernel :
    letI := singularCohomologyModule (CentralSpace C ε) 2
    Set.InjOn (singularH2HolomorphicLinearMap C ε hε hε1 hC hR)
      {a | HomologicalComplex.homologyMap
        (singularPullback (AddCommGrpCat.of ℂ) (normalizationMap C ε hε).hom) 2 a = 0} :=
  Exact.injective_on_kernel_of_iso (singularNormalizationH2Map C ε hε)
    (singularH2HolomorphicMap C ε hε hε1 hC hR)
    (singularH2KernelHolomorphicIso C ε hε hε1 hC hR)
    (singularH2KernelHolomorphicIso_hom C ε hε hε1 hC hR)

/-- Exactly the manuscript's criterion: a singular class killed by
normalization has zero holomorphic image if and only if it is zero. -/
theorem singularH2Holomorphic_eq_zero_iff
    (a : (singularCochainComplex (CentralSpace C ε) (AddCommGrpCat.of ℂ)).homology 2)
    (ha : HomologicalComplex.homologyMap
      (singularPullback (AddCommGrpCat.of ℂ) (normalizationMap C ε hε).hom) 2 a = 0) :
    letI := singularCohomologyModule (CentralSpace C ε) 2
    singularH2HolomorphicLinearMap C ε hε hε1 hC hR a = 0 ↔ a = 0 :=
  Exact.zero_iff_of_kernel_iso (singularNormalizationH2Map C ε hε)
    (singularH2HolomorphicMap C ε hε hε1 hC hR)
    (singularH2KernelHolomorphicIso C ε hε hε1 hC hR)
    (singularH2KernelHolomorphicIso_hom C ε hε hε1 hC hR) a ha

end Wikipedia.HopfProblem.CuspNormalization.SheafCohomologySingularEdge
