import Wikipedia.HopfProblem.CuspHolomorphicCupNonvanishingIntegralDetection
import Wikipedia.HopfProblem.CuspCentralCohomologyBaseTorusCup
import Wikipedia.HopfProblem.CuspNormalizationSheafCuspBasic
import Wikipedia.HopfProblem.SheafSingularCupComparisonSingularIntegral

/-!
# The actual nonzero complex cusp cup class

The classes are the literal complex coefficient images of the original
integral classes `γ`, `u`, and the geometric base-torus dual. The latter
evaluates to one on the original integral base-torus cycle, so its
complex image is nonzero. Both existing central-fibre types reduce to
the same actual subspace; no replacement space is used.
-/

noncomputable section

open CategoryTheory
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspHolomorphicCupNonvanishing

open ConstantSheafSingularComparison CuspNormalization.SheafResolution
open CuspCentralCohomology CuspCentralHomology

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))

/-- Actual complex-valued singular cohomology of the original central subspace. -/
abbrev ComplexCohomology (n : ℕ) :=
  (singularCochainComplex (CentralSpace C r) (AddCommGrpCat.of ℂ)).homology n

/-- The literal complex coefficient image of the original class `γ`. -/
def complexGamma : ComplexCohomology C r 1 :=
  integralToComplexCohomologyHom (CentralSpace C r) 1 (centralGammaClass C r hr hC)

/-- The literal complex coefficient image of the original class `u`. -/
def complexU : ComplexCohomology C r 1 :=
  integralToComplexCohomologyHom (CentralSpace C r) 1 (centralUClass C r hr hC)

/-- The original geometric base-torus dual with complex coefficients. -/
def complexBase : ComplexCohomology C r 2 :=
  integralToComplexCohomologyHom (CentralSpace C r) 2 (baseTorusDualClass C r hr hC)

/-- The original integral AW formula is preserved by the actual coefficient map. -/
theorem complexBase_eq_cup :
    complexBase C r hr hC = SheafSingularCupComparison.Singular.cupProduct
      (CentralSpace C r) (complexGamma C r hr hC) (complexU C r hr hC) := by
  exact (congrArg (integralToComplexCohomologyHom (CentralSpace C r) 2)
    (baseTorusDualClass_eq_cup C r hr hC)).trans
      (SheafSingularCupComparison.Singular.integralToComplex_cupProduct
        (CentralSpace C r) (centralGammaClass C r hr hC) (centralUClass C r hr hC))

/-- Literal evaluation one on the actual base torus detects this complex class. -/
theorem complexBase_ne_zero : complexBase C r hr hC ≠ 0 := by
  apply integralToComplex_two_ne_zero_of_evaluation (CentralSpace C r)
    (baseTorusDualClass C r hr hC) (baseTorusH2Class C r hr)
  intro h
  exact (one_ne_zero : (1 : ℤ) ≠ 0)
    ((baseTorusDualClass_evaluate_base C r hr hC).symm.trans h)

/-- The two original cusp one-classes have genuinely nonzero complex AW product. -/
theorem complexGamma_cup_complexU_ne_zero :
    SheafSingularCupComparison.Singular.cupProduct (CentralSpace C r)
      (complexGamma C r hr hC) (complexU C r hr hC) ≠ 0 :=
  (complexBase_eq_cup C r hr hC) ▸ complexBase_ne_zero C r hr hC

end Wikipedia.HopfProblem.CuspHolomorphicCupNonvanishing
