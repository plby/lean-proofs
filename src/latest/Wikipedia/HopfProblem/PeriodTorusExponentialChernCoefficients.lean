import Wikipedia.HopfProblem.PeriodTorusExponentialChernCoefficientsBasic
import Wikipedia.HopfProblem.HolomorphicExponentialSheafIntegersInclusion

/-!
# The original exponential coefficient map detects integral torus classes

The coefficient homomorphism is the original ordinary-exponential period
map `n ↦ n * (2 * π * I)`.  Its singular cochain map acts on the original
integer-linear cochains, forgetting only their scalar structure.  The
degree-two map is therefore a map from the original integral singular
cohomology, not a map prescribed by period coordinates.

Its injectivity follows from genuine boundary detection.  This result
does not identify the exponential connecting class of a line bundle
with a separately constructed winding class: that comparison still
requires its own logarithm and derived-boundary proof.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.PeriodTorusExponentialChern.Coefficients

open FirstHurewicz ConstantSheafSingularComparison

/-- The actual coefficient homomorphism of the original exponential sequence. -/
def exponentialCoefficient : AddCommGrpCat.of ℤ ⟶ AddCommGrpCat.of ℂ :=
  AddCommGrpCat.ofHom HolomorphicExponentialSheaf.integerScalarHom

@[simp]
theorem exponentialCoefficient_apply (n : ℤ) :
    exponentialCoefficient n = (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := rfl

/-- The original integer-linear singular cochains map by their literal
ordinary-exponential coefficient values. -/
def exponentialCochainMap (p : PeriodDomain) :
    forgetIntegralCochains.obj (SingularCohomologyFree.singularCochainComplex p.Torus) ⟶
      singularCochainComplex p.Torus (AddCommGrpCat.of ℂ) :=
  (integralCochainIso p.Torus).inv ≫ coefficientMap p.Torus exponentialCoefficient

@[simp]
theorem exponentialCochainMap_apply (p : PeriodDomain) (n : ℕ)
    (φ : Chains p.Torus n →ₗ[ℤ] ℤ) (c : Chains p.Torus n) :
    (exponentialCochainMap p).f n φ c =
      (φ c : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := rfl

/-- Genuine degree-two coefficient change from the original native
integral cohomology to the actual complex-valued singular cohomology. -/
def exponentialH2Map (p : PeriodDomain) :
    integralForget.obj (SingularCohomologyFree.SingularCohomology p.Torus 2) ⟶
      (singularCochainComplex p.Torus (AddCommGrpCat.of ℂ)).homology 2 :=
  (integralCohomologyIso p.Torus 2).inv ≫
    HomologicalComplex.homologyMap (coefficientMap p.Torus exponentialCoefficient) 2

/-- The map is precisely homology of the literal native-source cochain
map, after the canonical homology comparison for forgetting scalars. -/
theorem exponentialH2Map_eq_native_cochain_map (p : PeriodDomain) :
    exponentialH2Map p =
      (forgetIntegralHomologyIso
        (SingularCohomologyFree.singularCochainComplex p.Torus) 2).inv ≫
          HomologicalComplex.homologyMap (exponentialCochainMap p) 2 := by
  simp only [exponentialH2Map, integralCohomologyIso_inv,
    exponentialCochainMap, HomologicalComplex.homologyMap_comp, Category.assoc]

/-- The same original coefficient change as an additive homomorphism. -/
def exponentialH2Hom (p : PeriodDomain) :
    SingularCohomologyFree.SingularCohomology p.Torus 2 →+
      (singularCochainComplex p.Torus (AddCommGrpCat.of ℂ)).homology 2 :=
  (exponentialH2Map p).hom

/-- The actual integral/additive comparison precedes the actual
coefficient-induced homology map. -/
@[simp]
theorem exponentialH2Hom_apply (p : PeriodDomain)
    (ξ : SingularCohomologyFree.SingularCohomology p.Torus 2) :
    exponentialH2Hom p ξ =
      HomologicalComplex.homologyMap (coefficientMap p.Torus exponentialCoefficient) 2
        ((integralCohomologyEquiv p.Torus 2).symm ξ) := rfl

/-- No class is lost by the actual exponential coefficient change on
the original period torus. -/
theorem exponentialH2Hom_injective (p : PeriodDomain) :
    Function.Injective (exponentialH2Hom p) :=
  (coefficientMap_h2_injective p exponentialCoefficient
    HolomorphicExponentialSheaf.integerScalarHom_injective).comp
      (integralCohomologyEquiv p.Torus 2).symm.injective

/-- Equality after the genuine complex coefficient change detects
equality of the original native integral classes. -/
theorem exponentialH2Hom_eq_iff (p : PeriodDomain)
    (ξ η : SingularCohomologyFree.SingularCohomology p.Torus 2) :
    exponentialH2Hom p ξ = exponentialH2Hom p η ↔ ξ = η :=
  (exponentialH2Hom_injective p).eq_iff

@[simp]
theorem exponentialH2Hom_eq_zero_iff (p : PeriodDomain)
    (ξ : SingularCohomologyFree.SingularCohomology p.Torus 2) :
    exponentialH2Hom p ξ = 0 ↔ ξ = 0 := by
  constructor
  · intro h
    exact exponentialH2Hom_injective p (h.trans (map_zero (exponentialH2Hom p)).symm)
  · rintro rfl
    exact map_zero (exponentialH2Hom p)

/-- The categorical coefficient map is a genuine monomorphism. -/
theorem exponentialH2Map_mono (p : PeriodDomain) : Mono (exponentialH2Map p) :=
  (AddCommGrpCat.mono_iff_injective (exponentialH2Map p)).mpr
    (exponentialH2Hom_injective p)

end Wikipedia.HopfProblem.PeriodTorusExponentialChern.Coefficients
