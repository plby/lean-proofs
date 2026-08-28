import Wikipedia.HopfProblem.DegreeCollapseIntegralDualSequence
import Wikipedia.HopfProblem.DegreeCollapseIntegralOpenSupportCohomology
import Wikipedia.HopfProblem.DegreeCollapseIntegralRelativeMayerVietoris
import Wikipedia.NoExoticSixSphere.SmallRelativeIntegralComparison
import Wikipedia.NoExoticSixSphere.RelativeSmallMayerVietoris

/-!
# The genuine integral small-cochain Mayer--Vietoris sequence

Proved freeness of the original small-relative quotient chains makes
the reversed integral cochain row short exact. Its actual connecting
map has the three original range-kernel equalities. The integral dual
of the original small-to-union comparison is also a quasi-isomorphism.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralRelativeCohomologyMayerVietoris

open SingularCohomologyFree NoExoticSixSphere

variable {X : Type} [TopologicalSpace X] (U V : Set X)

abbrev Cohomology (U : Set X) (n : ℕ) :=
  (dualComplex (RelativeCoefficients.complex (ModuleCat.of ℤ ℤ) U)).homology n

abbrev integralSequence := RelativeMayerVietoris.smallSequence (ModuleCat.of ℤ ℤ) U V

abbrev smallSequence := IntegralDualSequence.sequence (integralSequence U V)

theorem smallSequence_shortExact : (smallSequence U V).ShortExact := by
  let (n : ℕ) : Projective ((integralSequence U V).X₃.X n) := by
    let : Module.Free ℤ ((integralSequence U V).X₃.X n) :=
      SmallRelativeIntegral.chains_free U V n
    exact ModuleCat.projective_of_categoryTheory_projective _
  exact IntegralDualSequence.sequence_shortExact (integralSequence U V)
    (RelativeMayerVietoris.smallSequence_shortExact (ModuleCat.of ℤ ℤ) U V)

abbrev SmallCohomology (n : ℕ) := (smallSequence U V).X₁.homology n

abbrev MiddleCohomology (n : ℕ) := (smallSequence U V).X₂.homology n

def smallFirstMap (n : ℕ) : SmallCohomology U V n →ₗ[ℤ] MiddleCohomology U V n :=
  (HomologicalComplex.homologyMap (smallSequence U V).f n).hom

def secondMap (n : ℕ) : MiddleCohomology U V n →ₗ[ℤ] Cohomology (U ∩ V) n :=
  (HomologicalComplex.homologyMap (smallSequence U V).g n).hom

/-- The original connecting map of the proved integral cochain row. -/
def smallConnecting (n : ℕ) : Cohomology (U ∩ V) n →ₗ[ℤ] SmallCohomology U V (n + 1) :=
  ((smallSequence_shortExact U V).δ n (n + 1) rfl).hom

theorem small_exact_left (n : ℕ) :
    LinearMap.range (smallConnecting U V n) = LinearMap.ker (smallFirstMap U V (n + 1)) :=
  ((smallSequence_shortExact U V).homology_exact₁ n (n + 1) rfl).moduleCat_range_eq_ker

theorem small_exact_middle (n : ℕ) :
    LinearMap.range (smallFirstMap U V n) = LinearMap.ker (secondMap U V n) :=
  ((smallSequence_shortExact U V).homology_exact₂ n).moduleCat_range_eq_ker

theorem small_exact_right (n : ℕ) :
    LinearMap.range (secondMap U V n) = LinearMap.ker (smallConnecting U V n) :=
  ((smallSequence_shortExact U V).homology_exact₃ n (n + 1) rfl).moduleCat_range_eq_ker

/-- Original integral small-relative cochains compute the original open-union cohomology. -/
theorem smallToUnionQuotient_dual_quasiIso (hU : IsOpen U) (hV : IsOpen V) :
    QuasiIso (dualMap (RelativeCoefficients.smallToUnionQuotient (ModuleCat.of ℤ ℤ) U V)) := by
  let (n : ℕ) : Projective
      ((RelativeCoefficients.smallRelativeComplex (ModuleCat.of ℤ ℤ) U V).X n) := by
    let : Module.Free ℤ
        ((RelativeCoefficients.smallRelativeComplex (ModuleCat.of ℤ ℤ) U V).X n) :=
      SmallRelativeIntegral.chains_free U V n
    exact ModuleCat.projective_of_categoryTheory_projective _
  let (n : ℕ) : Projective
      ((RelativeCoefficients.complex (ModuleCat.of ℤ ℤ) (U ∪ V)).X n) := by
    let : Module.Free ℤ ((RelativeCoefficients.complex (ModuleCat.of ℤ ℤ) (U ∪ V)).X n) :=
      RelativeSingularHomology.chains_free (U ∪ V) n
    exact ModuleCat.projective_of_categoryTheory_projective _
  let := IntegralRelativeMayerVietoris.smallToUnionQuotient_quasiIso U V hU hV
  exact IntegralCochainTransport.dualMap_quasiIso_of_projective
    (RelativeCoefficients.smallToUnionQuotient (ModuleCat.of ℤ ℤ) U V)

def smallUnionEquiv (hU : IsOpen U) (hV : IsOpen V) (n : ℕ) :
    Cohomology (U ∪ V) n ≃ₗ[ℤ] SmallCohomology U V n := by
  let := smallToUnionQuotient_dual_quasiIso U V hU hV
  exact (isoOfQuasiIsoAt
    (dualMap (RelativeCoefficients.smallToUnionQuotient (ModuleCat.of ℤ ℤ) U V)) n).toLinearEquiv

theorem smallUnionEquiv_toLinearMap (hU : IsOpen U) (hV : IsOpen V) (n : ℕ) :
    (smallUnionEquiv U V hU hV n).toLinearMap =
      (HomologicalComplex.homologyMap
        (dualMap (RelativeCoefficients.smallToUnionQuotient (ModuleCat.of ℤ ℤ) U V)) n).hom := rfl

end Wikipedia.HopfProblem.DegreeCollapse.IntegralRelativeCohomologyMayerVietoris
