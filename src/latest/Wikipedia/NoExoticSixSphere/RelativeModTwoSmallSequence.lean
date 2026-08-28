import Wikipedia.NoExoticSixSphere.ModTwoDualShortExact
import Wikipedia.NoExoticSixSphere.SmallRelativeIntegralComparison
import Wikipedia.NoExoticSixSphere.RelativeSmallMayerVietoris
import Wikipedia.NoExoticSixSphere.RelativeModTwoCochainPullback
import Mathlib.Algebra.Homology.HomologySequence

/-!
# The original relative mod-two small-cochain Mayer--Vietoris sequence

The native integral relative small-chain row has proved free quotient
terms. Dualizing its degreewise splittings gives the genuine short exact
cochain row. Its connecting map and range-kernel equalities are those of
this original sequence, before transporting the small-relative term to
the cohomology of the open union.
-/

noncomputable section

open CategoryTheory

namespace NoExoticSixSphere.RelativeModTwoMayerVietoris

variable {X : Type} [TopologicalSpace X] (U V : Set X)

abbrev integralSequence := RelativeMayerVietoris.smallSequence (ModuleCat.of ℤ ℤ) U V

/-- The actual reversed mod-two dual of the original relative small-chain row. -/
abbrev smallSequence := ModTwoDualComplex.sequence (integralSequence U V)

/-- Actual degreewise quotient freeness proves short exactness of the cochain row. -/
theorem smallSequence_shortExact : (smallSequence U V).ShortExact := by
  let (n : ℕ) : Projective ((integralSequence U V).X₃.X n) := by
    let : Module.Free ℤ ((integralSequence U V).X₃.X n) :=
      SmallRelativeIntegral.chains_free U V n
    exact ModuleCat.projective_of_categoryTheory_projective _
  exact ModTwoDualComplex.sequence_shortExact (integralSequence U V)
    (RelativeMayerVietoris.smallSequence_shortExact (ModuleCat.of ℤ ℤ) U V)

/-- Cohomology of the actual small-relative dual term. -/
abbrev SmallCohomology (n : ℕ) := (smallSequence U V).X₁.homology n

/-- Cohomology of the actual dual of the two relative chain complexes' biproduct. -/
abbrev MiddleCohomology (n : ℕ) := (smallSequence U V).X₂.homology n

def smallFirstMap (n : ℕ) : SmallCohomology U V n →ₗ[ℤ] MiddleCohomology U V n :=
  (HomologicalComplex.homologyMap (smallSequence U V).f n).hom

def secondMap (n : ℕ) : MiddleCohomology U V n →ₗ[ℤ]
    RelativeModTwoCochains.Cohomology (U ∩ V) n :=
  (HomologicalComplex.homologyMap (smallSequence U V).g n).hom

/-- The connecting map of the genuine short exact mod-two cochain sequence. -/
def smallConnecting (n : ℕ) : RelativeModTwoCochains.Cohomology (U ∩ V) n →ₗ[ℤ]
    SmallCohomology U V (n + 1) := ((smallSequence_shortExact U V).δ n (n + 1) rfl).hom

theorem small_exact_left (n : ℕ) :
    LinearMap.range (smallConnecting U V n) = LinearMap.ker (smallFirstMap U V (n + 1)) :=
  ((smallSequence_shortExact U V).homology_exact₁ n (n + 1) rfl).moduleCat_range_eq_ker

theorem small_exact_middle (n : ℕ) :
    LinearMap.range (smallFirstMap U V n) = LinearMap.ker (secondMap U V n) :=
  ((smallSequence_shortExact U V).homology_exact₂ n).moduleCat_range_eq_ker

theorem small_exact_right (n : ℕ) :
    LinearMap.range (secondMap U V n) = LinearMap.ker (smallConnecting U V n) :=
  ((smallSequence_shortExact U V).homology_exact₃ n (n + 1) rfl).moduleCat_range_eq_ker

end NoExoticSixSphere.RelativeModTwoMayerVietoris
