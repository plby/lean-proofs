import Wikipedia.NoExoticSixSphere.RelativeModTwoCochainExtension
import Wikipedia.NoExoticSixSphere.RelativeModTwoCochainPullback
import Wikipedia.NoExoticSixSphere.RelativeModTwoCapAbsolute
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.HomologySequence

/-!
# The genuine relative mod-two cohomology sequence

The relative-to-absolute cochain map and actual subspace restriction form
a short exact sequence. Degreewise surjectivity uses the explicit
simplex-value extension, not an injectivity assumption on `ZMod 2` as an
integer module. The original categorical sequence gives the connecting
map and exactness on the actual cohomology objects.
-/

noncomputable section

open CategoryTheory
open Wikipedia.HopfProblem SingularMayerVietoris

namespace NoExoticSixSphere.RelativeModTwoCochains

variable {X : Type} [TopologicalSpace X] (U : Set X)

/-- The actual relative cochains restrict to zero as cochain maps. -/
theorem toAbsoluteMap_pullback_zero :
    toAbsoluteMap U ≫ ModTwoCapProduct.cochainPullback (subtypeInclusion U) = 0 := by
  apply HomologicalComplex.Hom.ext
  funext p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro α
  exact pullback_toAbsolute U p α

/-- The original relative, ambient, and subspace cochain maps. -/
def sequence : ShortComplex (CochainComplex (ModuleCat.{0} ℤ) ℕ) :=
  ShortComplex.mk (toAbsoluteMap U) (ModTwoCapProduct.cochainPullback (subtypeInclusion U))
    (toAbsoluteMap_pullback_zero U)

/-- The original sequence is short exact in each actual cochain degree. -/
theorem sequence_degree_shortExact (p : ℕ) :
    ((sequence U).map
      (HomologicalComplex.eval (ModuleCat.{0} ℤ) (ComplexShape.up ℕ) p)).ShortExact where
  exact := by
    apply (ShortComplex.moduleCat_exact_iff _).mpr
    intro α hα
    change ModTwoCapProduct.Cochain X p at α
    change ModTwoCapProduct.pullback (subtypeInclusion U) p α = 0 at hα
    exact ⟨descend U p α hα, toAbsolute_descend U p α hα⟩
  mono_f := by
    apply (ModuleCat.mono_iff_injective _).mpr
    exact toAbsolute_injective U p
  epi_g := by
    apply (ModuleCat.epi_iff_surjective _).mpr
    exact pullback_subtype_surjective U p

/-- Actual short exactness of the relative cochain sequence. -/
theorem sequence_shortExact : (sequence U).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact (sequence U)
    (sequence_degree_shortExact U)

/-- The original cohomological connecting map for this pair. -/
def connecting (p : ℕ) : ModTwoCapProduct.Cohomology U p →ₗ[ℤ] Cohomology U (p + 1) :=
  ((sequence_shortExact U).δ p (p + 1) rfl).hom

/-- Exactness at the actual relative cohomology group. -/
theorem exact_at_relative (p : ℕ) :
    LinearMap.range (connecting U p) = LinearMap.ker (toAbsoluteCohomology U (p + 1)) :=
  ((sequence_shortExact U).homology_exact₁ p (p + 1) rfl).moduleCat_range_eq_ker

/-- Exactness at the original ambient cohomology group. -/
theorem exact_at_absolute (p : ℕ) :
    LinearMap.range (toAbsoluteCohomology U p) =
      LinearMap.ker (ModTwoCapProduct.cohomologyPullback (subtypeInclusion U) p) :=
  ((sequence_shortExact U).homology_exact₂ p).moduleCat_range_eq_ker

/-- Exactness at the original subspace cohomology group. -/
theorem exact_at_subspace (p : ℕ) :
    LinearMap.range (ModTwoCapProduct.cohomologyPullback (subtypeInclusion U) p) =
      LinearMap.ker (connecting U p) :=
  ((sequence_shortExact U).homology_exact₃ p (p + 1) rfl).moduleCat_range_eq_ker

end NoExoticSixSphere.RelativeModTwoCochains
