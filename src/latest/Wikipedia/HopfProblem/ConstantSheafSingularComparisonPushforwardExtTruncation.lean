import Wikipedia.HopfProblem.ConstantSheafSingularComparisonPushforwardExtBasic
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonPushforwardExtFunctorBasic

/-!
# The genuine comparison between pushforward and truncation

The only nonidentity component is the native comparison between
the pushforward of a kernel and the kernel of the pushed differential.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison.PushforwardExt

open CuspNormalization.SheafCohomologyResolution
open CuspNormalization.SheafCohomologyFinitePushforward
open LowExt

universe v u v' u'

section ExactFunctor

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  (G : C ⥤ D) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  (R : CochainResolution C)

theorem map_toCycles₂ :
    G.map R.toCycles₂ ≫ kernelComparison (R.K.d 2 3) G =
      (mapCochainResolution G R).toCycles₂ :=
  map_lift_kernelComparison (R.K.d 2 3) G (R.K.d_comp_d 1 2 3)

/-- The actual comparison of the degree-two truncated short complexes. -/
def truncationShortMap : R.shortComplex.map G ⟶ (mapCochainResolution G R).shortComplex where
  τ₁ := 𝟙 _
  τ₂ := 𝟙 _
  τ₃ := kernelComparison (R.K.d 2 3) G
  comm₁₂ := (Category.id_comp _).trans (Category.comp_id _).symm
  comm₂₃ := (Category.id_comp _).trans (map_toCycles₂ G R).symm

/-- Applying an exact functor and truncating commute through the
actual identity maps and native kernel comparison. -/
def truncationMap : AugmentedResolution.Hom
    (PushforwardExtFunctor.mappedResolution G R.truncation)
    (mapCochainResolution G R).truncation where
  augmentation := 𝟙 _
  complex := truncationShortMap G R
  comm := (Category.id_comp _).trans (Category.comp_id _).symm

end ExactFunctor

variable {X Y : TopCat.{0}} [T2Space X] (f : X ⟶ Y)
  (hf : IsClosedMap f) (hfinite : ∀ y : Y, (f ⁻¹' {y}).Finite)

/-- Literal native pushforward of the actual finite augmented resolution. -/
def pushforwardAugmentedResolution (R : AugmentedResolution (AbelianSheaf X)) :
    AugmentedResolution (AbelianSheaf Y) := by
  letI := (pushforward_preservesFiniteLimitsAndColimits f hf hfinite).1
  letI := pushforward_preservesFiniteColimits f hf hfinite
  exact PushforwardExtFunctor.mappedResolution (pushforward f) R

/-- The actual finite-pushforward truncation comparison. -/
def pushforwardTruncationMap (R : CochainResolution (AbelianSheaf X)) :
    AugmentedResolution.Hom (pushforwardAugmentedResolution f hf hfinite R.truncation)
      (pushforwardResolution f hf hfinite R).truncation := by
  letI := (pushforward_preservesFiniteLimitsAndColimits f hf hfinite).1
  letI := pushforward_preservesFiniteColimits f hf hfinite
  exact truncationMap (pushforward f) R

end Wikipedia.HopfProblem.ConstantSheafSingularComparison.PushforwardExt
