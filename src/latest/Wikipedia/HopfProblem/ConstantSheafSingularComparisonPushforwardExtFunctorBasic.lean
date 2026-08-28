import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyResolutionExtNaturality
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyFinitePushforwardExt
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Exact functors applied to actual augmented resolutions

The intermediate kernels of a resolution and its image are related
by the native kernel comparison.  All maps of Ext groups below are
the native exact-functor maps, followed by precomposition at the
representing object.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison.PushforwardExtFunctor

open CuspNormalization.SheafCohomologyResolution

universe v u v' u'

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  (G : C ⥤ D) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- Apply an actual exact functor to every term and arrow of the
augmented resolution. -/
def mappedResolution (R : AugmentedResolution C) : AugmentedResolution D where
  F := G.obj R.F
  complex := R.complex.map G
  ι := G.map R.ι
  zero := (G.map_comp R.ι R.complex.f).symm.trans
    ((congrArg G.map R.zero).trans (G.map_zero _ _))
  initial_exact := R.initial_exact.map G
  exact := R.exact.map G
  mono_ι := inferInstanceAs (Mono (G.map R.ι))
  epi_g := inferInstanceAs (Epi (G.map R.complex.g))

/-- The native comparison from the mapped original intermediate
kernel to the intermediate kernel of the mapped resolution. -/
def kernelComparisonMap (R : AugmentedResolution C) :
    G.obj R.K ⟶ (mappedResolution G R).K :=
  kernelComparison R.complex.g G

@[reassoc] theorem kernelComparisonMap_ι (R : AugmentedResolution C) :
    kernelComparisonMap G R ≫ kernel.ι (mappedResolution G R).complex.g =
      G.map (kernel.ι R.complex.g) :=
  kernelComparison_comp_ι R.complex.g G

@[reassoc] theorem toK_kernelComparisonMap (R : AugmentedResolution C) :
    G.map R.toK ≫ kernelComparisonMap G R = (mappedResolution G R).toK :=
  map_lift_kernelComparison R.complex.g G R.complex.zero

/-- The actual first short exact sequence maps to the first sequence
of the mapped resolution. -/
def firstMap (R : AugmentedResolution C) :
    R.first.map G ⟶ (mappedResolution G R).first where
  τ₁ := 𝟙 _
  τ₂ := 𝟙 _
  τ₃ := kernelComparisonMap G R
  comm₁₂ := (Category.id_comp _).trans (Category.comp_id _).symm
  comm₂₃ := (Category.id_comp _).trans (toK_kernelComparisonMap G R).symm

/-- The actual second short exact sequence maps by the same kernel
comparison and identities on its other two terms. -/
def secondMap (R : AugmentedResolution C) :
    R.second.map G ⟶ (mappedResolution G R).second where
  τ₁ := kernelComparisonMap G R
  τ₂ := 𝟙 _
  τ₃ := 𝟙 _
  comm₁₂ := (kernelComparisonMap_ι G R).trans (Category.comp_id _).symm
  comm₂₃ := (Category.id_comp _).trans (Category.comp_id _).symm

variable [HasExt.{0} C] [HasExt.{0} D] {V : C} {A : D} (η : A ⟶ G.obj V)

/-- The bundled native exact-functor comparison of Ext groups. -/
def comparisonHom (Y : C) (n : ℕ) :
    AddCommGrpCat.of (Ext.{0} V Y n) ⟶ AddCommGrpCat.of (Ext.{0} A (G.obj Y) n) :=
  AddCommGrpCat.ofHom
    (CuspNormalization.SheafCohomologyFinitePushforward.ExtComparison.comparison G η Y n)

/-- The actual comparison commutes with covariant Ext maps. -/
@[reassoc] theorem comparisonHom_naturality {Y Z : C} (f : Y ⟶ Z) (n : ℕ) :
    (extFunctorObj V n).map f ≫ comparisonHom G η Z n =
      comparisonHom G η Y n ≫ (extFunctorObj A n).map (G.map f) := by
  ext e
  exact CuspNormalization.SheafCohomologyFinitePushforward.ExtComparison.comparison_naturality
    G η f e

/-- The literal termwise degree-zero comparison of the two Ext
complexes. -/
def extZeroMap (R : AugmentedResolution C) :
    R.extZeroComplex V ⟶ (mappedResolution G R).extZeroComplex A where
  τ₁ := comparisonHom G η R.complex.X₁ 0
  τ₂ := comparisonHom G η R.complex.X₂ 0
  τ₃ := comparisonHom G η R.complex.X₃ 0
  comm₁₂ := (comparisonHom_naturality G η R.complex.f 0).symm
  comm₂₃ := (comparisonHom_naturality G η R.complex.g 0).symm

/-- Map the actual Ext group of the original intermediate kernel to
that of the mapped resolution's intermediate kernel. -/
def kernelExtComparison (R : AugmentedResolution C) (n : ℕ) :
    AddCommGrpCat.of (Ext.{0} V R.K n) ⟶
      AddCommGrpCat.of (Ext.{0} A (mappedResolution G R).K n) :=
  comparisonHom G η R.K n ≫ (extFunctorObj A n).map (kernelComparisonMap G R)

end Wikipedia.HopfProblem.ConstantSheafSingularComparison.PushforwardExtFunctor
