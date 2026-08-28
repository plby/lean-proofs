import Wikipedia.HopfProblem.ConstantSheafSingularComparisonLowExt
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyFinitePushforwardDegreeZero

/-!
# The actual finite closed pushforward of a cochain resolution

Exactness is supplied by the proved exactness of native sheaf
pushforward. Its complex of global sections is literally the original
complex, since inverse image of the top open set is the top open set.
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

/-- Apply an actual exact functor to all terms and arrows of an
augmented cochain resolution. -/
def mapCochainResolution (R : CochainResolution C) : CochainResolution D where
  F := G.obj R.F
  K := (G.mapHomologicalComplex (ComplexShape.up ℕ)).obj R.K
  ι := G.map R.ι
  zero := (G.map_comp _ _).symm.trans ((congrArg G.map R.zero).trans (G.map_zero _ _))
  initial_exact := R.initial_exact.map G
  exact_one := R.exact_one.map G
  exact_two := R.exact_two.map G
  mono_ι := inferInstanceAs (Mono (G.map R.ι))

end ExactFunctor

variable {X Y : TopCat.{0}} [T2Space X] (f : X ⟶ Y)
  (hf : IsClosedMap f) (hfinite : ∀ y : Y, (f ⁻¹' {y}).Finite)

/-- The genuine native finite closed pushforward of the full
augmented cochain resolution. -/
def pushforwardResolution (R : CochainResolution (AbelianSheaf X)) :
    CochainResolution (AbelianSheaf Y) := by
  letI := (pushforward_preservesFiniteLimitsAndColimits f hf hfinite).1
  letI := pushforward_preservesFiniteColimits f hf hfinite
  exact mapCochainResolution (pushforward f) R

/-- No new global-section complex is substituted: the actual
pushforward complex has literally the original global sections. -/
def globalCochainIso (R : CochainResolution (AbelianSheaf X)) :
    R.globalCochainComplex ≅
      (pushforwardResolution f hf hfinite R).globalCochainComplex :=
  Iso.refl _

/-- The degree maps of the global comparison are the identity on the
literal global sections. -/
theorem globalCochainIso_hom_f (R : CochainResolution (AbelianSheaf X)) (n : ℕ) :
    (globalCochainIso f hf hfinite R).hom.f n = 𝟙 (R.globalCochainComplex.X n) := rfl

include hf hfinite in
/-- Native finite-pushforward cohomology comparison transfers the
specified acyclicity, without an independent vanishing assumption. -/
theorem pushforward_cohomology_subsingleton (F : AbelianSheaf X) (n : ℕ)
    [Subsingleton (CategoryTheory.Sheaf.H.{0} F n)] :
    Subsingleton (CategoryTheory.Sheaf.H.{0} ((pushforward f).obj F) n) :=
  ⟨fun _ _ => (cohomologyEquiv f hf hfinite F n).injective (Subsingleton.elim _ _)⟩

end Wikipedia.HopfProblem.ConstantSheafSingularComparison.PushforwardExt
