import Wikipedia.HopfProblem.HolomorphicFunctionSheafSphereH1LiftingLocal
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Actual section-to-stalk maps in an extension

An extension of abelian sheaves has an exact sequence of sections on the
left. When its last map is surjective on a chosen open set, the genuine
short five lemma compares that sequence with its actual stalk sequence.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.ConstantSheafFirstCohomology.Extension

open HolomorphicFunctionSheaf.SphereH1

variable {X : TopCat.{0}}

/-- Evaluation of the actual additive sheaf on an actual open set. -/
abbrev sectionFunctor (X : TopCat.{0}) (U : Opens X) :
    TopCat.Sheaf AddCommGrpCat.{0} X ⥤ AddCommGrpCat.{0} :=
  TopCat.Sheaf.forget AddCommGrpCat X ⋙
    (evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op U)

/-- The native stalk functor on additive sheaves. -/
abbrev stalkFunctor (X : TopCat.{0}) (x : X) :
    TopCat.Sheaf AddCommGrpCat.{0} X ⥤ AddCommGrpCat.{0} :=
  TopCat.Sheaf.forget AddCommGrpCat X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat x

instance sectionFunctor_additive (U : Opens X) : (sectionFunctor X U).Additive where
  map_add := by intros; rfl

/-- Germs give a genuine morphism between the section and stalk short complexes. -/
def germComplexHom (S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} X))
    (U : Opens X) (x : X) (hx : x ∈ U) :
    S.map (sectionFunctor X U) ⟶ S.map (stalkFunctor X x) where
  τ₁ := TopCat.Presheaf.germ S.X₁.obj U x hx
  τ₂ := TopCat.Presheaf.germ S.X₂.obj U x hx
  τ₃ := TopCat.Presheaf.germ S.X₃.obj U x hx
  comm₁₂ := TopCat.Presheaf.stalkFunctor_map_germ U x hx S.f.hom
  comm₂₃ := TopCat.Presheaf.stalkFunctor_map_germ U x hx S.g.hom

/-- Surjectivity at the last term makes the actual section sequence short exact. -/
theorem section_shortExact
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} X)} (hS : S.ShortExact)
    (U : Opens X) (hπ : Function.Surjective (S.g.hom.app (op U))) :
    (S.map (sectionFunctor X U)).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · exact (ShortComplex.ab_exact_iff _).mpr fun t ht => section_kernel_lift hS t ht
  · exact (AddCommGrpCat.mono_iff_injective _).mpr (section_f_injective hS U)
  · exact (AddCommGrpCat.epi_iff_surjective _).mpr hπ

/-- The actual stalk sequence is short exact. -/
theorem stalk_shortExact
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} X)} (hS : S.ShortExact)
    (x : X) : (S.map (stalkFunctor X x)).ShortExact := by
  exact hS.map_of_exact (stalkFunctor X x)

/-- In a short exact sequence, bijective germs at the endpoints and
surjectivity on sections at the last term force bijective middle germs. -/
theorem middle_germ_bijective
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} X)} (hS : S.ShortExact)
    (U : Opens X) (x : X) (hx : x ∈ U)
    (hπ : Function.Surjective (S.g.hom.app (op U)))
    (h₁ : Function.Bijective (TopCat.Presheaf.germ S.X₁.obj U x hx))
    (h₃ : Function.Bijective (TopCat.Presheaf.germ S.X₃.obj U x hx)) :
    Function.Bijective (TopCat.Presheaf.germ S.X₂.obj U x hx) := by
  let φ := germComplexHom S U x hx
  have hφ₁ : IsIso φ.τ₁ := (ConcreteCategory.isIso_iff_bijective _).mpr h₁
  have hφ₃ : IsIso φ.τ₃ := (ConcreteCategory.isIso_iff_bijective _).mpr h₃
  have hφ₂ : IsIso φ.τ₂ :=
    ShortComplex.isIso₂_of_shortExact_of_isIso₁₃ φ (section_shortExact hS U hπ)
      (stalk_shortExact hS x)
  exact (ConcreteCategory.isIso_iff_bijective φ.τ₂).mp hφ₂

end Wikipedia.HopfProblem.ConstantSheafFirstCohomology.Extension
