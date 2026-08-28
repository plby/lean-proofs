import Wikipedia.HopfProblem.ConstantSheafSingularComparisonPresheafBasic
import Mathlib.Algebra.Homology.Functor

/-!
# Evaluation of the native singular cochain presheaf complex

Evaluation on an open gives its original singular cochain complex.  On
the top open, the actual inclusion homeomorphism identifies this with the
original complex of the ambient space.  This records the comparison needed
when global sections of sheaves are compared with singular cochains.
-/

noncomputable section

open CategoryTheory Opposite TopologicalSpace

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison

variable (X : TopCat.{0}) (A : AddCommGrpCat.{0})

/-- The native evaluation functor on additive presheaves. -/
abbrev presheafEvaluation (U : Opens X) :
    TopCat.Presheaf AddCommGrpCat.{0} X ⥤ AddCommGrpCat.{0} :=
  (evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op U)

instance presheafEvaluation_additive (U : Opens X) :
    (presheafEvaluation X U).Additive where
  map_add := by intros; rfl

/-- Evaluating the presheaf complex retains the literal open-subspace cochains. -/
def cochainPresheafEvaluationIso (U : Opens X) :
    (((presheafEvaluation X U).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (cochainPresheafComplex X A)) ≅ singularCochainComplex U A :=
  Iso.refl _

@[simp]
theorem cochainPresheafEvaluationIso_hom_f (U : Opens X) (n : ℕ) :
    (cochainPresheafEvaluationIso X A U).hom.f n =
      𝟙 (AddCommGrpCat.of (Cochains U A n)) := rfl

/-- The actual top-open inclusion identifies global presheaf cochains with
the original ambient-space singular cochains. -/
def cochainPresheafGlobalIso :
    (((presheafEvaluation X ⊤).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (cochainPresheafComplex X A)) ≅ singularCochainComplex X A :=
  cochainPresheafEvaluationIso X A ⊤ ≪≫
    ((singularCochainFunctor A).mapIso (Opens.inclusionTopIso X).op).symm

/-- The inverse comparison is precisely pullback along the top-open inclusion. -/
@[simp]
theorem cochainPresheafGlobalIso_inv_f (n : ℕ) :
    (cochainPresheafGlobalIso X A).inv.f n =
      (singularPullback A (Opens.inclusion' (⊤ : Opens X)).hom).f n := by
  apply AddCommGrpCat.hom_ext
  ext φ
  rfl

end Wikipedia.HopfProblem.ConstantSheafSingularComparison
