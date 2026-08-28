import Wikipedia.HopfProblem.PeriodFamilyHigherDirectImageFibreNeighborhoodRestriction

/-!
# Genuine fibre restriction of neighborhood cohomology classes

An actual coefficient map to the pushforward of a finite closed fibre
sheaf induces a map on the original Ext-defined neighborhood cohomology.
The proved finite-pushforward comparison identifies its target with the
original fibre cohomology. This restriction commutes with the actual
cohomology-presheaf maps when neighborhoods shrink.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage.FibreNeighborhood

open CuspNormalization.SheafCohomologyFinitePushforward

variable {T X : TopCat.{0}} [T2Space T] (i : T ⟶ X)
  (hi : IsClosedMap i) (hfinite : ∀ x : X, (i ⁻¹' {x}).Finite)
  {F : AbelianSheaf X} {G : AbelianSheaf T} (κ : F ⟶ (pushforward i).obj G)

/-- The actual coefficient map on Mathlib's original cohomology presheaves. -/
abbrev coefficientMap (n : ℕ) :
    CategoryTheory.Sheaf.cohomologyPresheaf F n ⟶
      CategoryTheory.Sheaf.cohomologyPresheaf ((pushforward i).obj G) n :=
  (CategoryTheory.Sheaf.cohomologyPresheafFunctor
    (Opens.grothendieckTopology X) n).map κ

/-- The genuine restriction to fibre cohomology of a neighborhood Ext class. -/
def cohomologyEvaluation (U : Opens X) (hU : ∀ t : T, i t ∈ U) (n : ℕ) :
    ↥(CategoryTheory.Sheaf.H'.{0} F n U) →+ CategoryTheory.Sheaf.H.{0} G n :=
  (cohomologyEquiv i hi hfinite U hU G n).toAddMonoidHom.comp
    ((coefficientMap i κ n).app (op U)).hom

@[simp] theorem cohomologyEvaluation_apply (U : Opens X) (hU : ∀ t : T, i t ∈ U)
    (n : ℕ) (a : CategoryTheory.Sheaf.H'.{0} F n U) :
    cohomologyEvaluation i hi hfinite κ U hU n a =
      cohomologyEquiv i hi hfinite U hU G n ((coefficientMap i κ n).app (op U) a) := rfl

/-- The genuine fibre evaluation is unchanged by an actual neighborhood restriction. -/
theorem cohomologyEvaluation_restrict {U V : Opens X} (r : U ⟶ V)
    (hU : ∀ t : T, i t ∈ U) (hV : ∀ t : T, i t ∈ V)
    (n : ℕ) (a : CategoryTheory.Sheaf.H'.{0} F n V) :
    cohomologyEvaluation i hi hfinite κ U hU n
      ((CategoryTheory.Sheaf.cohomologyPresheaf F n).map r.op a) =
        cohomologyEvaluation i hi hfinite κ V hV n a := by
  have he := (coefficientMap i κ n).naturality_apply r.op a
  exact (congrArg (cohomologyEquiv i hi hfinite U hU G n) he).trans
    (cohomologyEquiv_restrict i r hU hV hi hfinite G n
      ((coefficientMap i κ n).app (op V) a))

end Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage.FibreNeighborhood
