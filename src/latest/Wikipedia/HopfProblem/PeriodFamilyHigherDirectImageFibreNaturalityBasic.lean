import Wikipedia.HopfProblem.PeriodFamilyHigherDirectImageFibreEvaluation

/-!
# Coefficient naturality of actual neighborhood fibre evaluation

A commuting square of original coefficient sheaves gives a commuting
square on genuine neighborhood-to-fibre cohomology in every degree.
The target comparison is the proved finite closed-pushforward Ext
equivalence. No comparison of dimensions is used.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory

namespace Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage.FibreNeighborhood

open CuspNormalization.SheafCohomologyFinitePushforward

variable {T X : TopCat.{0}} (i : T ⟶ X)
  {F F' : AbelianSheaf X} {G G' : AbelianSheaf T}
  (κ : F ⟶ (pushforward i).obj G) (κ' : F' ⟶ (pushforward i).obj G')
  (a : F ⟶ F') (b : G ⟶ G')
  (hsq : a ≫ κ' = κ ≫ (pushforward i).map b)

include hsq

/-- The actual neighborhood cohomology functor preserves the original
commuting coefficient square. -/
theorem cohomology_coefficient_square (U : Opens X) (n : ℕ) :
    ((CategoryTheory.Sheaf.cohomologyPresheafFunctor
      (Opens.grothendieckTopology X) n).map a).app (op U) ≫
        (coefficientMap i κ' n).app (op U) =
      (coefficientMap i κ n).app (op U) ≫
        ((CategoryTheory.Sheaf.cohomologyPresheafFunctor
          (Opens.grothendieckTopology X) n).map ((pushforward i).map b)).app (op U) := by
  let Cq := CategoryTheory.Sheaf.cohomologyPresheafFunctor
    (Opens.grothendieckTopology X) n
  exact congrArg (fun η : Cq.obj F ⟶ Cq.obj ((pushforward i).obj G') => η.app (op U))
    ((Cq.map_comp a κ').symm.trans
      ((congrArg Cq.map hsq).trans (Cq.map_comp κ ((pushforward i).map b))))

/-- The same original coefficient square on literal native Ext classes. -/
theorem cohomology_coefficient_square_apply (U : Opens X) (n : ℕ)
    (x : CategoryTheory.Sheaf.H'.{0} F n U) :
    (coefficientMap i κ' n).app (op U)
        (((CategoryTheory.Sheaf.cohomologyPresheafFunctor
          (Opens.grothendieckTopology X) n).map a).app (op U) x) =
      ((CategoryTheory.Sheaf.cohomologyPresheafFunctor
        (Opens.grothendieckTopology X) n).map ((pushforward i).map b)).app (op U)
          ((coefficientMap i κ n).app (op U) x) :=
  ConcreteCategory.congr_hom (cohomology_coefficient_square i κ κ' a b hsq U n) x

variable [T2Space T] (hi : IsClosedMap i)
  (hfinite : ∀ x : X, (i ⁻¹' {x}).Finite)

/-- Genuine fiber restriction commutes with every original coefficient
square, in all native cohomological degrees. -/
theorem cohomologyEvaluation_naturality (U : Opens X) (hU : ∀ t : T, i t ∈ U)
    (n : ℕ) (x : CategoryTheory.Sheaf.H'.{0} F n U) :
    cohomologyEvaluation i hi hfinite κ' U hU n
        (((CategoryTheory.Sheaf.cohomologyPresheafFunctor
          (Opens.grothendieckTopology X) n).map a).app (op U) x) =
      CategoryTheory.Sheaf.H.map b n (cohomologyEvaluation i hi hfinite κ U hU n x) :=
  (congrArg (cohomologyEquiv i hi hfinite U hU G' n)
    (cohomology_coefficient_square_apply i κ κ' a b hsq U n x)).trans
      (cohomologyEquiv_naturality i hi hfinite U hU b n
        ((coefficientMap i κ n).app (op U) x))

end Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage.FibreNeighborhood
