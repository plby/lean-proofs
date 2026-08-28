import Wikipedia.HopfProblem.PeriodFamilyHigherDirectImageFibreNeighborhoodBasic

/-!
# Genuine cohomology of a finite closed sheaf on a fibre neighborhood

The original pushforward is exact and preserves injectives. Its actual
degree-zero representing map therefore compares Ext in every degree.
The open is only required to contain the image of the given finite
closed map. This supplies the actual target comparison for fibre
restriction of a cohomology class on a neighborhood.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage.FibreNeighborhood

open HolomorphicSheafCohomology.OpenRestriction
open CuspNormalization.SheafCohomologyFinitePushforward

variable {T X : TopCat.{0}} [T2Space T] (i : T ⟶ X)
  (hi : IsClosedMap i) (hfinite : ∀ x : X, (i ⁻¹' {x}).Finite)
  (U : Opens X) (hU : ∀ t : T, i t ∈ U)

/-- The actual exact-pushforward Ext map, preceded by the canonical neighborhood unit. -/
def cohomologyForward (G : AbelianSheaf T) (n : ℕ) :
    CategoryTheory.Sheaf.H.{0} G n →+
      ↥(CategoryTheory.Sheaf.H'.{0} ((pushforward i).obj G) n U) := by
  let _ := (pushforward_preservesFiniteLimitsAndColimits i hi hfinite).1
  let _ := pushforward_preservesFiniteColimits i hi hfinite
  exact ExtComparison.comparison (pushforward i) (integerUnit i U hU) G n

/-- The genuine neighborhood comparison is bijective in every actual Ext degree. -/
theorem cohomologyForward_bijective (G : AbelianSheaf T) (n : ℕ) :
    Function.Bijective (cohomologyForward i hi hfinite U hU G n) := by
  let _ := (pushforward_preservesFiniteLimitsAndColimits i hi hfinite).1
  let _ := pushforward_preservesFiniteColimits i hi hfinite
  let _ := pushforward_preservesInjectiveObjects i
  exact ExtComparison.comparison_bijective (pushforward i) (integerUnit i U hU)
    (integerUnit_bijective i U hU) G n

/-- Actual cohomology of the pushed-forward fibre sheaf on the neighborhood
is genuine cohomology of the original fibre sheaf. -/
def cohomologyEquiv (G : AbelianSheaf T) (n : ℕ) :
    ↥(CategoryTheory.Sheaf.H'.{0} ((pushforward i).obj G) n U) ≃+
      CategoryTheory.Sheaf.H.{0} G n :=
  (AddEquiv.ofBijective (cohomologyForward i hi hfinite U hU G n)
    (cohomologyForward_bijective i hi hfinite U hU G n)).symm

@[simp] theorem cohomologyEquiv_symm_apply (G : AbelianSheaf T) (n : ℕ)
    (a : CategoryTheory.Sheaf.H.{0} G n) :
    (cohomologyEquiv i hi hfinite U hU G n).symm a =
      cohomologyForward i hi hfinite U hU G n a := rfl

/-- Applying the actual forward map after the comparison recovers the original class. -/
theorem cohomologyForward_equiv (G : AbelianSheaf T) (n : ℕ)
    (a : CategoryTheory.Sheaf.H'.{0} ((pushforward i).obj G) n U) :
    cohomologyForward i hi hfinite U hU G n
      (cohomologyEquiv i hi hfinite U hU G n a) = a :=
  (cohomologyEquiv i hi hfinite U hU G n).symm_apply_apply a

/-- Actual coefficient maps commute with the genuine comparison. -/
theorem cohomologyForward_naturality {F G : AbelianSheaf T} (g : F ⟶ G)
    (n : ℕ) (a : CategoryTheory.Sheaf.H.{0} F n) :
    cohomologyForward i hi hfinite U hU G n (CategoryTheory.Sheaf.H.map g n a) =
      ((CategoryTheory.Sheaf.cohomologyPresheafFunctor
        (Opens.grothendieckTopology X) n).map ((pushforward i).map g)).app (op U)
        (cohomologyForward i hi hfinite U hU F n a) := by
  exact @ExtComparison.comparison_naturality
    (AbelianSheaf T) _ _ (AbelianSheaf X) _ _ (pushforward i) (pushforward_additive i)
    (pushforward_preservesFiniteLimitsAndColimits i hi hfinite).1
    (pushforward_preservesFiniteColimits i hi hfinite)
    (abelianSheaf_hasExt T) (abelianSheaf_hasExt X)
    (integerSheaf T) (freeOpen U) (integerUnit i U hU) F G g n a

/-- The actual inverse comparison is natural in the original fibre sheaf. -/
theorem cohomologyEquiv_naturality {F G : AbelianSheaf T} (g : F ⟶ G)
    (n : ℕ) (a : CategoryTheory.Sheaf.H'.{0} ((pushforward i).obj F) n U) :
    cohomologyEquiv i hi hfinite U hU G n
      (((CategoryTheory.Sheaf.cohomologyPresheafFunctor
        (Opens.grothendieckTopology X) n).map ((pushforward i).map g)).app (op U) a) =
      CategoryTheory.Sheaf.H.map g n (cohomologyEquiv i hi hfinite U hU F n a) := by
  apply (cohomologyForward_bijective i hi hfinite U hU G n).injective
  rw [cohomologyForward_equiv, cohomologyForward_naturality, cohomologyForward_equiv]

end Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage.FibreNeighborhood
