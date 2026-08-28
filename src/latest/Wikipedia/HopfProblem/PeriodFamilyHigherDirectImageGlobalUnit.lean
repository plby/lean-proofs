import Wikipedia.HopfProblem.PeriodFamilyHigherDirectImageFibreNeighborhoodRestriction
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyCechFibreInteger
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyOpenRestrictionTop

/-!
# The original global integer unit on a fibre neighborhood

Global cohomology restricts through the actual top-open representing
isomorphism and the original free-open functor. The resulting unit
agrees with the previously constructed closed-fibre neighborhood unit
after the genuine integer-sheaf map into pushforward.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage.GlobalRestriction

open HolomorphicSheafCohomology.OpenRestriction
open CuspNormalization.SheafCohomologyFinitePushforward
open HolomorphicPicard.CechExtension
open SheafHigherDirectImage.Sections

variable {X : TopCat.{0}}

/-- The actual global integer unit, restricted along the original free-open map. -/
def globalUnit (U : Opens X) : freeOpen U ⟶ integerSheaf X :=
  (freeOpenFunctor X).map (homOfLE le_top : U ⟶ ⊤) ≫ freeTopToInteger X

/-- The top-open representing unit is the original constant section of degree one. -/
theorem freeTopToInteger_section :
    freeHomEquiv (⊤ : Opens X) (integerSheaf X) (freeTopToInteger X) =
      (degreeUnit X).app (op (⊤ : Opens X)) (ULift.up (1 : ℤ)) := by
  have h := topHomEquiv_sections X (integerSheaf X) (freeTopToInteger X)
  rw [freeTopToInteger, AddEquiv.apply_symm_apply] at h
  exact h.symm

/-- The restricted unit still represents the literal original constant one. -/
theorem globalUnit_section (U : Opens X) :
    freeHomEquiv U (integerSheaf X) (globalUnit U) =
      (degreeUnit X).app (op U) (ULift.up (1 : ℤ)) := by
  rw [globalUnit, freeHomEquiv_naturality_open, freeTopToInteger_section]
  exact (ConcreteCategory.congr_hom
    ((degreeUnit X).naturality (homOfLE le_top : U ⟶ ⊤).op)
    (ULift.up (1 : ℤ))).symm

/-- Original open inclusions commute with this actual global representing map. -/
theorem globalUnit_restrict {U V : Opens X} (r : U ⟶ V) :
    (freeOpenFunctor X).map r ≫ globalUnit V = globalUnit U := by
  rw [globalUnit, globalUnit, ← Category.assoc, ← Functor.map_comp]
  congr 1

variable {T : TopCat.{0}} (i : T ⟶ X) (U : Opens X) (hU : ∀ t : T, i t ∈ U)

/-- The literal section identification on a neighborhood preserves
the genuine integer-sheaf degree section. -/
theorem sectionsEquiv_degreeUnit :
    FibreNeighborhood.sectionsEquiv i U hU (integerSheaf T)
        ((degreeUnit T).app (op ((Opens.map i).obj U)) (ULift.up (1 : ℤ))) =
      (degreeUnit T).app (op (⊤ : Opens T)) (ULift.up (1 : ℤ)) := by
  change (integerSheaf T).obj.map
      (eqToHom (congrArg op (FibreNeighborhood.inverseImage_eq_top i U hU)))
      ((degreeUnit T).app (op ((Opens.map i).obj U)) (ULift.up (1 : ℤ))) = _
  exact (ConcreteCategory.congr_hom ((degreeUnit T).naturality
    (eqToHom (congrArg op (FibreNeighborhood.inverseImage_eq_top i U hU))))
    (ULift.up (1 : ℤ))).symm

/-- The original global integer map followed by restriction is exactly
the actual closed-fibre neighborhood representing map. -/
theorem globalUnit_integerUnit :
    globalUnit U ≫ integerUnit i = FibreNeighborhood.integerUnit i U hU := by
  apply (freeHomEquiv U ((pushforward i).obj (integerSheaf T))).injective
  apply (FibreNeighborhood.sectionsEquiv i U hU (integerSheaf T)).injective
  rw [freeHomEquiv_naturality, globalUnit_section,
    PeriodFamilyHolomorphicCohomology.CechFibre.integerUnit_degreeUnit_app,
    sectionsEquiv_degreeUnit, FibreNeighborhood.integerUnit,
    FibreNeighborhood.homEquiv_sections]
  rfl

end Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage.GlobalRestriction
