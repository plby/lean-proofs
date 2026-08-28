import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeResolution
import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeCohomologyAbstract
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyLocallyFineSmooth

/-!
# Genuine native degree-one Dolbeault cohomology

The proved original short exact sequence and the actual fine smooth-function
sheaf give every genuine `Sheaf.H` class a global closed native form
representative.  Its class vanishes exactly when the form is the actual
native antiholomorphic derivative of an actual global smooth function.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicDolbeaultThree.Cohomology

open NativeDifferential

variable (M : Type) [TopologicalSpace M] [ChartedSpace Model M]
  [IsManifold 𝓘(ℂ, Model) ω M] [IsManifold 𝓘(ℝ, Model) ∞ M]

abbrev GlobalSmooth := Functions.SmoothSection Model M ⊤
abbrev GlobalClosed := ClosedForms.ClosedFormSection Model M ⊤

/-- The original sheaf-cohomology group, not a redefinition by forms. -/
abbrev H1 := CategoryTheory.Sheaf.H.{0} (Functions.holomorphicSheaf Model M) 1

/-- The positive native connecting class of the actual global closed form. -/
def classMap : GlobalClosed M →+ H1 M :=
  CohomologyAbstract.classMap (initialComplex_shortExact M)

local instance closedH0AddCommGroup :
    AddCommGroup (CategoryTheory.Sheaf.H.{0} (ClosedForms.sheaf Model M) 0) :=
  CategoryTheory.Abelian.Ext.instAddCommGroup

/-- The map is exactly the original Ext connecting morphism, with its
canonical degree-zero section comparison and no sign alteration. -/
theorem classMap_ext (s : GlobalClosed M) :
    classMap M s =
      ((CohomologyAbstract.zeroEquiv (ClosedForms.sheaf Model M) :
        CategoryTheory.Abelian.Ext.{0}
          (CuspNormalization.SheafCohomologyResolution.unitSheaf (TopCat.of M))
          (ClosedForms.sheaf Model M) 0 ≃+ GlobalClosed M).symm s).comp
          (initialComplex_shortExact M).extClass rfl := rfl

/-- A representative has zero genuine cohomology class exactly when it
is the actual native differential of a global smooth function. -/
theorem classMap_eq_zero_iff (s : GlobalClosed M) :
    classMap M s = 0 ↔ ∃ f : GlobalSmooth M, closedSection Model M ⊤ f = s :=
  CohomologyAbstract.classMap_eq_zero_iff (initialComplex_shortExact M) s

/-- Equality of genuine classes is exactly a global native exact difference. -/
theorem classMap_eq_iff (s t : GlobalClosed M) :
    classMap M s = classMap M t ↔
      ∃ f : GlobalSmooth M, closedSection Model M ⊤ f = s - t :=
  CohomologyAbstract.classMap_eq_iff (initialComplex_shortExact M) s t

variable [T2Space M] [SigmaCompactSpace M]

omit [IsManifold 𝓘(ℂ, Model) ω M] in
/-- The actual original smooth-function sheaf is degree-one acyclic,
by the proved native smooth partitions of unity and fine-sheaf theorem. -/
theorem smooth_h1_subsingleton :
    Subsingleton (CategoryTheory.Sheaf.H.{0} (Functions.smoothSheaf Model M) 1) :=
  HolomorphicSheafCohomology.SmoothFunctions.higher_subsingleton 𝓘(ℝ, Model) M 0

/-- Every genuine degree-one class has an actual global closed native
form representative, without assuming analytic or sheaf acyclicity. -/
theorem classMap_surjective : Function.Surjective (classMap M) := by
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} (initialComplex Model M).X₂ 1) :=
    smooth_h1_subsingleton M
  exact CohomologyAbstract.classMap_surjective (initialComplex_shortExact M)

/-- Closed global native forms modulo actual globally exact native forms. -/
abbrev AdditiveQuotient := CohomologyAbstract.SectionQuotient (initialComplex Model M)

/-- The additive Dolbeault comparison with the genuine original `H¹(O)`. -/
def additiveEquiv : AdditiveQuotient M ≃+ H1 M := by
  letI : Subsingleton (CategoryTheory.Sheaf.H.{0} (initialComplex Model M).X₂ 1) :=
    smooth_h1_subsingleton M
  exact CohomologyAbstract.quotientEquiv (initialComplex_shortExact M)

@[simp] theorem additiveEquiv_mk (s : GlobalClosed M) :
    additiveEquiv M (QuotientAddGroup.mk s) = classMap M s := rfl

end Wikipedia.HopfProblem.HolomorphicDolbeaultThree.Cohomology
