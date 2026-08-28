import Wikipedia.HopfProblem.HolomorphicPicardCechExtensionClass
import Wikipedia.HopfProblem.HolomorphicPicardCechExtensionSplitting
import Wikipedia.HopfProblem.HolomorphicPicardExtSplit

/-!
# Vanishing of the genuine extension class detects actual coboundaries

The derived-category extension class vanishes exactly when the actual
sheaf extension splits. The independently constructed local-degree-one
sections and original sheaf's kernel exactness identify splitting with
actual Čech solvability. No comparison or coboundary premise is assumed.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory

namespace Wikipedia.HopfProblem.HolomorphicPicard.CechExtension

open HolomorphicFunctionSheaf.SphereH1

variable {X : TopCat.{0}} {F : TopCat.Sheaf AddCommGrpCat.{0} X}
  {ι : Type} {U : ι → Opens X} (c : CechOneCocycle F U)

local instance : AddCommGroup (CategoryTheory.Sheaf.H.{0} F 1) :=
  CategoryTheory.Abelian.Ext.instAddCommGroup

/-- The actual sheaf-cohomology class is zero if and only if the
literal cocycle is the coboundary of actual sections on the given cover. -/
theorem classOf_eq_zero_iff_solvable (hU : ∀ x : X, ∃ i : ι, x ∈ U i) :
    classOf c hU = 0 ↔ c.Solvable :=
  (ExtExtensions.extClass_eq_zero_iff_exists_section (complex_shortExact c hU)).trans
    (exists_splitting_iff_solvable c hU)

theorem classOf_eq_zero_of_solvable (hU : ∀ x : X, ∃ i : ι, x ∈ U i)
    (hc : c.Solvable) : classOf c hU = 0 :=
  (classOf_eq_zero_iff_solvable c hU).mpr hc

end Wikipedia.HopfProblem.HolomorphicPicard.CechExtension
