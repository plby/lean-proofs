import Wikipedia.HopfProblem.CuspNormalizationSheafEvaluationSkyscraper
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Topology.Separation.Basic

/-!
# Actual skyscraper stalks away from their support

In a `T1` space, the actual categorical stalk of an additive skyscraper
sheaf vanishes at every point distinct from its support. The result
uses Mathlib's colimit computation of the skyscraper stalk.
-/

noncomputable section

open CategoryTheory Limits

namespace Wikipedia.HopfProblem.CuspNormalization.SheafTripleStalk

variable {X : TopCat.{0}} [T1Space X]

/-- The actual skyscraper stalk away from its support is a zero object. -/
theorem skyscraper_stalk_isZero_of_ne (b x : X) (A : AddCommGrpCat.{0})
    (h : x ≠ b) : IsZero ((SheafEvaluation.skyscraper b A).presheaf.stalk x) := by
  classical
  exact (skyscraperPresheafStalkOfNotSpecializesIsTerminal b A
    (fun hs => h (specializes_iff_eq.mp hs).symm)).isZero

/-- The underlying group of the actual off-support skyscraper stalk
has just one element. -/
theorem skyscraper_stalk_subsingleton_of_ne (b x : X) (A : AddCommGrpCat.{0})
    (h : x ≠ b) : Subsingleton ((SheafEvaluation.skyscraper b A).presheaf.stalk x) :=
  AddCommGrpCat.subsingleton_of_isZero (skyscraper_stalk_isZero_of_ne b x A h)

end Wikipedia.HopfProblem.CuspNormalization.SheafTripleStalk
