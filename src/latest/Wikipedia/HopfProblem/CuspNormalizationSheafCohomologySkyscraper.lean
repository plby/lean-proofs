import Wikipedia.HopfProblem.CuspNormalizationSheaf
import Wikipedia.HopfProblem.HolomorphicFunctionSheafSphereH1ExtGlobal
import Mathlib.Algebra.Category.Grp.Injective
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-!
# Genuine acyclicity of the two actual scalar skyscrapers

A skyscraper with injective abelian coefficient group is injective as an
actual sheaf: its defining functor is right adjoint to the exact stalk
functor. The complex numbers are divisible, hence injective as an abelian
group. This proves all positive-degree cohomology vanishing for the last
term of the actual cusp normalization resolution, directly for Mathlib's
`Sheaf.H` defined by `Ext`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.CuspNormalization.SheafCohomology

attribute [local instance] Classical.propDecidable

/-- The genuine skyscraper functor sends injective abelian coefficient
groups to injective sheaves, by its actual stalk adjunction. -/
theorem skyscraper_injective {X : TopCat.{0}} (x : X) (A : AddCommGrpCat.{0})
    [Injective A] : Injective (skyscraperSheaf x A) := by
  classical
  exact Injective.injective_of_adjoint (stalkSkyscraperSheafAdjunction x) A

/-- A scalar skyscraper is an actual injective abelian sheaf. -/
theorem scalarSkyscraper_injective {X : TopCat.{0}} (x : X) :
    Injective (skyscraperSheaf x (AddCommGrpCat.of ℂ)) :=
  skyscraper_injective x (AddCommGrpCat.of ℂ)

/-- Every genuine higher cohomology group of an actual scalar skyscraper
vanishes; there is no acyclicity hypothesis. -/
theorem scalarSkyscraper_higher_subsingleton {X : TopCat.{0}} (x : X) (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H.{0}
      (skyscraperSheaf x (AddCommGrpCat.of ℂ)) (n + 1)) := by
  exact @CategoryTheory.Abelian.Ext.subsingleton_of_injective
    (TopCat.Sheaf AddCommGrpCat.{0} X) _ _ _
    (HolomorphicFunctionSheaf.SphereH1.constantIntegerSheaf X)
    (skyscraperSheaf x (AddCommGrpCat.of ℂ)) (scalarSkyscraper_injective x) n

open SheafResolution

attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)

/-- Each actual triple-point term of the normalization resolution is
injective. This uses its independently constructed skyscraper sheaf. -/
theorem triplePointSheaf_injective (t : Fin 2) :
    Injective (triplePointSheaf C ε hε t) :=
  scalarSkyscraper_injective (X := TopCat.of (CentralSpace C ε)) (triplePoint C ε hε t)

/-- The actual direct sum of the two scalar skyscrapers is injective. -/
theorem tripleSheaf_injective : Injective (tripleSheaf C ε hε) := by
  let := triplePointSheaf_injective C ε hε
  infer_instance

/-- All genuine positive-degree cohomology of the actual terminal term
in the cusp normalization resolution vanishes. -/
theorem tripleSheaf_higher_subsingleton (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H.{0} (tripleSheaf C ε hε) (n + 1)) := by
  exact @CategoryTheory.Abelian.Ext.subsingleton_of_injective
    (TopCat.Sheaf AddCommGrpCat.{0} (TopCat.of (CentralSpace C ε))) _ _ _
    (HolomorphicFunctionSheaf.SphereH1.constantIntegerSheaf (TopCat.of (CentralSpace C ε)))
    (tripleSheaf C ε hε) (tripleSheaf_injective C ε hε) n

end Wikipedia.HopfProblem.CuspNormalization.SheafCohomology
