import Wikipedia.HopfProblem.HolomorphicFunctionSheafSphereNegativeOneCohomologyExact
import Wikipedia.HopfProblem.HolomorphicFunctionSheafSphereNegativeOneCohomologyScalars
import Wikipedia.HopfProblem.HolomorphicFunctionSheafSphereH1NegativeOneH0
import Wikipedia.HopfProblem.HolomorphicFunctionSheafSphereH1NegativeOneH1
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologySphere
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologySkyscraper

/-!
# All genuine cohomology of the sphere infinity ideal vanishes

The original degree-zero and degree-one results are retained.  In every
higher degree, the actual infinity-ideal short exact sequence has a
surjective native Ext connecting map from a zero skyscraper cohomology
group.  The middle term's vanishing is the proved analytic cohomology
vanishing for the original holomorphic sphere sheaf.
-/

noncomputable section

open TopologicalSpace CategoryTheory
open scoped OnePoint

namespace Wikipedia.HopfProblem.HolomorphicFunctionSheaf.SphereH1.NegativeOneCohomology

open CuspNormalization.SheafCohomologyResolution

attribute [local instance] negativeOneCohomologyModule

/-- The actual skyscraper connecting map proves every degree at least two vanishes. -/
theorem negativeOne_cohomology_ge_two_subsingleton (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H.{0} negativeOneSheaf (n + 2)) := by
  have hs := @connecting_surjective
    (TopCat.Sheaf AddCommGrpCat.{0} (TopCat.of RiemannSphere)) _ _ _
    (constantIntegerSheaf (TopCat.of RiemannSphere))
    idealComplex idealComplex_shortExact (n + 1)
    (HolomorphicSheafCohomology.SphereDolbeault.holomorphic_higher_subsingleton (n + 1))
  have hSky := CuspNormalization.SheafCohomology.scalarSkyscraper_higher_subsingleton
    (X := TopCat.of RiemannSphere) (∞ : RiemannSphere) n
  refine ⟨fun a b => ?_⟩
  obtain ⟨a', rfl⟩ := hs a
  obtain ⟨b', rfl⟩ := hs b
  exact congrArg (connecting
    (C := TopCat.Sheaf AddCommGrpCat.{0} (TopCat.of RiemannSphere))
    (constantIntegerSheaf (TopCat.of RiemannSphere)) idealComplex_shortExact (n + 1))
    (hSky.elim a' b')

/-- All actual Ext-defined cohomology groups of `O(-∞)` vanish, including degree zero. -/
theorem negativeOne_cohomology_subsingleton (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H.{0} negativeOneSheaf n) := by
  cases n with
  | zero => exact negativeOne_h0_subsingleton
  | succ n =>
    cases n with
    | zero => exact negativeOne_h1_subsingleton
    | succ n => exact negativeOne_cohomology_ge_two_subsingleton n

/-- Every actual cohomology class of the infinity ideal equals zero. -/
theorem negativeOne_cohomology_eq_zero (n : ℕ)
    (x : CategoryTheory.Sheaf.H.{0} negativeOneSheaf n) : x = 0 :=
  (negativeOne_cohomology_subsingleton n).elim x 0

/-- The corresponding object of the actual cohomology functor is a zero object. -/
theorem negativeOne_cohomology_isZero (n : ℕ) : Limits.IsZero
    ((CategoryTheory.Sheaf.functorH
      (Opens.grothendieckTopology (TopCat.of RiemannSphere)) n).obj negativeOneSheaf) :=
  AddCommGrpCat.isZero_iff_subsingleton.mpr (negativeOne_cohomology_subsingleton n)

/-- The native scalar module is finite-dimensional because its underlying group is zero. -/
instance negativeOne_cohomology_finite (n : ℕ) :
    Module.Finite ℂ (CategoryTheory.Sheaf.H.{0} negativeOneSheaf n) := by
  let := negativeOne_cohomology_subsingleton n
  infer_instance

/-- The genuine sheaf-induced complex dimension is zero in every degree. -/
theorem negativeOne_cohomology_finrank (n : ℕ) :
    Module.finrank ℂ (CategoryTheory.Sheaf.H.{0} negativeOneSheaf n) = 0 := by
  let := negativeOne_cohomology_subsingleton n
  exact Module.finrank_zero_of_subsingleton

/-- The actual cohomology module is canonically the zero complex vector space. -/
def negativeOne_cohomology_zeroLinearEquiv (n : ℕ) :
    CategoryTheory.Sheaf.H.{0} negativeOneSheaf n ≃ₗ[ℂ] (Fin 0 → ℂ) := by
  letI := negativeOne_cohomology_subsingleton n
  exact LinearEquiv.ofSubsingleton _ _

end Wikipedia.HopfProblem.HolomorphicFunctionSheaf.SphereH1.NegativeOneCohomology
