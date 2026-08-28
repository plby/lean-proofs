import Wikipedia.HopfProblem.ConstantSheafSingularComparisonFlasqueInjective
import Wikipedia.HopfProblem.HolomorphicFunctionSheafSphereH1Ext
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyResolutionExt

/-!
# Genuine higher cohomology vanishes for flasque abelian sheaves

Flasqueness gives surjectivity on global sections in every short exact
sequence beginning in the given sheaf. This proves degree one vanishing
for the original Ext-defined cohomology. An actual injective presentation
then has flasque middle and cokernel sheaves, so the native Ext connecting
maps give the assertion in every positive degree.

The coefficient sheaf is arbitrary: no complex scalar structure,
compactness, or singular-cohomology comparison is assumed.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits
open CategoryTheory.Abelian

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison.Flasque

open HolomorphicFunctionSheaf.SphereH1
open CuspNormalization.SheafCohomologyResolution

variable {X : TopCat.{0}}

/-- Flasqueness lifts every genuine global section of the last sheaf
in a short exact sequence beginning in the specified sheaf. -/
theorem globalLifting_of_isFlasque (F : TopCat.Sheaf AddCommGrpCat.{0} X)
    [TopCat.Sheaf.IsFlasque F] : GlobalLifting F := by
  intro G Q ι π h hS
  have := TopCat.Sheaf.IsFlasque.epi_of_shortExact (U := ⊤) hS
  exact (AddCommGrpCat.epi_iff_surjective _).mp this

/-- Every positive genuine sheaf cohomology group of a flasque abelian
sheaf is a subsingleton. -/
theorem h_succ_subsingleton (F : TopCat.Sheaf AddCommGrpCat.{0} X)
    [TopCat.Sheaf.IsFlasque F] (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H.{0} F (n + 1)) := by
  induction n generalizing F with
  | zero =>
      exact subsingleton_h1_of_globalLifting F (globalLifting_of_isFlasque F)
  | succ n ih =>
      let p : InjectivePresentation F := Classical.arbitrary _
      have : TopCat.Sheaf.IsFlasque p.J := injective_isFlasque p.J
      have : TopCat.Sheaf.IsFlasque (cokernel p.f) :=
        TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂ p.shortExact_shortComplex
      have : Subsingleton (Ext.{0} (C := TopCat.Sheaf AddCommGrpCat.{0} X)
          (constantIntegerSheaf X) p.shortComplex.X₃ (n + 1)) :=
        ih (cokernel p.f)
      have : Subsingleton (Ext.{0} (C := TopCat.Sheaf AddCommGrpCat.{0} X)
          (constantIntegerSheaf X) p.J ((n + 1) + 1)) :=
        Ext.subsingleton_of_injective (C := TopCat.Sheaf AddCommGrpCat.{0} X) _ _ (n + 1)
      exact (connecting_surjective (C := TopCat.Sheaf AddCommGrpCat.{0} X)
        (constantIntegerSheaf X)
        p.shortExact_shortComplex (n + 1)).subsingleton

/-- Every positive Ext-defined class of the original flasque sheaf is zero. -/
theorem h_succ_eq_zero (F : TopCat.Sheaf AddCommGrpCat.{0} X)
    [TopCat.Sheaf.IsFlasque F] (n : ℕ)
    (ξ : CategoryTheory.Sheaf.H.{0} F (n + 1)) : ξ = 0 :=
  (h_succ_subsingleton F n).elim ξ 0

/-- The actual positive cohomology object of a flasque abelian sheaf is zero. -/
theorem h_succ_isZero (F : TopCat.Sheaf AddCommGrpCat.{0} X)
    [TopCat.Sheaf.IsFlasque F] (n : ℕ) :
    IsZero ((CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X)
      (n + 1)).obj F) :=
  AddCommGrpCat.isZero_iff_subsingleton.mpr (h_succ_subsingleton F n)

end Wikipedia.HopfProblem.ConstantSheafSingularComparison.Flasque
