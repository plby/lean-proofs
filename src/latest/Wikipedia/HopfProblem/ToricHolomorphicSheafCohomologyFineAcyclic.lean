import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyGodementLocal
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyGodementScalars
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyFineCocycle
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyResolutionExt

/-!
# Genuine higher cohomology vanishing for complex-linear fine sheaves

The degree-one case is proved by actual supported cocycle sections.
For every higher degree, the constructed Godement presentation has an
injective middle term; its actual cokernel retains both fineness and the
complex scalar action. The genuine Ext connecting map therefore shifts
the problem to the preceding degree. No vanishing theorem or comparison
with a separately defined cochain group is assumed.
-/

noncomputable section

open CategoryTheory CategoryTheory.Abelian

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology

open HolomorphicFunctionSheaf.SphereH1
open CuspNormalization.SheafCohomologyResolution

variable {X : TopCat.{0}}

/-- All positive Ext degrees of the actual constructed middle term
vanish, because that term was proved to be injective. -/
theorem Godement.complexPresentation_higher_subsingleton
    (F : TopCat.Sheaf AddCommGrpCat.{0} X) (ρ : ℂ →+* End F) (n : ℕ) :
    Subsingleton (Ext (constantIntegerSheaf X) (complexPresentation F ρ).J (n + 1)) :=
  @Ext.subsingleton_of_injective (TopCat.Sheaf AddCommGrpCat.{0} X) _ _ _
    (constantIntegerSheaf X) (complexPresentation F ρ).J
    (complexPresentation F ρ).injective n

/-- Every genuine positive-degree sheaf cohomology group of an actual
complex-linear finite-fine sheaf on a compact space is zero. -/
theorem FiniteFine.higher_subsingleton [CompactSpace X]
    {F : TopCat.Sheaf AddCommGrpCat.{0} X} (hF : FiniteFine F)
    (ρ : ℂ →+* End F) (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H.{0} F (n + 1)) := by
  induction n generalizing F with
  | zero => exact hF.h1_subsingleton
  | succ n ih =>
    let ip := Godement.complexPresentation F ρ
    have hQ : Subsingleton (CategoryTheory.Sheaf.H.{0} (Godement.successor F) (n + 1)) :=
      ih (Godement.successor_finiteFine hF) (Godement.successorScalarEnd F ρ)
    have hs := @connecting_surjective (TopCat.Sheaf AddCommGrpCat.{0} X) _ _ _
      (constantIntegerSheaf X) ip.shortComplex ip.shortExact_shortComplex (n + 1)
      (Godement.complexPresentation_higher_subsingleton F ρ (n + 1))
    refine ⟨fun a b => ?_⟩
    obtain ⟨a', rfl⟩ := hs a
    obtain ⟨b', rfl⟩ := hs b
    exact congrArg (connecting (C := TopCat.Sheaf AddCommGrpCat.{0} X)
      (constantIntegerSheaf X) ip.shortExact_shortComplex (n + 1)) (hQ.elim a' b')

end Wikipedia.HopfProblem.HolomorphicSheafCohomology
