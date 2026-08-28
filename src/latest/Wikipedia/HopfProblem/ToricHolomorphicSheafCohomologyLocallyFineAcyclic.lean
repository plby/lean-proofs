import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyLocallyFineCocycle
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyFineAcyclic

/-!
# Genuine higher acyclicity of complex-linear locally fine sheaves

Actual locally finite supported sums prove the degree-one vanishing
without compactness.  The actual Godement successor retains the local
fine decomposition and the complex scalar action.  Its genuine
injective presentation and Ext connecting map then shift every higher
degree down to degree one.  No acyclicity is an input.
-/

noncomputable section

open CategoryTheory CategoryTheory.Abelian

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology

open HolomorphicFunctionSheaf.SphereH1
open CuspNormalization.SheafCohomologyResolution

variable {X : TopCat.{0}}

/-- The actual local additive Godement successor preserves the entire
locally finite fine decomposition, with the same closed supports. -/
theorem Godement.successor_locallyFine {F : TopCat.Sheaf AddCommGrpCat.{0} X}
    (hF : LocallyFine F) : LocallyFine (Godement.successor F) :=
  hF.map Godement.successorFunctor Godement.successorFunctor_isLocal

/-- Every genuine positive-degree cohomology group of an actual
complex-linear locally fine sheaf vanishes, with no compactness assumption. -/
theorem LocallyFine.higher_subsingleton {F : TopCat.Sheaf AddCommGrpCat.{0} X}
    (hF : LocallyFine F) (ρ : ℂ →+* End F) (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H.{0} F (n + 1)) := by
  induction n generalizing F with
  | zero => exact hF.h1_subsingleton
  | succ n ih =>
    let ip := Godement.complexPresentation F ρ
    have hQ : Subsingleton (CategoryTheory.Sheaf.H.{0} (Godement.successor F) (n + 1)) :=
      ih (Godement.successor_locallyFine hF) (Godement.successorScalarEnd F ρ)
    have hs := @connecting_surjective (TopCat.Sheaf AddCommGrpCat.{0} X) _ _ _
      (constantIntegerSheaf X) ip.shortComplex ip.shortExact_shortComplex (n + 1)
      (Godement.complexPresentation_higher_subsingleton F ρ (n + 1))
    refine ⟨fun a b => ?_⟩
    obtain ⟨a', rfl⟩ := hs a
    obtain ⟨b', rfl⟩ := hs b
    exact congrArg (connecting (C := TopCat.Sheaf AddCommGrpCat.{0} X)
      (constantIntegerSheaf X) ip.shortExact_shortComplex (n + 1)) (hQ.elim a' b')

end Wikipedia.HopfProblem.HolomorphicSheafCohomology
