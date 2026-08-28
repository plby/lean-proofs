import Wikipedia.HopfProblem.ConstantSheafSingularComparisonFineAcyclicProduct
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonFlasque
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyGodementLocal
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyFineCocycle

/-!
# Higher acyclicity of finite-fine sheaves with arbitrary abelian coefficients

The genuine product-of-stalks Godement sheaf is flasque for every abelian
coefficient sheaf: each actual skyscraper is flasque, as is their product.
Its positive cohomology therefore vanishes without any divisibility or
complex scalar hypothesis. The original Godement cokernel retains finite
fineness, and its genuine short exact sequence gives dimension shifting.

On a compact base this proves higher acyclicity of every finite-fine
abelian sheaf, using the existing actual degree-one cocycle argument.
-/

noncomputable section

open TopologicalSpace CategoryTheory CategoryTheory.Limits
open CategoryTheory.Abelian

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology

open HolomorphicFunctionSheaf.SphereH1
open CuspNormalization.SheafCohomologyResolution

variable {X : TopCat.{0}}

/-- The actual product-of-stalks Godement sheaf is flasque for arbitrary
abelian coefficients. No stalk injectivity is required. -/
theorem Godement.sheaf_isFlasque (F : TopCat.Sheaf AddCommGrpCat.{0} X) :
    TopCat.Sheaf.IsFlasque (Godement.sheaf F) := by
  classical
  have (x : X) : TopCat.Sheaf.IsFlasque (Godement.pointTerm F x) :=
    isFlasque_skyscraperSheaf_of_hasZeroObject x (F.presheaf.stalk x)
  exact ConstantSheafSingularComparison.Flasque.product_isFlasque (Godement.pointTerm F)

/-- The original germ inclusion and its actual cokernel, without an
injectivity hypothesis on the Godement term. -/
abbrev Godement.flasqueShortComplex (F : TopCat.Sheaf AddCommGrpCat.{0} X) :
    ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} X) :=
  ShortComplex.mk (Godement.inclusion F) (cokernel.π (Godement.inclusion F))
    (cokernel.condition (Godement.inclusion F))

/-- The actual Godement germ inclusion is mono, so its original cokernel
sequence is short exact for every abelian sheaf. -/
theorem Godement.flasqueShortComplex_shortExact (F : TopCat.Sheaf AddCommGrpCat.{0} X) :
    (Godement.flasqueShortComplex F).ShortExact :=
  { exact := ShortComplex.exact_cokernel (Godement.inclusion F) }

/-- Every genuine positive cohomology group of the original Godement
sheaf is zero, without a complex scalar hypothesis. -/
theorem Godement.sheaf_higher_subsingleton (F : TopCat.Sheaf AddCommGrpCat.{0} X) (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H.{0} (Godement.sheaf F) (n + 1)) := by
  have := Godement.sheaf_isFlasque F
  exact ConstantSheafSingularComparison.Flasque.h_succ_subsingleton (Godement.sheaf F) n

/-- A finite-fine abelian sheaf on a compact space has zero genuine
positive-degree sheaf cohomology, independently of its coefficient group. -/
theorem FiniteFine.higher_subsingleton_abelian [CompactSpace X]
    {F : TopCat.Sheaf AddCommGrpCat.{0} X} (hF : FiniteFine F) (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H.{0} F (n + 1)) := by
  induction n generalizing F with
  | zero => exact hF.h1_subsingleton
  | succ n ih =>
      have hQ : Subsingleton (CategoryTheory.Sheaf.H.{0}
          (Godement.successor F) (n + 1)) :=
        ih (Godement.successor_finiteFine hF)
      have hs := @connecting_surjective (TopCat.Sheaf AddCommGrpCat.{0} X) _ _ _
        (constantIntegerSheaf X) (Godement.flasqueShortComplex F)
        (Godement.flasqueShortComplex_shortExact F) (n + 1)
        (Godement.sheaf_higher_subsingleton F (n + 1))
      refine ⟨fun a b => ?_⟩
      obtain ⟨a', rfl⟩ := hs a
      obtain ⟨b', rfl⟩ := hs b
      exact congrArg (connecting (C := TopCat.Sheaf AddCommGrpCat.{0} X)
        (constantIntegerSheaf X) (Godement.flasqueShortComplex_shortExact F) (n + 1))
        (hQ.elim a' b')

/-- Every positive original sheaf cohomology class of a finite-fine
abelian sheaf on a compact space is zero. -/
theorem FiniteFine.higher_eq_zero_abelian [CompactSpace X]
    {F : TopCat.Sheaf AddCommGrpCat.{0} X} (hF : FiniteFine F) (n : ℕ)
    (ξ : CategoryTheory.Sheaf.H.{0} F (n + 1)) : ξ = 0 :=
  (hF.higher_subsingleton_abelian n).elim ξ 0

/-- The actual positive cohomology object of an arbitrary finite-fine
abelian sheaf on a compact space is zero. -/
theorem FiniteFine.higher_isZero_abelian [CompactSpace X]
    {F : TopCat.Sheaf AddCommGrpCat.{0} X} (hF : FiniteFine F) (n : ℕ) :
    IsZero ((CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X)
      (n + 1)).obj F) :=
  AddCommGrpCat.isZero_iff_subsingleton.mpr (hF.higher_subsingleton_abelian n)

end Wikipedia.HopfProblem.HolomorphicSheafCohomology
