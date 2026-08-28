import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyOpenRestriction
import Mathlib.Topology.Sheaves.MayerVietoris
import Mathlib.CategoryTheory.Sites.SheafCohomology.MayerVietoris
import Mathlib.Algebra.Homology.ShortComplex.Ab

/-!
# Genuine Mayer–Vietoris exactness for actual open sets

All groups and maps are the existing Ext-defined cohomology presheaf
and the actual Mayer–Vietoris sequence supplied by Mathlib.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.MayerVietoris

variable {X : TopCat.{0}} (F : TopCat.Sheaf AddCommGrpCat.{0} X) (U V : Opens X)

/-- The actual open-set Mayer–Vietoris square. -/
abbrev square := _root_.Opens.mayerVietorisSquare U V

/-- The actual restriction pair from the union. -/
abbrev restrictionPair (n : ℕ) := (square U V).toBiprod F n

/-- The actual difference of the restrictions to the intersection. -/
abbrev restrictionDifference (n : ℕ) := (square U V).fromBiprod F n

/-- The genuine Mayer–Vietoris connecting map on Ext cohomology. -/
abbrev connecting (n : ℕ) := (square U V).δ F n (n + 1) rfl

/-- The actual two arrows through the intersection cohomology. -/
abbrev intersectionComplex (n : ℕ) : ShortComplex AddCommGrpCat.{0} :=
  ShortComplex.mk (restrictionDifference F U V n) (connecting F U V n)
    ((square U V).fromBiprod_δ F n (n + 1) rfl)

/-- The actual two arrows through the union cohomology. -/
abbrev unionComplex (n : ℕ) : ShortComplex AddCommGrpCat.{0} :=
  ShortComplex.mk (connecting F U V n) (restrictionPair F U V (n + 1))
    ((square U V).δ_toBiprod F n (n + 1) rfl)

theorem intersectionComplex_exact (n : ℕ) : (intersectionComplex F U V n).Exact :=
  ((square U V).sequence_exact F n (n + 1) rfl).exact 1

theorem unionComplex_exact (n : ℕ) : (unionComplex F U V n).Exact :=
  ((square U V).sequence_exact F n (n + 1) rfl).exact 2

/-- When the two component cohomology groups vanish, every union class
comes from the genuine connecting map. -/
theorem connecting_surjective (n : ℕ)
    [Subsingleton (CategoryTheory.Sheaf.H'.{0} F (n + 1) U)]
    [Subsingleton (CategoryTheory.Sheaf.H'.{0} F (n + 1) V)] :
    Function.Surjective (connecting F U V n) := by
  have hsub : Subsingleton
      ↥(CategoryTheory.Sheaf.H'.{0} F (n + 1) U ⊞ CategoryTheory.Sheaf.H'.{0} F (n + 1) V) :=
    (AddCommGrpCat.biprodIsoProd _ _).addCommGroupIsoToAddEquiv.injective.subsingleton
  have : Subsingleton (unionComplex F U V n).X₃ := hsub
  intro a
  exact ((unionComplex F U V n).ab_exact_iff.mp (unionComplex_exact F U V n))
    a (Subsingleton.elim _ _)

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.MayerVietoris
