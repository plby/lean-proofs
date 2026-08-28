import Wikipedia.HopfProblem.SheafSingularCupComparisonResolutionRowExact
import Wikipedia.HopfProblem.SheafSingularCupComparisonResolution

/-!
# Genuine acyclicity of the actual ring-cochain row

The canonical forgotten-ring comparison identifies each term with the
original singular-cochain sheaf. The proved finite-fine theorem for that
original sheaf gives all positive Ext vanishings on a compact Hausdorff
space. The resulting low-degree resolution comparisons therefore have
no separate acyclicity or injectivity assumptions.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Wikipedia.HopfProblem.SheafSingularCupComparison.ResolutionRow

open CuspNormalization ConstantSheafSingularComparison
open RingCochains

variable (X : TopCat.{0}) [CompactSpace X] [T2Space X]

/-- Every actual forgotten ring-cochain term has zero positive sheaf cohomology. -/
theorem rowTerm_higher_subsingleton (n q : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H.{0} (rowTerm X n) (q + 1)) := by
  have hs : Subsingleton (CategoryTheory.Sheaf.H.{0}
      (cochainSheaf X (AddCommGrpCat.of ℂ) n) (q + 1)) :=
    FineCochains.cochainSheaf_higher_subsingleton X (AddCommGrpCat.of ℂ) n q
  let e := ((CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X)
    (q + 1)).mapIso (forgetSheafIso X n)).addCommGroupIsoToAddEquiv
  exact ⟨fun a b => e.injective (hs.elim (e a) (e b))⟩

/-- The genuine positive cohomology object of each row term is zero. -/
theorem rowTerm_higher_isZero (n q : ℕ) :
    IsZero ((CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X)
      (q + 1)).obj (rowTerm X n)) :=
  AddCommGrpCat.isZero_iff_subsingleton.mpr (rowTerm_higher_subsingleton X n q)

theorem row_zero_one_subsingleton (hLC : LocallyContractibleSpace X) :
    Subsingleton (CategoryTheory.Sheaf.H.{0} (rowPartialResolution X hLC).I₀ 1) :=
  rowTerm_higher_subsingleton X 0 0

theorem row_zero_two_subsingleton (hLC : LocallyContractibleSpace X) :
    Subsingleton (CategoryTheory.Sheaf.H.{0} (rowPartialResolution X hLC).I₀ 2) :=
  rowTerm_higher_subsingleton X 0 1

theorem row_one_one_subsingleton (hLC : LocallyContractibleSpace X) :
    Subsingleton (CategoryTheory.Sheaf.H.{0} (rowPartialResolution X hLC).I₁ 1) :=
  rowTerm_higher_subsingleton X 1 0

/-- The original degree-one resolution comparison, now for the actual ring-cochain row. -/
def rowH1Iso (hLC : LocallyContractibleSpace X) :
    AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0}
      (SheafConstants.complexAdditiveSheaf X) 1) ≅
        (rowPartialResolution X hLC).globalOneComplex.homology :=
  (rowPartialResolution X hLC).h1IsoAcyclic
    (h0 := row_zero_one_subsingleton X hLC)

/-- The original degree-two resolution comparison, now for the actual ring-cochain row. -/
def rowH2Iso (hLC : LocallyContractibleSpace X) :
    AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0}
      (SheafConstants.complexAdditiveSheaf X) 2) ≅
        (rowPartialResolution X hLC).globalTwoComplex.homology :=
  (rowPartialResolution X hLC).h2IsoAcyclic
    (h01 := row_zero_one_subsingleton X hLC)
    (h02 := row_zero_two_subsingleton X hLC)
    (h11 := row_one_one_subsingleton X hLC)

end Wikipedia.HopfProblem.SheafSingularCupComparison.ResolutionRow
