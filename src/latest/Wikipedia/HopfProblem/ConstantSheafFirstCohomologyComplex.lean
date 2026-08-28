import Wikipedia.HopfProblem.ConstantSheafFirstCohomologyVanishing
import Wikipedia.HopfProblem.CuspNormalizationSheafConstantsAdditiveBasic

/-!
# The original constant complex sheaf has vanishing first cohomology

The normalization construction uses the additive sheaf underlying the
sheafification of the constant complex ring presheaf. Its already proved
canonical isomorphism with the native constant additive sheaf transports
the genuine Ext-defined cohomology, without changing either sheaf.
-/

noncomputable section

open TopologicalSpace CategoryTheory CategoryTheory.Abelian

namespace Wikipedia.HopfProblem.ConstantSheafFirstCohomology

open CuspNormalization.SheafConstants

variable {X : TopCat.{0}}

/-- The group operations are the original operations on the native Ext group. -/
instance complexCohomologyAddCommGroup (X : TopCat.{0}) (n : ℕ) :
    AddCommGroup (CategoryTheory.Sheaf.H.{0} (complexAdditiveSheaf X) n) :=
  Ext.instAddCommGroup

/-- The native constant additive sheaf uses the same original Ext operations. -/
instance nativeCohomologyAddCommGroup (X : TopCat.{0}) (A : AddCommGrpCat.{0}) (n : ℕ) :
    AddCommGroup (CategoryTheory.Sheaf.H.{0} (Constant.sheaf X A) n) :=
  Ext.instAddCommGroup

/-- The same Ext operations for explicitly bundled underlying spaces. -/
instance complexCohomologyAddCommGroupOfType (M : Type) [TopologicalSpace M] (n : ℕ) :
    AddCommGroup (CategoryTheory.Sheaf.H.{0} (complexAdditiveSheaf (TopCat.of M)) n) :=
  Ext.instAddCommGroup

/-- The actual cohomology isomorphism induced by the original comparison
between constant complex ring and additive sheafifications. -/
def complexConstantCohomologyEquiv (X : TopCat.{0}) (n : ℕ) :
    CategoryTheory.Sheaf.H.{0} (complexAdditiveSheaf X) n ≃+
      CategoryTheory.Sheaf.H.{0} (Constant.sheaf X (AddCommGrpCat.of ℂ)) n :=
  ((CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) n).mapIso
    (complexAdditiveSheafIso X)).addCommGroupIsoToAddEquiv

/-- The forward equivalence is precisely the original induced cohomology
map, not a newly assigned scalar map. -/
theorem complexConstantCohomologyEquiv_apply (X : TopCat.{0}) (n : ℕ)
    (ξ : CategoryTheory.Sheaf.H.{0} (complexAdditiveSheaf X) n) :
    complexConstantCohomologyEquiv X n ξ =
      CategoryTheory.Sheaf.H.map.{0} (complexAdditiveSheafIso X).hom n ξ := rfl

variable [SimplyConnectedSpace X] [LocallyPathConnectedSpace X]

/-- Genuine first cohomology of the literal constant complex sheaf
vanishes on a simply connected, locally path-connected space. -/
theorem complex_h1_subsingleton :
    Subsingleton (CategoryTheory.Sheaf.H.{0} (complexAdditiveSheaf X) 1) := by
  let e := complexConstantCohomologyEquiv X 1
  have h := native_h1_subsingleton (X := X) (AddCommGrpCat.of ℂ)
  exact ⟨fun a b => e.injective (h.elim (e a) (e b))⟩

/-- Every original degree-one class is zero. -/
theorem complex_h1_eq_zero
    (ξ : CategoryTheory.Sheaf.H.{0} (complexAdditiveSheaf X) 1) : ξ = 0 :=
  complex_h1_subsingleton.elim ξ 0

/-- The native first cohomology object is a zero abelian group. -/
theorem complex_h1_isZero : Limits.IsZero
    ((CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) 1).obj
      (complexAdditiveSheaf X)) :=
  AddCommGrpCat.isZero_iff_subsingleton.mpr complex_h1_subsingleton

end Wikipedia.HopfProblem.ConstantSheafFirstCohomology
