import Wikipedia.HopfProblem.HolomorphicPicardExtIntegerOne

/-!
# The degree-zero identity is the actual constant integer one

After the degree-zero Ext-to-Hom equivalence, the constant-sheaf adjunction
evaluates the identity at the literal lifted integer one.  Its unit is
definitionally the actual sheafification unit used by `constantIntegerOne`.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Abelian

namespace Wikipedia.HopfProblem.HolomorphicPicard.ExtExtensions

open HolomorphicFunctionSheaf.SphereH1

theorem h0_identity_eq_constantIntegerOne (X : TopCat.{0}) :
    (CategoryTheory.Sheaf.H.equiv₀.{0} (constantIntegerSheaf X)
      (show Limits.IsTerminal (⊤ : Opens X) from Limits.isTerminalTop))
        (Ext.mk₀ (𝟙 (constantIntegerSheaf X))) = constantIntegerOne X ⊤ := by
  have h₀ : Ext.addEquiv₀.{0} (Ext.mk₀ (𝟙 (constantIntegerSheaf X))) =
      𝟙 (constantIntegerSheaf X) :=
    (Ext.addEquiv₀.{0} (X := constantIntegerSheaf X)
      (Y := constantIntegerSheaf X)).apply_symm_apply _
  simp only [CategoryTheory.Sheaf.H.equiv₀, AddEquiv.trans_apply, h₀]
  rfl

end Wikipedia.HopfProblem.HolomorphicPicard.ExtExtensions
