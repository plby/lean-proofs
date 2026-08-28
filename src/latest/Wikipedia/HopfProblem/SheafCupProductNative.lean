import Wikipedia.HopfProblem.SheafCupProductNativeBasic
import Wikipedia.HopfProblem.SheafCupProductTransport

/-!
# The genuine degree-one cup product on native sheaf cohomology

The Alexander--Whitney product on actual multiplicative Godement
cochains is transported through the proved native Ext comparisons.
Thus both arguments and the result lie in Mathlib's original sheaf
cohomology, not in a newly declared replacement group.  Literal cocycle
representatives, additivity, and degree-one skew commutativity are retained.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.SheafCupProduct

open GodementRing

variable {X : TopCat.{0}} (F : RingSheaf X) (ρ : ℂ →+* End ((forgetSheaf X).obj F))

/-- The actual Godement first-cocycle class in native sheaf cohomology. -/
def classOne : (globalData F).CocycleOne →+ H F 1 :=
  (h1CofaceEquiv F ρ).symm.toAddMonoidHom.comp (globalData F).classOne

/-- The actual Godement second-cocycle class in native sheaf cohomology. -/
def classTwo : (globalData F).CocycleTwo →+ H F 2 :=
  (h2CofaceEquiv F ρ).symm.toAddMonoidHom.comp (globalData F).classTwo

theorem classOne_surjective : Function.Surjective (classOne F ρ) :=
  (h1CofaceEquiv F ρ).symm.surjective.comp (globalData F).classOne_surjective

theorem classTwo_surjective : Function.Surjective (classTwo F ρ) :=
  (h2CofaceEquiv F ρ).symm.surjective.comp (globalData F).classTwo_surjective

/-- The genuine Alexander--Whitney H¹×H¹→H² product of the original
ring sheaf, additive in each argument. -/
def cup : H F 1 →+ H F 1 →+ H F 2 :=
  transportPairing (h1CofaceEquiv F ρ) (h2CofaceEquiv F ρ) (globalData F).cup

/-- The native product is represented by the literal Godement coface product. -/
theorem cup_comparison (a b : H F 1) :
    h2CofaceEquiv F ρ (cup F ρ a b) =
      (globalData F).cup (h1CofaceEquiv F ρ a) (h1CofaceEquiv F ρ b) :=
  transportPairing_comparison _ _ _ a b

theorem cup_classOne (a b : (globalData F).CocycleOne) :
    cup F ρ (classOne F ρ a) (classOne F ρ b) =
      classTwo F ρ ((globalData F).cupCocycle a b) := by
  apply (h2CofaceEquiv F ρ).injective
  rw [cup_comparison]
  change (globalData F).cup
      (h1CofaceEquiv F ρ ((h1CofaceEquiv F ρ).symm ((globalData F).classOne a)))
      (h1CofaceEquiv F ρ ((h1CofaceEquiv F ρ).symm ((globalData F).classOne b))) =
    h2CofaceEquiv F ρ ((h2CofaceEquiv F ρ).symm
      ((globalData F).classTwo ((globalData F).cupCocycle a b)))
  rw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  exact (globalData F).cup_classOne a b

/-- The explicit cochain boundary for the symmetric product proves
skew commutativity on the genuine native cohomology groups. -/
theorem cup_skew_comm (a b : H F 1) : cup F ρ a b = -cup F ρ b a :=
  transportPairing_skew _ _ _ (globalData F).cup_skew_comm a b

/-- The scalar action supplies injectivity proofs only; changing that
action does not change the constructed native product. -/
theorem cup_scalarAction_independent (σ : ℂ →+* End ((forgetSheaf X).obj F)) :
    cup F ρ = cup F σ := rfl

/-- In complex-valued sheaf cohomology, degree-one skew commutativity
is genuinely alternating. -/
theorem cup_self_eq_zero (a : H F 1) : cup F ρ a a = 0 := by
  let := CuspNormalization.SheafCohomology.cohomologyModule ((forgetSheaf X).obj F) ρ 2
  have hsum : cup F ρ a a + cup F ρ a a = 0 :=
    eq_neg_iff_add_eq_zero.mp (cup_skew_comm F ρ a a)
  have h : (2 : ℂ) • cup F ρ a a = 0 := by
    simpa only [two_smul] using hsum
  exact (smul_eq_zero.mp h).resolve_left (by norm_num)

end Wikipedia.HopfProblem.SheafCupProduct
