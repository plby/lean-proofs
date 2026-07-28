import Mathlib.Algebra.Polynomial.Basic

attribute [local instance] Classical.propDecidable

noncomputable def Erdos283.Condition :
    @Polynomial.{0} Int Int.instSemiring → Prop
  := by
  sorry

theorem Erdos283.erdos_283 :
    Iff True (∀ (p : @Polynomial.{0} Int Int.instSemiring), Erdos283.Condition p)
  := by
  sorry
