import Mathlib.Algebra.Group.Action.Defs
import Mathlib.GroupTheory.OrderOfElement

/-!
# Finite-order fixed points through a torsion-free deck action

For a free action of a torsion-free group, an equivariant map cannot
move a periodic point to a different representative of the same orbit.
This is a purely algebraic statement: no topology or connected family
of maps is needed.
-/

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.FiniteActionFixed.Cusp

variable {Γ X : Type*} [Group Γ] [IsMulTorsionFree Γ]
  [MulAction Γ X] [IsCancelSMul Γ X]

/-- A periodic point whose image differs by a deck transformation is
already fixed, provided the deck action is free and torsion-free. -/
theorem fixed_of_finite_iterate_of_deck (T : X → X)
    (hcomm : ∀ (g : Γ) (x : X), T (g • x) = g • T x)
    (n : ℕ) (hn : 0 < n) (x : X) (hperiod : T^[n] x = x)
    (hdeck : ∃ g : Γ, T x = g • x) : T x = x := by
  obtain ⟨g, hg⟩ := hdeck
  have hiter : ∀ m : ℕ, T^[m] x = g ^ m • x := by
    intro m
    induction m with
    | zero => simp only [Function.iterate_zero_apply, pow_zero, one_smul]
    | succ m hm =>
        rw [Function.iterate_succ_apply', hm, hcomm, hg, ← mul_smul, ← pow_succ]
  have hpow : g ^ n = 1 :=
    IsCancelSMul.eq_one_of_smul ((hiter n).symm.trans hperiod)
  have hg1 : g = 1 := (isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, hpow⟩).eq_one'
  simpa only [hg1, one_smul] using hg

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.FiniteActionFixed.Cusp
