/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.CommonThreatGoodWeight

/-! # Swapping common-threat witnesses and the exhaustive weighted-case split -/

namespace Erdos207.CommonThreatWitness

open Finset

noncomputable section

variable {W : Type*} [DecidableEq W] {F G : Finset (Finset W)} {T T' : W}

@[simp] theorem swap_swap (w : CommonThreatWitness F G T T') : w.swap.swap = w := by
  cases w
  rfl

def swapEquiv (F G : Finset (Finset W)) (T T' : W) :
    CommonThreatWitness F G T T' ≃ CommonThreatWitness G F T' T where
  toFun := swap
  invFun := swap
  left_inv := swap_swap
  right_inv := swap_swap

@[simp] theorem swap_remainder (w : CommonThreatWitness F G T T') :
    w.swap.remainder = w.remainder := by
  change w.rightRemainder ∪ w.leftRemainder = w.leftRemainder ∪ w.rightRemainder
  exact union_comm _ _

theorem good_or_swap_good_or_equal_remainders
    (w : CommonThreatWitness F G T T') (H : Finset W) (r s : ℕ)
    (hH : H ⊆ w.remainder) (hfirst : w.first.card = r - 2) (hsecond : w.second.card = s - 2) :
    (w.exposureCode H).IsGood H r s ∨ (w.swap.exposureCode H).IsGood H s r ∨
      (H = ∅ ∧ r = s ∧ w.first.erase T = w.second.erase T') := by
  rcases w.orderedAt_or_swap H with horder | horder
  · rcases w.ordered_exponent_or_equal_remainders H hH horder r s hfirst hsecond with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  · have hH' : H ⊆ w.swap.remainder := by simpa using hH
    rcases w.swap.ordered_exponent_or_equal_remainders H hH' horder s r hsecond hfirst with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨h.1, h.2.1.symm, h.2.2.symm⟩)

end

end Erdos207.CommonThreatWitness
