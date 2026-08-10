import Mathlib.NumberTheory.Real.Irrational
import Std.Tactic.BVDecide.LRAT.Internal.Clause

set_option linter.style.setOption false
set_option aesop.warn.nonterminal false
set_option linter.flexible false
set_option linter.unusedSimpArgs false

namespace Erdos264

def IsIrrationalitySequence (a : ℕ → ℕ) : Prop :=
  ∀ b : ℕ → ℕ,
    BddAbove (Set.range b) →
      0 ∉ Set.range (a + b) →
        0 ∉ Set.range b →
          Irrational (∑' n, (1 : ℝ) / (a n + b n))
noncomputable section AristotleLemmas

end AristotleLemmas

noncomputable section AristotleLemmas

end AristotleLemmas

end Erdos264

attribute [local instance] Classical.propDecidable

theorem Erdos264.erdos_264.parts.i :
    Not
      (Erdos264.IsIrrationalitySequence fun (x : Nat) ↦
        @HPow.hPow.{0, 0, 0} Nat Nat Nat
          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) x)
  := by
  sorry
theorem Erdos264.erdos_264.variants.example :
    Erdos264.IsIrrationalitySequence fun (n : Nat) ↦
      @HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n)
  := by
  sorry
