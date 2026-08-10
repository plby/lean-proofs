import Mathlib.Data.Real.Basic
import Mathlib.Order.Fin.Basic

noncomputable section

namespace Erdos194

structure LinearOrdering {α : Type*}
    (r : α → α → Prop) : Prop where

  irrefl : ∀ a, ¬ r a a

  trans : ∀ a b c, r a b → r b c → r a c

  tri : ∀ a b, r a b ∨ a = b ∨ r b a

@[reducible]
def LinearOrdering.toPreorder {α : Type*}
    {r : α → α → Prop}
    (h : LinearOrdering r) : Preorder α where
  le x y := r x y ∨ x = y
  le_refl x := Or.inr rfl
  le_trans x y z hxy hyz := by
    rcases hxy with hxy | rfl
    · rcases hyz with hyz | rfl
      · exact Or.inl (h.trans x y z hxy hyz)
      · exact Or.inl hxy
    · exact hyz
  lt a b := r a b
  lt_iff_le_not_ge a b := by
    constructor
    · intro hab
      exact ⟨Or.inl hab, fun hba => by
        rcases hba with hba | hba
        · exact h.irrefl _
            (h.trans _ _ _ hab hba)
        · subst hba; exact h.irrefl _ hab⟩
    · rintro ⟨hab | rfl, hnle⟩
      · exact hab
      · exact absurd (Or.inr rfl) hnle

def ArithProgression (a d : ℝ) (k : ℕ) : Fin k → ℝ :=
  fun i => a + (i : ℝ) * d
end Erdos194

attribute [local instance] Classical.propDecidable

universe u_1

namespace Erdos194

end Erdos194

theorem Erdos194.erdos_194 :
    @Exists.{1} (Real → Real → Prop) fun (r : Real → Real → Prop) ↦
      @Exists.{0} (@Erdos194.LinearOrdering.{0} Real r)
        fun (hlin : @Erdos194.LinearOrdering.{0} Real r) ↦
        ∀ (k : Nat),
          @GE.ge.{0} Nat instLENat k (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
            ∀ (a d : Real),
              And
                (Not
                  (@StrictMono.{0, 0} (Fin k) Real
                    (@PartialOrder.toPreorder.{0} (Fin k) (@Fin.instPartialOrder k))
                    (@Erdos194.LinearOrdering.toPreorder.{0} Real r hlin)
                    (Erdos194.ArithProgression a d k)))
                (Not
                  (@StrictAnti.{0, 0} (Fin k) Real
                    (@PartialOrder.toPreorder.{0} (Fin k) (@Fin.instPartialOrder k))
                    (@Erdos194.LinearOrdering.toPreorder.{0} Real r hlin)
                    (Erdos194.ArithProgression a d k)))
  := by
  sorry
