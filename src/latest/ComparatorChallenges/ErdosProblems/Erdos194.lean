import Mathlib.Data.Real.Basic
import Mathlib.Order.Fin.Basic

attribute [local instance] Classical.propDecidable

universe u_1

namespace Erdos194

structure LinearOrdering {α : Type*} (r : α → α → Prop) : Prop where
  irrefl : ∀ a, ¬r a a
  trans : ∀ a b c, r a b → r b c → r a c
  tri : ∀ a b, r a b ∨ a = b ∨ r b a

end Erdos194

noncomputable def Erdos194.LinearOrdering.toPreorder :
    {α : Type u_1} → {r : α → α → Prop} → @Erdos194.LinearOrdering.{u_1} α r → Preorder.{u_1} α
  := by
  let _ := ULift.{u_1, 0} PUnit
  sorry

noncomputable def Erdos194.ArithProgression :
    Real → Real → (k : Nat) → Fin k → Real
  := by
  sorry

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
