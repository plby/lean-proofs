import Mathlib.Data.Nat.Totient

set_option linter.style.setOption false
set_option linter.flexible false

namespace Erdos418

def m_BS : ℕ := 509203
end Erdos418

attribute [local instance] Classical.propDecidable

open Lean Elab Command

theorem Erdos418.erdos_418 :
    @Set.Infinite.{0} Nat
      (@Compl.compl.{0} (Set.{0} Nat) (@Set.instCompl.{0} Nat)
        (@setOf.{0} Nat fun (x : Nat) ↦
          @Exists.{1} Nat fun (n : Nat) ↦
            @Eq.{1} Nat (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) n n.totient)
              x))
  := by
  sorry
