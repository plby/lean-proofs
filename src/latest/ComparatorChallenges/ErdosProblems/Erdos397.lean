import Mathlib.Data.Finite.Defs
import Mathlib.Data.Nat.Choose.Central

namespace Erdos397

def is_solution (M N : List ℕ) : Prop :=
  (M ++ N).Nodup ∧
  (M.map Nat.centralBinom).prod = (N.map Nat.centralBinom).prod
end Erdos397

open Erdos397

attribute [local instance] Classical.propDecidable

theorem Erdos397.infinite_solutions :
    @Set.Infinite.{0} (Prod.{0, 0} (List.{0} Nat) (List.{0} Nat))
      (@Set.ofPred.{0} (Prod.{0, 0} (List.{0} Nat) (List.{0} Nat))
        fun (s : Prod.{0, 0} (List.{0} Nat) (List.{0} Nat)) ↦
        Erdos397.is_solution (@Prod.fst.{0, 0} (List.{0} Nat) (List.{0} Nat) s)
          (@Prod.snd.{0, 0} (List.{0} Nat) (List.{0} Nat) s))
  := by
  sorry
