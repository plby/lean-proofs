import Mathlib.Data.Finite.Defs

attribute [local instance] Classical.propDecidable

noncomputable def Erdos397.is_solution :
    List.{0} Nat → List.{0} Nat → Prop
  := by
  sorry

theorem Erdos397.infinite_solutions :
    @Set.Infinite.{0} (Prod.{0, 0} (List.{0} Nat) (List.{0} Nat))
      (@setOf.{0} (Prod.{0, 0} (List.{0} Nat) (List.{0} Nat))
        fun (s : Prod.{0, 0} (List.{0} Nat) (List.{0} Nat)) ↦
        Erdos397.is_solution (@Prod.fst.{0, 0} (List.{0} Nat) (List.{0} Nat) s)
          (@Prod.snd.{0, 0} (List.{0} Nat) (List.{0} Nat) s))
  := by
  sorry
