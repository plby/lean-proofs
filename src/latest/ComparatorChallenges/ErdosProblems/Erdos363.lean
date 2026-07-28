import Mathlib.Data.Finite.Defs
import Mathlib.Data.Finset.Defs

attribute [local instance] Classical.propDecidable

noncomputable def Erdos363.is_valid_collection :
    List.{0} (Finset.{0} Nat) → Prop
  := by
  sorry

theorem Erdos363.erdos_363 :
    Not
      (@Set.Finite.{0} (List.{0} (Finset.{0} Nat))
        (@setOf.{0} (List.{0} (Finset.{0} Nat)) fun (S : List.{0} (Finset.{0} Nat)) ↦
          Erdos363.is_valid_collection S))
  := by
  sorry
