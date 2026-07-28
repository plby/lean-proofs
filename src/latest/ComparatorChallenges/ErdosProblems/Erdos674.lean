import Mathlib.Data.Finite.Defs

attribute [local instance] Classical.propDecidable

noncomputable def Erdos674.solutionSet :
    Set.{0} (Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat))
  := by
  sorry

theorem Erdos674.erdos_674_infinite :
    @Set.Infinite.{0} (Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat)) Erdos674.solutionSet
  := by
  sorry
