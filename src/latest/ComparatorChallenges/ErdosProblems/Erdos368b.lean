import Mathlib

namespace Erdos368b

def P_plus (m : ℕ) : ℕ :=
  match (Nat.primeFactorsList m).maximum with
  | some p => p
  | none => 1
end Erdos368b

attribute [local instance] Classical.propDecidable

namespace Erdos368b

theorem n_n_plus_one_inf :
    Filter.Tendsto (fun n => P_plus (n * (n + 1))) Filter.atTop Filter.atTop := by
  sorry

end Erdos368b
