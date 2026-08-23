/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

set_option linter.style.setOption false
set_option linter.flexible false

namespace Erdos648

open Asymptotics Filter Nat Real

def P (n : ℕ) : ℕ := (n.primeFactors.max).getD 1
def is_valid_seq (n : ℕ) (l : List ℕ) : Prop :=
  l.IsChain (· < ·) ∧ (∀ m ∈ l, m ∈ Set.Ioc 0 n) ∧ (l.map P).IsChain (· > ·)
noncomputable def g (n : ℕ) : ℕ :=
  sSup { k | ∃ l, is_valid_seq n l ∧ l.length = k }
end Erdos648

open Asymptotics Filter Nat Real

namespace Erdos648

open scoped Classical in
theorem erdos_648 :
  (fun (n : ℕ) => (g n : ℝ)) =Θ[atTop]
    (fun (n : ℕ) => Real.sqrt ((n : ℝ) / Real.log (n : ℝ))) := by
  sorry

end Erdos648
