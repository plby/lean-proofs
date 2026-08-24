/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos977

noncomputable def greatestPrimeFactor (m : ℕ) : ℕ :=
  if h : m.primeFactors.Nonempty then m.primeFactors.max' h else 1

def mersenne (n : ℕ) : ℕ := 2 ^ n - 1

theorem erdos_977 :
    Filter.Tendsto
      (fun n : ℕ => (Erdos977.greatestPrimeFactor (Erdos977.mersenne n) : ℝ) / (n : ℝ))
      Filter.atTop Filter.atTop := by
  sorry

end Erdos977
