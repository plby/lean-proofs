/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos93
section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable [FiniteDimensional ℝ V]
variable [Fact (Module.finrank ℝ V = 2)]

open scoped Classical in
noncomputable def distinctDistances (s : Finset V) : Finset ℝ :=
  (s.product s).filter (fun p => p.1 ≠ p.2) |>.image (fun p => dist p.1 p.2)
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable [FiniteDimensional ℝ V]
variable [Fact (Module.finrank ℝ V = 2)]

theorem erdos_93 (s : Finset V) (n : ℕ)
    (h_n : 3 ≤ n)
    (h_card : s.card = n)
    (h_conv : ConvexIndependent ℝ (Subtype.val : s → V)) :
    (distinctDistances s).card ≥ n / 2 := by
  sorry

end
end Erdos93
