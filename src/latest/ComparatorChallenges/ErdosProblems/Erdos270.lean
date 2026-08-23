/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter Finset
open scoped BigOperators Topology

noncomputable section


namespace Erdos270

open scoped Classical in
def productTerm (n k : ℕ) : ℝ :=
  ((n + 2).ascFactorial k : ℝ)⁻¹

end Erdos270

namespace Erdos270

open scoped Classical in
def Erdos270Assertion : Prop :=
  ∀ f : ℕ → ℕ,
    (∀ n, 0 < f n) →
    Tendsto f atTop atTop →
    Irrational (∑' n, productTerm n (f (n + 1)))

end Erdos270

namespace Erdos270

open scoped Classical in
theorem erdos_270 : ¬ Erdos270Assertion := by
  sorry

end Erdos270

end
