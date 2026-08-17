import Mathlib

open Filter Finset
open scoped BigOperators Topology

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Erdos270

def productTerm (n k : ℕ) : ℝ :=
  ((n + 2).ascFactorial k : ℝ)⁻¹

end Erdos270

namespace Erdos270

def Erdos270Assertion : Prop :=
  ∀ f : ℕ → ℕ,
    (∀ n, 0 < f n) →
    Tendsto f atTop atTop →
    Irrational (∑' n, productTerm n (f (n + 1)))

end Erdos270

namespace Erdos270

theorem erdos_270 : ¬ Erdos270Assertion := by
  sorry

end Erdos270

end
