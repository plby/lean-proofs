import Mathlib

open Set Topology

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Erdos909

theorem erdos_909 (n : ℕ) (hn : 2 ≤ n) :
    ∃ (S : Type) (_ : TopologicalSpace S),
      smallInductiveDimension S = n ∧
      smallInductiveDimension (S × S) = n := by
  sorry

end Erdos909

end
