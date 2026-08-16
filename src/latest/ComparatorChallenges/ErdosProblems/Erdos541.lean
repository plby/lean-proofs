import Mathlib

attribute [local instance] Classical.propDecidable

open scoped Pointwise
open Multiset
open Filter

namespace Erdos541

theorem erdos_541 : ∀ p, Fact p.Prime → ∀ (a : Fin p → ZMod p),
    (∃ r, ∀ (S : Finset (Fin p)), S ≠ ∅ → ∑ i ∈ S, a i = 0 → S.card = r) →
      (Set.range a).ncard ≤ 2 := by
  sorry

end Erdos541
