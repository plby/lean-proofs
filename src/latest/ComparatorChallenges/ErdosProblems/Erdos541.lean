/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib


open scoped Pointwise
open Multiset
open Filter

namespace Erdos541

open scoped Classical in
theorem erdos_541 : ∀ p, Fact p.Prime → ∀ (a : Fin p → ZMod p),
    (∃ r, ∀ (S : Finset (Fin p)), S ≠ ∅ → ∑ i ∈ S, a i = 0 → S.card = r) →
      (Set.range a).ncard ≤ 2 := by
  sorry

end Erdos541
