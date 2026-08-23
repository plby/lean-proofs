import Mathlib

open Filter Set
open scoped Pointwise Topology

syntax (name := answerSyntax245Challenge) "answer(" term ")" : term

macro_rules
  | `(answer($t)) => `($t)

namespace Erdos245

theorem erdos_245 :
    answer(True) ↔ ∀ (A : Set ℕ), A.Infinite →
      atTop.Tendsto
        (fun N ↦ (A ∩ Icc 1 ⌊N⌋₊ |>.ncard : ℝ) / N) (nhds 0) →
      3 ≤ atTop.limsup
        fun N : ℝ ↦ ((A + A) ∩ Icc 1 ⌊N⌋₊ |>.ncard : EReal) /
          (A ∩ Icc 1 ⌊N⌋₊).ncard := by
  sorry

end Erdos245
