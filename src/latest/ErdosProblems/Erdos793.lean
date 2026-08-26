/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- No license was supplied for the problem-specific proof.
Modified for this repository and Lean/Mathlib 4.33.0. -/
/-
Erdős Problem 793.
Informal authors: GPT-5.6 Sol Ultra, prompted by Przemek Chojecki;
the upper-bound argument refines Paul Erdős's 1938 proof.
Formal authors: Aristotle, Wouter van Doorn.
Jake Mallen integrated the complete PNT dependency in the selected source.
Source: https://www.erdosproblems.com/793#post-7596
https://github.com/Woett/Lean-files/blob/ce4bcdac98415c60c7a7d7f78ce54c9adb79bc47/ErdosProblem793.lean
https://github.com/Jayyhk/erdos-lean/tree/cc6c94bd3f9de7c4cf7703ed40d8fd06380780a3/problems/793
Selected complete source: Lean 4.30.0, Mathlib c5ea00351c28e24afc9f0f84379aa41082b1188f.
The original single-file upload does not specify a toolchain.
This port reuses the tracked PNT+ library instead of copying its vendored proof.
-/
import ErdosProblems.Erdos793.Lower
import PrimeNumberTheoremAnd.Consequences

open Filter
open scoped Topology

namespace Erdos793

theorem erdos_793 :
    Tendsto
      (fun n : ℕ =>
        ((F n : ℝ) - Nat.primeCounting n) /
          ((n : ℝ) ^ ((2 : ℝ) / 3) / (Real.log n) ^ 2))
      atTop (𝓝 (27 / 2)) :=
  second_order_asymptotic_of_PNT _root_.pi_alt

#print axioms erdos_793
-- 'Erdos793.erdos_793' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos793
