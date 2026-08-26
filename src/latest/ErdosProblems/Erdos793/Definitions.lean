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
import Mathlib

namespace Erdos793

/-- A finite set `A ⊆ ℕ` is *strongly 2-primitive* if, for every `a, b, c ∈ A`
with `a ≠ b` and `a ≠ c`, we have `a ∤ b * c`. -/
def Strongly2Primitive (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, a ≠ b → a ≠ c → ¬ a ∣ b * c

/-- The extremal function: the maximal cardinality of a strongly 2-primitive
subset of `[n] = {1, …, n}`. -/
noncomputable def F (n : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 n).powerset.filter Strongly2Primitive).sup Finset.card

end Erdos793
