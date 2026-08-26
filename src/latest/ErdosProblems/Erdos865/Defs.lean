/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Licensed under the Apache License, Version 2.0; see LICENSE.
Modified for this repository and Lean/Mathlib 4.33.0. -/
/-
Erdős Problem 865.
Informal authors: Ricky Cipollini and GPT-5.5 Pro.
Formal proof: Aristotle; submitted by Ricky Cipollini.
Source: https://www.erdosproblems.com/865#post-7378
https://github.com/mrricky22/erdos-865-lean/tree/54bfae36c1b0384737bc23b18180bdf001816c5d
Original toolchain: Lean/Mathlib 4.28.0.
Original Mathlib commit: 8f9d9cff6bd728b17a24e163c9402775d9e6a365.
This is the complete July formalization, with the coarse theorem replaced by induction.
-/
import Mathlib

set_option linter.mathlibStandardSet false

namespace Erdos865

/-- `A` contains a *pairwise-sum triple*: distinct `a, b, c ∈ A` with
`a+b, a+c, b+c ∈ A`. -/
def HasTriple (A : Finset ℕ) : Prop :=
  ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A,
    a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ a + b ∈ A ∧ a + c ∈ A ∧ b + c ∈ A

/-- `A` is *triple-free* if it contains no pairwise-sum triple. -/
def IsTripleFree (A : Finset ℕ) : Prop := ¬ HasTriple A

/-! ### Folded additive lemma definitions -/

/-- Non-wrapped pair sums `x + y` (`x ≠ y`, both in `B`, `x + y < m`). -/
def lowSums (m : ℕ) (B : Finset ℕ) : Finset ℕ :=
  ((B ×ˢ B).filter (fun p => p.1 ≠ p.2 ∧ p.1 + p.2 < m)).image (fun p => p.1 + p.2)

/-- Wrapped pair sums `x + y - m` (`x ≠ y`, both in `B`, `x + y > m`). -/
def highSums (m : ℕ) (B : Finset ℕ) : Finset ℕ :=
  ((B ×ˢ B).filter (fun p => p.1 ≠ p.2 ∧ m < p.1 + p.2)).image (fun p => p.1 + p.2 - m)

/-- Residues arising both as a non-wrapped and as a wrapped pair sum. -/
def collisions (m : ℕ) (B : Finset ℕ) : Finset ℕ := lowSums m B ∩ highSums m B

/-- The hypothesis `(1.1)` of the folded additive lemma: `B ⊆ {1,…,m-1}` and for
all distinct `x, y ∈ B`, `x + y ≠ m` and the residue of `x + y` mod `m` is not in
`B`. -/
def FoldedOK (m : ℕ) (B : Finset ℕ) : Prop :=
  (∀ b ∈ B, 1 ≤ b ∧ b < m) ∧
  (∀ x ∈ B, ∀ y ∈ B, x ≠ y → x + y ≠ m ∧ (x + y) % m ∉ B)

/-! ### Folding definitions -/

/-- `X = {r : 1 ≤ r < h, r ∈ A}`. -/
def Xset (A : Finset ℕ) (h : ℕ) : Finset ℕ :=
  (Finset.Ico 1 h).filter (fun r => r ∈ A)

/-- `Y = {r : 1 ≤ r < h, h + r ≤ N, h + r ∈ A}`. -/
def Yset (A : Finset ℕ) (N h : ℕ) : Finset ℕ :=
  (Finset.Ico 1 h).filter (fun r => h + r ≤ N ∧ h + r ∈ A)

/-- `B_h = X ∩ Y`. -/
def Bset (A : Finset ℕ) (N h : ℕ) : Finset ℕ := Xset A h ∩ Yset A N h

/-- `E = [1, h-1] \ (X ∪ Y)`. -/
def Eset (A : Finset ℕ) (N h : ℕ) : Finset ℕ :=
  (Finset.Ico 1 h) \ (Xset A h ∪ Yset A N h)

end Erdos865
