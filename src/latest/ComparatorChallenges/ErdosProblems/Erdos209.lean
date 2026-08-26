/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
MIT License

Copyright (c) 2026 Axiom Math.

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.

This file has been modified.
-/
import Mathlib

namespace Erdos209

abbrev PlanePoint := ℂ
abbrev PlaneLine := AffineSubspace ℝ PlanePoint

def IsLine (L : PlaneLine) : Prop :=
  Module.finrank ℝ L.direction = 1

structure LineArrangement where
  lines : Set PlaneLine
  finite : lines.Finite
  all_lines : ∀ L ∈ lines, IsLine L

noncomputable def LineArrangement.card (A : LineArrangement) : ℕ :=
  A.lines.ncard

noncomputable def LineArrangement.pointMultiplicity
    (A : LineArrangement) (p : PlanePoint) : ℕ :=
  Set.ncard {L ∈ A.lines | p ∈ (L : Set PlanePoint)}

def LinesParallel (L₁ L₂ : PlaneLine) : Prop :=
  L₁.direction = L₂.direction

def LineArrangement.pairwiseNonParallel (A : LineArrangement) : Prop :=
  ∀ L₁ ∈ A.lines, ∀ L₂ ∈ A.lines, L₁ ≠ L₂ → ¬LinesParallel L₁ L₂

def LineArrangement.IsGallaiTriangle
    (A : LineArrangement) (L₁ L₂ L₃ : PlaneLine) : Prop :=
  L₁ ∈ A.lines ∧ L₂ ∈ A.lines ∧ L₃ ∈ A.lines ∧
  L₁ ≠ L₂ ∧ L₁ ≠ L₃ ∧ L₂ ≠ L₃ ∧
  ∃ p₁₂ p₁₃ p₂₃ : PlanePoint,
    p₁₂ ∈ (L₁ : Set PlanePoint) ∧ p₁₂ ∈ (L₂ : Set PlanePoint) ∧
    p₁₃ ∈ (L₁ : Set PlanePoint) ∧ p₁₃ ∈ (L₃ : Set PlanePoint) ∧
    p₂₃ ∈ (L₂ : Set PlanePoint) ∧ p₂₃ ∈ (L₃ : Set PlanePoint) ∧
    p₁₂ ≠ p₁₃ ∧ p₁₂ ≠ p₂₃ ∧ p₁₃ ≠ p₂₃ ∧
    A.pointMultiplicity p₁₂ = 2 ∧
    A.pointMultiplicity p₁₃ = 2 ∧
    A.pointMultiplicity p₂₃ = 2

theorem not_erdos_209 :
    ∀ d : ℕ, 4 ≤ d → ∃ A : LineArrangement,
      A.card = d ∧ A.pairwiseNonParallel ∧
      (∀ p : PlanePoint, A.pointMultiplicity p ≤ 3) ∧
      ¬∃ L₁ L₂ L₃, A.IsGallaiTriangle L₁ L₂ L₃ := by
  sorry

end Erdos209
