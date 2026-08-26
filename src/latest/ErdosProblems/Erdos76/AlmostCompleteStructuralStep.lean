/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import ErdosProblems.Erdos76.AlmostCompleteD8

/-!
# The assembled almost-complete structural step

This module combines cases D5--D8 into the two-order induction step used by
the companion almost-complete theorem.  The exact-missing-edge statement is
the direct case split.  A final decreasing induction over missing edges turns
it into the `≤` statement required by `AlmostCompleteStrongAt`.
-/

namespace Erdos76

noncomputable section

attribute [local instance] Classical.propDecidable

variable {A : Type} [Fintype A] [DecidableEq A]

/-- The four structural cases exhaust every graph with the exact extremal
number of missing edges. -/
theorem almostCompleteExactStructuralCase {n a : ℕ}
    (hcard : Fintype.card A = n) (hn : 14 ≤ n) (ha : a ≤ 4)
    (G : SimpleGraph A) (hexact : missingEdgeCount G = n - 4 + a)
    (hstrong₁ : AlmostCompleteStrongAt (n - 1))
    (hstrong₂ : AlmostCompleteStrongAt (n - 2)) :
    HasStrongFractionalPacking G (a : ℝ) := by
  by_cases hD5 : ∃ u : A, n + a + 1 ≤ 3 * Gᶜ.degree u
  · obtain ⟨u, hu⟩ := hD5
    exact d5_case hcard hn ha G u hstrong₁ hexact.le hu
  · have hnoD5 : ∀ u : A, 3 * Gᶜ.degree u ≤ n + a := by
      intro u
      have hu : ¬n + a + 1 ≤ 3 * Gᶜ.degree u := by
        intro h
        exact hD5 ⟨u, h⟩
      omega
    by_cases hm : (universalVertices G).card ≤ 3
    · exact d6_case hcard hn ha G hexact hm hnoD5 hstrong₁ hstrong₂
    · have hm4 : 4 ≤ (universalVertices G).card := by omega
      by_cases ha4 : a = 4
      · subst a
        have hexactD8 : missingEdgeCount G = n := by omega
        exact d8_case hcard hn G hexactD8 hm4
          (by simpa using hnoD5) hstrong₁
      · have haLt : a < 4 := by omega
        exact d7_case hcard hn haLt G hexact hm4 hnoD5 hstrong₁

/-- Cases D5--D8, followed by the bounded downward missing-edge induction,
prove the complete local two-order structural step. -/
theorem almostCompleteStructuralStep : AlmostCompleteStructuralStep := by
  intro n hn hstrong₁ hstrong₂
  intro A _ _ hcard a ha G hmissing
  by_cases hlow : missingEdgeCount G ≤ n - 4
  · have hexactZero : ∀ H : SimpleGraph A,
        missingEdgeCount H = n - 4 →
          ∃ w : Finset A → ℝ,
            IsFractionalDecomposition H w ∧ IsHalfBounded H w := by
      intro H hH
      obtain ⟨w, hw, hunc, hhalf⟩ :=
        almostCompleteExactStructuralCase (a := 0) hcard hn (by omega) H
          (by simpa using hH) hstrong₁ hstrong₂
      have hunc0 : fractionalUncoveredWeight H w = 0 :=
        le_antisymm (by simpa using hunc)
          (fractionalUncoveredWeight_nonneg hw)
      exact ⟨w, (isFractionalDecomposition_iff hw).2 hunc0, hhalf⟩
    obtain ⟨w, hw, hhalf⟩ := halfBoundedDecomposition_of_exact_missing
      (A := A) (by omega) (m := n - 4) (by rw [hcard])
        hexactZero G hlow
    refine ⟨w, hw.isPacking, ?_, hhalf⟩
    rw [fractionalUncoveredWeight_eq_zero hw]
    positivity
  · let b := missingEdgeCount G - (n - 4)
    have hb : b ≤ a := by
      dsimp only [b]
      omega
    have hb4 : b ≤ 4 := hb.trans ha
    have hGb : missingEdgeCount G = n - 4 + b := by
      dsimp only [b]
      omega
    obtain ⟨w, hw, hunc, hhalf⟩ :=
      almostCompleteExactStructuralCase hcard hn hb4 G hGb
        hstrong₁ hstrong₂
    refine ⟨w, hw, hunc.trans ?_, hhalf⟩
    exact_mod_cast hb

end

end Erdos76
