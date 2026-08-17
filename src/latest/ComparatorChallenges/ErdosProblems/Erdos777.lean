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
import Mathlib

/-!
# Erdős Problem 777

This file formalizes the three-part resolution of the Daykin--Erdős problem
on comparable pairs in a family of subsets of `[n]`.

* the first question is affirmative;
* the proposed constant-density bound in the second question is false;
* the third question is affirmative.

The mathematical proof and the detailed map to the declarations below are in
`tex/777.tex`.
-/

open scoped BigOperators NNReal

namespace Erdos777

noncomputable section

/-- The comparability graph of a finite family of finite sets.  Vertices are
members of the family, and adjacency is strict containment in either
direction. -/
def comparableGraph {α : Type*} [DecidableEq α]
    (𝓕 : Finset (Finset α)) : SimpleGraph {A // A ∈ 𝓕} where
  Adj A B := A.1 < B.1 ∨ B.1 < A.1
  symm := ⟨by intro A B; tauto⟩
  loopless := ⟨by intro A h; exact (lt_irrefl A.1) (h.elim id id)⟩

instance comparableGraph_instDecidableRel {α : Type*} [DecidableEq α]
    (𝓕 : Finset (Finset α)) : DecidableRel (comparableGraph 𝓕).Adj :=
  fun _ _ ↦ Classical.propDecidable _

@[simp] theorem comparableGraph_adj {α : Type*} [DecidableEq α]
    {𝓕 : Finset (Finset α)} {A B : {S // S ∈ 𝓕}} :
    (comparableGraph 𝓕).Adj A B ↔ A.1 < B.1 ∨ B.1 < A.1 :=
  Iff.rfl

/-- The number of unordered strict comparable pairs in `𝓕`. -/
def comparableEdges {α : Type*} [Fintype α] [DecidableEq α]
    (𝓕 : Finset (Finset α)) : ℕ :=
  (comparableGraph 𝓕).edgeFinset.card

/-- Strictly oriented containment pairs.  Every unoriented edge of the
comparability graph has a unique orientation of this form. -/
def strictContainments {α : Type*} [DecidableEq α]
    (𝓕 : Finset (Finset α)) : ℕ :=
  (Finset.univ.filter fun p : {A // A ∈ 𝓕} × {B // B ∈ 𝓕} ↦ p.1.1 < p.2.1).card

/-- The affirmative answer to the first question in Problem 777. -/
def FirstQuestion : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ 𝓕 : Finset (Finset (Fin n)),
      (𝓕.card : ℝ) ≤ (2 - ε) * (2 : ℝ) ^ ((n : ℝ) / 2) →
      comparableEdges 𝓕 < 2 ^ n

/-- The uniform `O_c(2^{n/2})` assertion proposed in the second question. -/
def SecondQuestion : Prop :=
  ∀ c : ℝ, 0 < c →
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ 𝓕 : Finset (Finset (Fin n)),
      c * (𝓕.card : ℝ) ^ 2 ≤ comparableEdges 𝓕 →
      (𝓕.card : ℝ) ≤ C * (2 : ℝ) ^ ((n : ℝ) / 2)

/-- The affirmative answer to the third question in Problem 777. -/
def ThirdQuestion : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ δ : ℝ, 0 < δ ∧ ∀ n : ℕ, ∀ 𝓕 : Finset (Finset (Fin n)),
      (𝓕.card : ℝ) ^ (2 - δ) < comparableEdges 𝓕 →
      (𝓕.card : ℝ) < (2 + ε) ^ ((n : ℝ) / 2)

/-- The exact yes/no resolution of all three questions. -/
def Resolution : Prop := FirstQuestion ∧ ¬ SecondQuestion ∧ ThirdQuestion

theorem erdos777 : Resolution := by
  sorry

end

end Erdos777
