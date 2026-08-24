/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos777

/-- The comparability graph of a finite family of finite sets.  Vertices are
members of the family, and adjacency is strict containment in either
direction. -/
def comparableGraph {α : Type*} [DecidableEq α]
    (𝓕 : Finset (Finset α)) : SimpleGraph {A // A ∈ 𝓕} where
  Adj A B := A.1 < B.1 ∨ B.1 < A.1
  symm := ⟨by intro A B; tauto⟩
  loopless := ⟨by intro A h; exact (lt_irrefl A.1) (h.elim id id)⟩

noncomputable instance comparableGraph_instDecidableRel {α : Type*} [DecidableEq α]
    (𝓕 : Finset (Finset α)) : DecidableRel (comparableGraph 𝓕).Adj :=
  fun _ _ ↦ Classical.propDecidable _

/-- The number of unordered strict comparable pairs in `𝓕`. -/
noncomputable def comparableEdges {α : Type*} [Fintype α] [DecidableEq α]
    (𝓕 : Finset (Finset α)) : ℕ :=
  (comparableGraph 𝓕).edgeFinset.card

theorem erdos_777 :
    (∀ ε : ℝ, 0 < ε →
      ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ 𝓕 : Finset (Finset (Fin n)),
        (𝓕.card : ℝ) ≤ (2 - ε) * (2 : ℝ) ^ ((n : ℝ) / 2) →
        Erdos777.comparableEdges 𝓕 < 2 ^ n) ∧ ¬ (∀ c : ℝ, 0 < c →
      ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ 𝓕 : Finset (Finset (Fin n)),
        c * (𝓕.card : ℝ) ^ 2 ≤ Erdos777.comparableEdges 𝓕 →
        (𝓕.card : ℝ) ≤ C * (2 : ℝ) ^ ((n : ℝ) / 2)) ∧ (∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧ ∀ n : ℕ, ∀ 𝓕 : Finset (Finset (Fin n)),
        (𝓕.card : ℝ) ^ (2 - δ) < Erdos777.comparableEdges 𝓕 →
        (𝓕.card : ℝ) < (2 + ε) ^ ((n : ℝ) / 2)) := by
  sorry

end Erdos777
