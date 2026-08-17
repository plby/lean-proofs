import Mathlib

open Nat Finset Real Filter
def Theorem_2_2 : Prop :=
  ∀ ε : ℝ, ε > 0 → ∃ n₀ : ℕ,
    ∀ (V : Finset ℕ) (E : Finset (Finset ℕ)),
    V.card ≥ n₀ →
    (∀ e ∈ E, e.card = 3 ∧ e ⊆ V) →
    (∀ e ∈ E, ∃! K, K ⊆ V ∧ K.card ≥ 4 ∧
      (∀ t ⊆ K, t.card = 3 → t ∈ E) ∧ e ⊆ K) →
    (E.card : ℝ) < ε * (V.card : ℝ) ^ 3

axiom frankl_roedl_theorem : Theorem_2_2

namespace Erdos658

section
open Finset

def gridRange (N : ℕ) : Finset ℤ :=
  (Finset.range N).image (↑· : ℕ → ℤ)

def grid2 (N : ℕ) : Finset (ℤ × ℤ) :=
  gridRange N ×ˢ gridRange N

def grid3 (N : ℕ) : Finset (ℤ × ℤ × ℤ) :=
  gridRange N ×ˢ (gridRange N ×ˢ gridRange N)

def ContainsSquare (S : Finset (ℤ × ℤ)) : Prop :=
  ∃ a b d : ℤ, d ≠ 0 ∧
    (a, b) ∈ S ∧ (a + d, b) ∈ S ∧
    (a, b + d) ∈ S ∧ (a + d, b + d) ∈ S

def ContainsQuadruple (S : Finset (ℤ × ℤ × ℤ)) : Prop :=
  ∃ a b c d : ℤ, d ≠ 0 ∧
    (a, b, c) ∈ S ∧ (a + d, b, c) ∈ S ∧
    (a, b + d, c) ∈ S ∧ (a + d, b + d, c + d) ∈ S
end

end Erdos658

attribute [local instance] Classical.propDecidable

open Finset

namespace Erdos658

theorem Theorem_1_2 (hFR : Theorem_2_2) :
    ∀ δ : ℝ, δ > 0 → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ < N →
      ∀ S : Finset (ℤ × ℤ × ℤ), S ⊆ grid3 N →
        δ * (↑N) ^ 3 ≤ ↑S.card →
        ContainsQuadruple S := by
  sorry


theorem Theorem_1_1 (hFR : Theorem_2_2) :
    ∀ δ : ℝ, δ > 0 → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ < N →
      ∀ S : Finset (ℤ × ℤ), S ⊆ grid2 N →
        δ * (↑N) ^ 2 ≤ ↑S.card → ContainsSquare S := by
  sorry


theorem erdos658 :
    ∀ δ : ℝ, δ > 0 → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ < N →
      ∀ S : Finset (ℤ × ℤ), S ⊆ grid2 N →
        δ * (↑N) ^ 2 ≤ ↑S.card → ContainsSquare S := by
  sorry

end Erdos658
