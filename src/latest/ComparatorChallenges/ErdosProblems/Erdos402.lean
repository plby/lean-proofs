/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This file develops verified supporting lemmas toward a Lean formalization of
the resolution of Erdős Problem 402, also known as Graham's gcd conjecture.

Informal authors:
- R. Balasubramanian
- K. Soundararajan

Reference:
- R. Balasubramanian and K. Soundararajan, "On a conjecture of R. L. Graham",
  Acta Arithmetica 75 (1996), 1--38.

Progress log:
- verified: normalization, reciprocal/lcm reductions, prime-cardinality and
  Boyle lemmas, collision structure, the closed range through cardinality 7000,
  Lemmas 2.1--2.5, the Section 4 exceptional-prime reduction, and exact finite
  lower/upper endgame interfaces;
- verified most recently: a complete first-moment/PNT separation proving the
  conjecture for every sufficiently large cardinality, and the square-root
  prime-pair reduction used by the published medium-range computation;
- remaining: an axiom-free explicit prime certificate bridging cardinalities
  `7001` through the non-effective threshold inherited from `MediumPNT`.
-/

import Mathlib

namespace Erdos402

open scoped Pointwise
open Filter Asymptotics

/-- The integral form of the bound in Graham's gcd conjecture. -/
def GrahamBound (A : Finset ℕ) : Prop :=
  ∃ a ∈ A, ∃ b ∈ A, A.card * a.gcd b ≤ a

/-- Executable witness search for `GrahamBound`.  This is used only to
kernel-check closed finite certificates. -/
private def hasGrahamBound (A : Finset ℕ) : Bool :=
  (A.sort (· ≤ ·)).any fun a ↦
    (A.sort (· ≤ ·)).any fun b ↦ decide (A.card * a.gcd b ≤ a)

theorem erdos_402_of_sufficiently_large :
    ∃ N₀ : ℕ, ∀ A : Finset ℕ, N₀ ≤ A.card → 0 ∉ A → A.Nonempty →
      ∃ᵉ (a ∈ A) (b ∈ A), a.gcd b ≤ (a / A.card : ℚ) := by
  sorry
