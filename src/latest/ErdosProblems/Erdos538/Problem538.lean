import Mathlib

/- Ported from Lean 4.31.0 to 4.33.0; imports, namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Erdős Problem 538: pinned finite formulation

This file fixes the exact finite objects in the problem.  A proposed *exact*
answer is a function `B : ℕ → ℕ → ℚ` together with a proof of
`SolvesExactly B`.  We keep the extremal predicate separate because the phrase
"best possible upper bound" is sometimes used only up to asymptotic order.
Any asymptotic final theorem must still use `Admissible` and `reciprocalMass`
below and must contain both an upper bound and matching admissible witnesses.
-/

namespace Erdos538

/-- All solution pairs `(p,a)` of `m = p*a` with `p` prime and `a ∈ A`.
The range `m+1` is exhaustive: a prime in such a solution is at most `m`,
because members of an admissible `A` are positive. -/
def representations (A : Finset ℕ) (m : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (m + 1)).product A).filter
    (fun pa => Nat.Prime pa.1 ∧ m = pa.1 * pa.2)

/-- The hypotheses in Problem 538, including `A ⊆ {1,...,N}`. -/
def Admissible (r N : ℕ) (A : Finset ℕ) : Prop :=
  (∀ a ∈ A, 1 ≤ a ∧ a ≤ N) ∧
  ∀ m : ℕ, (representations A m).card ≤ r

/-- The reciprocal sum in Problem 538, represented exactly in `ℚ`. -/
def reciprocalMass (A : Finset ℕ) : ℚ :=
  ∑ a ∈ A, (1 : ℚ) / a

/-- `B` is the pointwise best upper bound for the fixed parameters `r,N`.
The second conjunct is sharpness.  Since there are finitely many subsets of
`{1,...,N}`, the supremum is attained, so equality is the faithful finite
notion of "best possible". -/
def IsExactBestBoundAt (r N : ℕ) (B : ℚ) : Prop :=
  (∀ A : Finset ℕ, Admissible r N A → reciprocalMass A ≤ B) ∧
  ∃ A : Finset ℕ, Admissible r N A ∧ reciprocalMass A = B

/-- The exact-answer interface for Erdős Problem 538. -/
def SolvesExactly (B : ℕ → ℕ → ℚ) : Prop :=
  ∀ r : ℕ, 2 ≤ r → ∀ N : ℕ, IsExactBestBoundAt r N (B r N)

end Erdos538
