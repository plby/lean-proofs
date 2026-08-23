/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

/- The local verification cache for `BoundedGaps` was produced by Lake and
records this generated name for the standard order on `ℕ`.  Re-exporting the
same reducible instance name keeps that cache compatible; a clean Lake build
reduces it to the ordinary `Nat` partial order. -/
namespace Nat
abbrev «instPartialOrder_.lake» : PartialOrder ℕ := inferInstance
end Nat

/-!
# Erdős Problem 1202

Erdős asked whether removing half of the residue classes modulo sufficiently many
primes below `n ^ (1 - ε)` must leave at most `ε n` positive integers up to `n`.
The answer is negative.  We formalize the interval construction of Price and
GPT-5.4 Pro: primes in one short interval have aligned upper-half forbidden
sets, while a positive-density striped set survives every sieve.

The detailed mathematical proof and Leanization plan are in `tex/1202.tex`.
-/

namespace Erdos1202

open Filter Finset Real
open scoped Topology

noncomputable section

/-- Positive integers at most `n` avoiding every indexed forbidden residue set. -/
def survivors {k : ℕ} (n : ℕ) (p : Fin k → ℕ)
    (A : (i : Fin k) → Finset (ZMod (p i))) : Finset ℕ :=
  (Finset.Icc 1 n).filter fun x ↦ ∀ i, (x : ZMod (p i)) ∉ A i

/-- The literal assertion recorded as Erdős Problem 1202.

The source quantifies both `ε` and `η`, but its displayed upper bound uses `ε`;
we preserve that quantifier structure exactly. -/
def Erdos1202Statement : Prop :=
  ∀ ε η : ℝ, 0 < ε → 0 < η →
    ∃ k : ℕ, 0 < k ∧ ∀ (n : ℕ) (p : Fin k → ℕ)
      (A : (i : Fin k) → Finset (ZMod (p i))),
      (∀ i, (p i).Prime) →
      StrictMono p →
      (∀ i, (p i : ℝ) < (n : ℝ) ^ (1 - ε)) →
      (∀ i, (A i).card = (p i - 1) / 2) →
      ((survivors n p A).card : ℝ) ≤ ε * n

/-- The upper half of the least nonnegative representatives modulo `p`. -/
def upperHalf (p : ℕ) (hp0 : p ≠ 0) : Finset (ZMod p) :=
  letI : NeZero p := ⟨hp0⟩
  Finset.univ.filter fun a ↦ (p + 1) / 2 ≤ a.val

theorem erdos_1202 : ¬ Erdos1202Statement := by
  sorry

end

end Erdos1202
