import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Nth
import Mathlib.Order.Filter.Defs
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Std.Tactic.BVDecide.LRAT.Internal.Clause

open Nat Finset Real Filter

axiom maynardTaoBFT :
  ∀ m : ℕ, 0 < m → ∃ C : ℕ, 0 < C ∧ ∀ q : ℕ, 0 < q → ∀ a : ℤ,
    Int.gcd a (q : ℤ) = 1 →
    ∀ N : ℕ, ∃ r : ℕ, N ≤ r ∧
      (∀ j, j < m → (Nat.nth Nat.Prime (r + j) : ℤ) ≡ a [ZMOD (q : ℤ)]) ∧
      Nat.nth Nat.Prime (r + m - 1) - Nat.nth Nat.Prime r ≤ q * C
namespace BinQuadForm

end BinQuadForm

open Finset Int Nat Real

namespace Erdos997

noncomputable abbrev nthPrime (n : ℕ) : ℕ := nth Nat.Prime n

noncomputable def fracSeq (α : ℝ) (n : ℕ) : ℝ := fract (α * (nthPrime n : ℝ))

noncomputable def countInIcc (x : ℕ → ℝ) (a b : ℝ) (n k : ℕ) : ℕ :=
  ((Ioc n (n + k)).filter fun i ↦ a ≤ x i ∧ x i ≤ b).card

def IsWellDistributed (x : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ∀ n : ℕ,
    ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
      |((countInIcc x a b n k) : ℝ) - (b - a) * (k : ℝ)| < ε * (k : ℝ)
end Erdos997

attribute [local instance] Classical.propDecidable

theorem Erdos997.erdos997 :
    ∀ (α : Real), Not (Erdos997.IsWellDistributed (Erdos997.fracSeq α))
  := by
  sorry
