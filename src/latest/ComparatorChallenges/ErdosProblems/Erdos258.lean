import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.Real.Irrational
import Std.Tactic.BVDecide.LRAT.Internal.Clause

open Nat Finset Real Filter Topology

axiom tao_teravainen : ∃ C : ℝ, 0 < C ∧
    (∃ᶠ N in atTop, ∀ k : ℕ, 0 < k →
      (N + k).factorization.support.card ≤
          (N + k).factorization.sum (fun _ k => k) ∧
        (N + k).factorization.sum (fun _ k => k) ≤ C * k)
namespace BinQuadForm

end BinQuadForm

namespace Erdos258

open Nat Finset Filter
open scoped BigOperators Topology

noncomputable section

def Q (a : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | n + 1 => Q a n * a (n + 1)

def erdosTerm (a : ℕ → ℕ) (n : ℕ) : ℝ :=
  ((n + 1).divisors.card : ℝ) / (Q a (n + 1) : ℝ)

def erdosSeries (a : ℕ → ℕ) : ℝ := ∑' n, erdosTerm a n
end

end Erdos258

attribute [local instance] Classical.propDecidable

theorem Erdos258.erdos_258 :
    ∀ (a : Nat → Nat),
      (∀ (n : Nat),
          @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (a
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) →
        @Filter.Tendsto.{0, 0} Nat Nat a (@Filter.atTop.{0} Nat Nat.instPreorder)
            (@Filter.atTop.{0} Nat Nat.instPreorder) →
          Irrational (Erdos258.erdosSeries a)
  := by
  sorry
