import Mathlib

open Nat Finset Real Filter Topology
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

open Nat Finset Filter
open scoped BigOperators Topology

namespace Erdos258

theorem erdos_258 (a : ℕ → ℕ) (ha : ∀ n, 0 < a (n + 1))
    (ha_tendsto : Tendsto a atTop atTop) :
    Irrational (erdosSeries a) := by
  sorry

end Erdos258
