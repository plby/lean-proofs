import Mathlib

open Filter Finset Real Topology
open scoped BigOperators Topology

noncomputable section


namespace Erdos262

open scoped Classical in
def seriesTerm (a t : ℕ → ℕ) (n : ℕ) : ℝ :=
  1 / ((t n : ℝ) * (a n : ℝ))

end Erdos262

namespace Erdos262

open scoped Classical in
def IrrationalitySequence (a : ℕ → ℕ) : Prop :=
  (∀ n, 0 < a n) ∧ StrictMono a ∧
    ∀ t : ℕ → ℕ, (∀ n, 0 < t n) → Irrational (∑' n, seriesTerm a t n)

end Erdos262

namespace Erdos262

open scoped Classical in
def greedyDenom (a : ℕ) (r : ℝ) : ℕ :=
  ⌊1 / ((a : ℝ) * r)⌋₊ + 1

open scoped Classical in
def remainder (a : ℕ → ℕ) (M : ℕ) : ℕ → ℝ
  | 0 => (1 / 2 : ℝ) ^ M
  | n + 1 => remainder a M n -
      1 / ((a n : ℝ) * greedyDenom (a n) (remainder a M n))

open scoped Classical in
def doubleLogRatio (a : ℕ → ℕ) (n : ℕ) : ℝ :=
  Real.logb 2 (Real.logb 2 (a n : ℝ)) / ((n + 1 : ℕ) : ℝ)

end Erdos262

namespace Erdos262

open scoped Classical in
theorem erdos_262 (a : ℕ → ℕ) (h : IrrationalitySequence a) :
    (1 : EReal) ≤ limsup (fun n ↦ (doubleLogRatio a n : EReal)) atTop := by
  sorry

end Erdos262

end
