import Mathlib

open scoped BigOperators Topology
open Filter Set
open Polynomial

noncomputable section


namespace Erdos1114

open scoped Classical in
def RightGapMonotone (N : ℕ) (b : ℕ → ℝ) : Prop :=
  ∀ i : ℕ, i + 2 < N → N ≤ 2 * (i + 1) →
    b (i + 1) - b i ≤ b (i + 2) - b (i + 1)

end Erdos1114

namespace Erdos1114

open scoped Classical in
def GapSymmetric (N : ℕ) (b : ℕ → ℝ) : Prop :=
  ∀ i : ℕ, i + 1 < N →
    b (i + 1) - b i = b (N - 1 - i) - b (N - 2 - i)

end Erdos1114

namespace Erdos1114

open scoped Classical in
theorem erdos_1114 {N : ℕ} (hN : 0 < N) {a d : ℝ}
    (hd : 0 < d) {f : ℝ[X]} {b : ℕ → ℝ}
    (hf0 : f ≠ 0) (hdegree : f.natDegree = N + 1)
    (hroots : ∀ j, j ≤ N → eval (a + d * j) f = 0)
    (hb : ∀ k, k < N →
      b k ∈ Set.Ioo (a + d * k) (a + d * (k + 1)))
    (hderiv : ∀ k, k < N → eval (b k) f.derivative = 0) :
    RightGapMonotone N b ∧ GapSymmetric N b := by
  sorry

end Erdos1114

end
