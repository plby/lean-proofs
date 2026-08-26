import Mathlib

namespace Erdos856b

open Real Filter
open scoped BigOperators Topology

def LcmFree (k : ℕ) (A : Finset ℕ) : Prop :=
  ∀ a : Fin k → ℕ, Function.Injective a → (∀ i, a i ∈ A) →
    ¬ ∃ m : ℕ, ∀ i j, i ≠ j → Nat.lcm (a i) (a j) = m

noncomputable def reciprocalWeight (A : Finset ℕ) : NNReal :=
  ∑ a ∈ A, (a : NNReal)⁻¹

noncomputable def admissibleSets (k N : ℕ) : Finset (Finset ℕ) := by
  classical
  exact (Finset.Icc 1 N).powerset.filter (LcmFree k)

noncomputable def f (k N : ℕ) : ℝ :=
  ((admissibleSets k N).sup reciprocalWeight : NNReal)

def UnionFree {α : Type*} [DecidableEq α] (k : ℕ) (F : Finset (Finset α)) : Prop :=
  ∀ a : Fin k → Finset α, Function.Injective a → (∀ i, a i ∈ F) →
    ¬ ∃ u : Finset α, ∀ i j, i ≠ j → a i ∪ a j = u

noncomputable def admissibleFamilies (k n r : ℕ) : Finset (Finset (Finset (Fin n))) := by
  classical
  exact (Finset.univ.powersetCard r).powerset.filter (UnionFree k)

noncomputable def M (k n r : ℕ) : ℕ :=
  (admissibleFamilies k n r).sup Finset.card

/-- The harmonic LCM-avoidance exponent equals the finite-block supremum. -/
theorem erdos_856 (k : ℕ) (hk : 3 ≤ k) :
    Tendsto (fun N : ℕ => log (f k N) / log (log (N : ℝ))) atTop
      (𝓝 (sSup {v : ℝ | ∃ n r : ℕ, 0 < n ∧ 0 < r ∧ r ≤ n ∧
        v = (r : ℝ) / (exp 1 * n) * (M k n r : ℝ) ^ (1 / (r : ℝ))})) := by
  sorry

end Erdos856b
