/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open scoped BigOperators

noncomputable section

namespace Erdos441

open scoped Classical in
def LcmBounded (N : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ Finset.Icc 1 N ∧
    ∀ a ∈ A, ∀ b ∈ A, Nat.lcm a b ≤ N

open scoped Classical in
instance (N : ℕ) (A : Finset ℕ) : Decidable (LcmBounded N A) := by
  unfold LcmBounded
  infer_instance

end Erdos441

namespace Erdos441

open scoped Classical in
def erdosConstruction (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter fun a ↦
    2 * a ^ 2 ≤ N ∨ (2 ∣ a ∧ a ^ 2 ≤ 2 * N)

end Erdos441

namespace Erdos441

open scoped Classical in
def candidates (N : ℕ) : Finset (Finset ℕ) :=
  (Finset.Icc 1 N).powerset.filter (LcmBounded N)

end Erdos441

namespace Erdos441

open scoped Classical in
def g (N : ℕ) : ℕ :=
  (candidates N).sup Finset.card

end Erdos441

namespace Erdos441

open scoped Classical in
theorem erdos_441 :
    (∀ N : ℕ, LcmBounded N (erdosConstruction N)) ∧
      ∀ M : ℕ, ∃ N ≥ M,
        (erdosConstruction N).card < g N := by
  sorry

end Erdos441

end
