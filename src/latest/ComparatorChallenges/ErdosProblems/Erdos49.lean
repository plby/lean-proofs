/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter

namespace Erdos49

def TotientStrictOn (A : Finset ℕ) : Prop :=
  ∀ ⦃m⦄, m ∈ A → ∀ ⦃n⦄, n ∈ A → m < n →
    Nat.totient m < Nat.totient n

open scoped Classical in
noncomputable def strictFamilies (N : ℕ) : Finset (Finset ℕ) :=
  (Finset.Icc 1 N).powerset.filter (TotientStrictOn ·)

noncomputable def strictMaximum (N : ℕ) : ℕ :=
  (strictFamilies N).sup Finset.card

theorem erdos_49 :
    (fun N : ℕ ↦ (strictMaximum N : ℝ)) =o[atTop]
      (fun N : ℕ ↦ (N : ℝ)) := by
  sorry

end Erdos49
