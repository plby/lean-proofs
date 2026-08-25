/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter Asymptotics

namespace Erdos381

def tau (n : ℕ) : ℕ := n.divisors.card

def HighlyComposite (n : ℕ) : Prop :=
  0 < n ∧ ∀ m : ℕ, 0 < m → m < n → tau m < tau n

noncomputable instance highlyCompositeDecidable (n : ℕ) : Decidable (HighlyComposite n) :=
  Classical.dec _

noncomputable def Q (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).filter HighlyComposite).card

theorem not_erdos_381 :
    ¬ ∀ k : ℕ, 1 ≤ k →
      (fun n : ℕ => Real.log (n : ℝ) ^ k) =O[atTop]
        (fun n : ℕ => (Q n : ℝ)) := by
  sorry

end Erdos381
