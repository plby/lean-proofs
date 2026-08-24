/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter

namespace Erdos862

def Sidon {α : Type} [AddCommMonoid α] (S : Set α) : Prop :=
  ∀ a b c d, a ∈ S → b ∈ S → c ∈ S → d ∈ S → a + b = c + d → ({a, b} : Set α) = {c, d}

end Erdos862

namespace Erdos861

open scoped Classical in
noncomputable def sidonFamily (N : ℕ) : Finset (Finset ℕ) :=
  (Finset.Icc 1 N).powerset.filter
    (fun S : Finset ℕ => Erdos862.Sidon (S : Set ℕ))

noncomputable def A (N : ℕ) : ℕ :=
  (sidonFamily N).card

noncomputable def f (N : ℕ) : ℕ :=
  (sidonFamily N).sup Finset.card

noncomputable def normalizedRatio (N : ℕ) : ℝ :=
  (A N : ℝ) / (2 : ℝ) ^ f N

theorem erdos_861 :
    Tendsto normalizedRatio atTop atTop ∧
          ¬ (Filter.Tendsto
      (fun N : ℕ =>
        Real.log (Erdos861.A N : ℝ) / ((Erdos861.f N : ℝ) * Real.log 2))
      Filter.atTop (nhds 1)) := by
  sorry

end Erdos861
