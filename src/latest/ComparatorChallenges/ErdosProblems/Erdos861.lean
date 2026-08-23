/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter
open scoped Topology

noncomputable section


namespace Erdos862

open scoped Classical in
def Sidon {α : Type} [AddCommMonoid α] (S : Set α) : Prop :=
  ∀ a b c d, a ∈ S → b ∈ S → c ∈ S → d ∈ S → a + b = c + d → ({a, b} : Set α) = {c, d}

end Erdos862

namespace Erdos861

open scoped Classical in
noncomputable def sidonFamily (N : ℕ) : Finset (Finset ℕ) :=
  (Finset.Icc 1 N).powerset.filter
    (fun S : Finset ℕ => Erdos862.Sidon (S : Set ℕ))

end Erdos861

namespace Erdos861

open scoped Classical in
noncomputable def A (N : ℕ) : ℕ :=
  (sidonFamily N).card

end Erdos861

namespace Erdos861

open scoped Classical in
noncomputable def f (N : ℕ) : ℕ :=
  (sidonFamily N).sup Finset.card

end Erdos861

namespace Erdos861

open scoped Classical in
noncomputable def normalizedRatio (N : ℕ) : ℝ :=
  (A N : ℝ) / (2 : ℝ) ^ f N

end Erdos861

namespace Erdos861

open scoped Classical in
def UnitExponentAsymptotic : Prop :=
  Tendsto
    (fun N : ℕ =>
      Real.log (A N : ℝ) / ((f N : ℝ) * Real.log 2))
    atTop (nhds 1)

end Erdos861

namespace Erdos861

open scoped Classical in
theorem erdos861 :
    Tendsto normalizedRatio atTop atTop ∧
      ¬ UnitExponentAsymptotic := by
  sorry

end Erdos861

end
