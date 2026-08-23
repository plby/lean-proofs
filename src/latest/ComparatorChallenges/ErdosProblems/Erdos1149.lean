/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter
open scoped Topology

noncomputable section


namespace Erdos1149

open scoped Classical in
def coprimePowerFloorSet (α : ℝ) : Set ℕ :=
  {n : ℕ | 1 ≤ n ∧ Nat.Coprime n ⌊Real.rpow (n : ℝ) α⌋₊}

end Erdos1149

namespace Set

open scoped Classical in
noncomputable abbrev partialDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) (b : β) : ℝ :=
  ((S ∩ A) ∩ Iio b).ncard / (A ∩ Iio b).ncard

end Set

namespace Set

open scoped Classical in
def HasDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (α : ℝ) (A : Set β := Set.univ) : Prop :=
  Tendsto (fun (b : β) => S.partialDensity A b) atTop (𝓝 α)

end Set

namespace Erdos1149

open scoped Classical in
theorem erdos_1149 (α : ℝ) (hα_pos : 0 < α)
    (hα_nonint : α ∉ Set.range ((↑) : ℤ → ℝ)) :
    (coprimePowerFloorSet α).HasDensity (6 / Real.pi ^ 2) := by
  sorry

end Erdos1149

end
