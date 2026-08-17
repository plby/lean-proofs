import Mathlib

open Filter
open scoped Topology

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

namespace Set

noncomputable abbrev partialDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) (b : β) : ℝ :=
  ((S ∩ A) ∩ Iio b).ncard / (A ∩ Iio b).ncard

end Set

namespace Set

def HasDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (α : ℝ) (A : Set β := Set.univ) : Prop :=
  Tendsto (fun (b : β) => S.partialDensity A b) atTop (𝓝 α)

end Set

namespace Erdos144

def closeDivisorSet : Set ℕ :=
  {n : ℕ | ∃ d₁ d₂ : ℕ,
    d₁ ∣ n ∧ d₂ ∣ n ∧ d₁ < d₂ ∧ d₂ < 2 * d₁}

theorem erdos_144 : closeDivisorSet.HasDensity 1 := by
  sorry

end Erdos144

end
