import Mathlib

open Filter
open scoped BigOperators Topology

namespace Set

noncomputable abbrev partialDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) (b : β) : ℝ :=
  ((S ∩ A) ∩ Iio b).ncard / (A ∩ Iio b).ncard

def HasDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (α : ℝ) (A : Set β := Set.univ) : Prop :=
  Tendsto (fun (b : β) => S.partialDensity A b) atTop (𝓝 α)

end Set

namespace Erdos421

theorem erdos_421 :
    ∃ d : ℕ → ℕ, StrictMono d ∧ 1 ≤ d 0 ∧ (Set.range d).HasDensity 1 ∧
      {uv : ℕ × ℕ | uv.1 ≤ uv.2}.InjOn
        (fun uv ↦ ∏ i ∈ Finset.Icc uv.1 uv.2, d i) := by
  sorry

end Erdos421
