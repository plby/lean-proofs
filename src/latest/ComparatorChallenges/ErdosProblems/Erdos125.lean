/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter

open scoped Topology

namespace Set

@[inline]
noncomputable abbrev partialDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) (b : β) : ℝ :=
  ((S ∩ A) ∩ Iio b).ncard / (A ∩ Iio b).ncard

noncomputable def lowerDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) : ℝ :=
  atTop.liminf fun (b : β) ↦ S.partialDensity A b

def HasDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (α : ℝ) (A : Set β := Set.univ) : Prop :=
  Tendsto (fun (b : β) => S.partialDensity A b) atTop (𝓝 α)

def HasPosDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) : Prop :=
  ∃ α > 0, S.HasDensity α A
namespace HasDensity

end HasDensity

end Set

open scoped Pointwise



open Filter
open scoped Topology
open Nat Pointwise
open Topology

namespace Erdos125

open scoped Classical in
theorem erdos_125 :
    ¬ ({ x : ℕ | (Nat.digits 3 x).toFinset ⊆ {0, 1} } +
      { x : ℕ | (Nat.digits 4 x).toFinset ⊆ {0, 1} }).HasPosDensity := by
  sorry

end Erdos125
namespace Erdos125.erdos_125.variants

open scoped Classical in
theorem positive_lower_density :
    ¬ 0 < ({ x : ℕ | (Nat.digits 3 x).toFinset ⊆ {0, 1} } +
      { x : ℕ | (Nat.digits 4 x).toFinset ⊆ {0, 1} }).lowerDensity := by
  sorry

end Erdos125.erdos_125.variants
