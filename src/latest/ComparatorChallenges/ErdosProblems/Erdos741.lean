/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter

namespace Set

@[inline]
noncomputable abbrev partialDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) (b : β) : ℝ :=
  ((S ∩ A) ∩ Iio b).ncard / (A ∩ Iio b).ncard

noncomputable def upperDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) : ℝ :=
  atTop.limsup fun (b : β) ↦ S.partialDensity A b
namespace HasDensity

end HasDensity

end Set



open Filter
open scoped Topology
open scoped Pointwise
open Set

namespace Erdos741.erdos_741.variants

open scoped Classical in
theorem upper : (True) ↔ ∀ A :
    Set ℕ, 0 < upperDensity (A + A) → ∃ A₁ A₂,
    A = A₁ ∪ A₂ ∧ Disjoint A₁ A₂ ∧ 0 < upperDensity (A₁ + A₁)
    ∧ 0 < upperDensity (A₂ + A₂) := by
  sorry

end Erdos741.erdos_741.variants
