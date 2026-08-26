/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib

open Filter

namespace Set

noncomputable abbrev partialDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) (b : β) : ℝ :=
  ((S ∩ A) ∩ Iio b).ncard / (A ∩ Iio b).ncard

noncomputable def lowerDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) : ℝ :=
  atTop.liminf fun (b : β) ↦ S.partialDensity A b

end Set

namespace Erdos822

/-- The values of `n + φ(n)` have positive lower asymptotic density. -/
theorem erdos_822 :
    True ↔ 0 < (Set.range fun n : ℕ ↦ n + Nat.totient n).lowerDensity := by
  sorry

end Erdos822
