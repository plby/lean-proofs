import Mathlib

/-!
# Erdős Problem 697

For `m : ℕ` and `α : ℝ`, let `divisorSet m α` be the natural numbers
divisible by a `d ≡ 1 (mod m)` with `1 < d < exp (m ^ α)`. Hall's sharp
transition for the density of this set occurs at `1 / log 2`.

The hypotheses in the two limit declarations in the upstream
`formal-conjectures` file are reversed. The corrected directions below
agree with its prose and with Hall's theorem: the limit is zero below the
critical exponent and one above it.
-/

open Filter Set Real
open scoped Topology

namespace Set

@[inline]
noncomputable abbrev partialDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) (b : β) : ℝ :=
  ((S ∩ A) ∩ Iio b).ncard / (A ∩ Iio b).ncard

end Set

namespace Erdos697

/-- The set whose density is denoted by `δ(m, α)`. -/
def divisorSet (m : ℕ) (α : ℝ) : Set ℕ :=
  {n : ℕ | ∃ d, d ≡ 1 [MOD m] ∧
    (d : ℝ) ∈ Set.Ioo 1 (Real.exp (m ^ α)) ∧ d ∣ n}

/-- The natural density of `divisorSet m α`. -/
noncomputable def δ (m : ℕ) (α : ℝ) : ℝ :=
  atTop.limUnder fun n : ℕ => (divisorSet m α).partialDensity Set.univ n

theorem erdos_697 :
    ∃ β : ℝ, 1 < β ∧
      (∀ α : ℝ, α < β → Tendsto (fun m : ℕ => δ m α) atTop (𝓝 0)) ∧
      (∀ α : ℝ, β < α → Tendsto (fun m : ℕ => δ m α) atTop (𝓝 1)) := by
  sorry

end Erdos697
