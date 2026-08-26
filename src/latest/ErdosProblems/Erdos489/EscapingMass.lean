import Mathlib

/- Ported from Lean 4.31.0 to 4.33.0; imports and elaboration options adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos489

open Filter
open scoped Topology BigOperators

/-- A triangular array whose mass escapes to indices growing with `x`. -/
noncomputable def escapingMass (h x : ℕ) : ℝ :=
  if h < x + 1 then 1 / ((x : ℝ) + 1) else 0

/-- Every fixed coordinate of `escapingMass` tends to zero. -/
theorem escapingMass_tendsto_fixed (h : ℕ) :
    Tendsto (escapingMass h) atTop (𝓝 0) := by
  apply (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).congr'
  filter_upwards [eventually_ge_atTop h] with x hx
  rw [escapingMass, if_pos (by omega)]

/-- Every row is nonincreasing in the tail index. -/
theorem escapingMass_antitone (x : ℕ) : Antitone (fun h => escapingMass h x) := by
  intro h k hhk
  by_cases hh : h < x + 1 <;> by_cases hk : k < x + 1
  · simp [escapingMass, hh, hk]
  · simp [escapingMass, hh, hk]
    positivity
  · omega
  · simp [escapingMass, hh, hk]

/-- Despite fixed-coordinate convergence to zero, every row has total mass one. -/
theorem tsum_escapingMass (x : ℕ) : ∑' h : ℕ, escapingMass h x = 1 := by
  rw [tsum_eq_sum (s := Finset.range (x + 1))]
  · calc
      (∑ h ∈ Finset.range (x + 1), escapingMass h x) =
          ∑ _h ∈ Finset.range (x + 1), (1 / ((x : ℝ) + 1) : ℝ) := by
            apply Finset.sum_congr rfl
            intro h hh
            rw [escapingMass, if_pos (Finset.mem_range.mp hh)]
      _ = ((x + 1 : ℕ) : ℝ) * (1 / ((x : ℝ) + 1)) := by simp
      _ = 1 := by
        rw [Nat.cast_add, Nat.cast_one]
        field_simp
  · intro h hh
    simp only [Finset.mem_range, not_lt] at hh
    rw [escapingMass, if_neg (by omega)]

/-- Thus pointwise limits cannot in general be interchanged with the infinite
sum, even for nonnegative, rowwise decreasing, finitely supported arrays. -/
theorem escapingMass_blocks_limit_sum_interchange :
    (∀ h : ℕ, Tendsto (escapingMass h) atTop (𝓝 0)) ∧
    (∀ x : ℕ, Antitone (fun h => escapingMass h x)) ∧
    (∀ x : ℕ, ∑' h : ℕ, escapingMass h x = 1) := by
  exact ⟨escapingMass_tendsto_fixed, escapingMass_antitone, tsum_escapingMass⟩

end Erdos489
