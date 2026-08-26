-- Modified for this repository: Lean 4.33.0 port and Erdos1177 namespace.
import Mathlib

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The cardinal `δ(ρ)` (§6.3)

For an infinite cardinal `ρ`, `δ(ρ) = min{δ : ρ^δ > ρ}`.  With `ρ = 2^μ` and
`κ = μ⁺` we record the calibration's key fact `κ ≤ δ(ρ)`, which is what powers
the reduction of the Erdős–Galvin–Hajnal property `P(S,I,δ(ρ))` down to
`P(S,I,κ)` via monotonicity.
-/

open Cardinal

namespace Erdos1177

/-- `δ(ρ) = min{δ : ρ < ρ^δ}`. -/
noncomputable def deltaRho (ρ : Cardinal) : Cardinal := sInf {δ | ρ < ρ ^ δ}

/-- For `1 ≤ θ ≤ μ` with `μ` infinite, `(2^μ)^θ = 2^μ`. -/
theorem pow_pow_eq_of_le {μ θ : Cardinal} (hμ : ℵ₀ ≤ μ) (h1 : θ ≠ 0) (hθ : θ ≤ μ) :
    ((2 : Cardinal) ^ μ) ^ θ = (2 : Cardinal) ^ μ := by
  rw [← Cardinal.power_mul, Cardinal.mul_eq_left hμ hθ h1]

/-- The defining set of `δ(ρ)` is nonempty for infinite `ρ` (since `ρ < ρ^ρ`). -/
theorem deltaRho_mem {ρ : Cardinal} (hρ : ℵ₀ ≤ ρ) : ρ ∈ {δ | ρ < ρ ^ δ} := by
  show ρ < ρ ^ ρ
  calc ρ < 2 ^ ρ := Cardinal.cantor ρ
    _ ≤ ρ ^ ρ := Cardinal.power_le_power_right (le_trans (by norm_num) hρ)

/-- **Key calibration fact** (`lem:cardinal-facts` companion, §6.3):
for infinite `μ`, `μ⁺ ≤ δ(2^μ)`.  Hence, with `κ = μ⁺` and `ρ = 2^μ`,
`κ ≤ δ(ρ)`. -/
theorem succ_le_deltaRho {μ : Cardinal} (hμ : ℵ₀ ≤ μ) :
    Order.succ μ ≤ deltaRho ((2 : Cardinal) ^ μ) := by
  set ρ := (2 : Cardinal) ^ μ with hρdef
  have hρ : ℵ₀ ≤ ρ := le_of_lt (lt_of_le_of_lt hμ (Cardinal.cantor μ))
  show Order.succ μ ≤ sInf {δ | ρ < ρ ^ δ}
  apply le_csInf ⟨ρ, deltaRho_mem hρ⟩
  intro θ hθ
  by_contra h
  push_neg at h
  rw [Order.lt_succ_iff] at h
  have hle : ρ ^ θ ≤ ρ := by
    rcases eq_or_ne θ 0 with rfl | h1
    · simpa using! one_le_aleph0.trans hρ
    · rw [hρdef, pow_pow_eq_of_le hμ h1 h]
  exact absurd hθ (not_lt.mpr hle)

end Erdos1177
