import Mathlib

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

lemma integer_open_half_interval_label
    (A : ℝ) (m : ℕ) (hm : 0 < m) (n : ℤ)
    (hlow : A < (n : ℝ))
    (hupp : (n : ℝ) < A + (m : ℝ) / 2) :
    ∃ q : ℕ, 2 * q < m ∧
      n = (Int.floor A + 1) + (q : ℤ) := by
  let a : ℤ := Int.floor A + 1
  have hfa : (Int.floor A : ℝ) ≤ A := Int.floor_le A
  have haf : A < (a : ℝ) := by
    simpa [a] using Int.lt_floor_add_one A
  have hfloorN : Int.floor A < n := (Int.floor_lt).2 hlow
  have han : a ≤ n := by
    dsimp [a]
    omega
  let q : ℕ := (n - a).toNat
  have hqInt : (q : ℤ) = n - a := by
    dsimp [q]
    exact Int.toNat_of_nonneg (sub_nonneg.mpr han)
  have hqR : (q : ℝ) < (m : ℝ) / 2 := by
    have hqCast : (q : ℝ) = (n : ℝ) - (a : ℝ) := by
      exact_mod_cast hqInt
    rw [hqCast]
    nlinarith
  have htwoR : ((2 * q : ℕ) : ℝ) < (m : ℝ) := by
    push_cast
    nlinarith
  have htwo : 2 * q < m := by exact_mod_cast htwoR
  refine ⟨q, htwo, ?_⟩
  rw [hqInt]
  dsimp [a]
  omega

end Erdos336
