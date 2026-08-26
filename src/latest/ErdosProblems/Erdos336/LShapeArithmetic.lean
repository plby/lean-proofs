import Mathlib

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Sharp arithmetic optimization for two-dimensional L-shapes
-/

namespace Erdos336

/-- The standard L-shape optimization.  An outer `l × h` rectangle with a
`w × y` corner removed has area `n`.  If the two opposite boundary distances
are at most `H+2`, then `3n ≤ (H+2)²`. -/
theorem lShape_area_le_third
    {l h w y H n : ℕ}
    (hw : w ≤ l) (hy : y ≤ h)
    (hn : n + w * y = l * h)
    (hd₁ : l + h - w ≤ H + 2)
    (hd₂ : l + h - y ≤ H + 2) :
    3 * n ≤ (H + 2) ^ 2 := by
  let A := l - w
  let B := h - y
  let K := H + 2
  have hl : w + A = l := by
    dsimp [A]
    omega
  have hh : y + B = h := by
    dsimp [B]
    omega
  have hboundA : h + A ≤ K := by
    dsimp [K]
    omega
  have hboundB : l + B ≤ K := by
    dsimp [K]
    omega
  have hnform : n + A * B = l * B + h * A := by
    nlinarith
  have hmulA : h * A + A ^ 2 ≤ K * A := by
    simpa [pow_two, add_mul] using Nat.mul_le_mul_right A hboundA
  have hmulB : l * B + B ^ 2 ≤ K * B := by
    simpa [pow_two, add_mul] using Nat.mul_le_mul_right B hboundB
  have hmass : n + A * B + A ^ 2 + B ^ 2 ≤ K * (A + B) := by
    nlinarith
  have hpolyZ :
      3 * (K : ℤ) * ((A : ℤ) + B) ≤
        (K : ℤ) ^ 2 + 3 * ((A : ℤ) ^ 2 + A * B + (B : ℤ) ^ 2) := by
    nlinarith [sq_nonneg (2 * (K : ℤ) - 3 * A - 3 * B),
      sq_nonneg ((A : ℤ) - B)]
  have hpoly :
      3 * K * (A + B) ≤ K ^ 2 + 3 * (A ^ 2 + A * B + B ^ 2) := by
    exact_mod_cast hpolyZ
  have hthree :
      3 * n + 3 * (A * B + A ^ 2 + B ^ 2) ≤ 3 * K * (A + B) := by
    have := Nat.mul_le_mul_left 3 hmass
    nlinarith
  have hcancel :
      3 * n + 3 * (A * B + A ^ 2 + B ^ 2) ≤
        K ^ 2 + 3 * (A * B + A ^ 2 + B ^ 2) := by
    nlinarith
  have := Nat.le_of_add_le_add_right hcancel
  dsimp [K] at this ⊢
  simpa [add_comm, add_left_comm, add_assoc] using this

end Erdos336
