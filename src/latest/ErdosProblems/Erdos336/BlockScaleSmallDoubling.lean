import Mathlib
import ErdosProblems.Erdos336.DyadicSmallDoubling

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# An explicit sublinear dyadic scale
-/

namespace Erdos336

/-- Six dyadic doublings beat one block of size `128` at the `9/4`
threshold: `4^6 * 128 < 9^6`.  Consequently a block parameter `K`
with `h+1<128^K` produces small doubling before scale `64^K`. -/
theorem exists_small_doubling_before_block_scale
    {G : Type*} [AddCommGroup G] [Fintype G]
    {B : Set G} {b : G} {h K : ℕ}
    (hb : b ∈ B) (hweak : ∀ y : G, GroupRepAtMost B h y)
    (hK : 0 < K) (hh : h + 1 < 128 ^ K) :
    ∃ i : ℕ, i < 6 * K ∧ 2 ^ (i + 1) ≤ 64 ^ K ∧
      4 * (ExactPower (ShiftToZero B b) (2 ^ (i + 1) * h)).ncard <
        9 * (ExactPower (ShiftToZero B b) (2 ^ i * h)).ncard := by
  have hbase : 4 ^ 6 * 128 < 9 ^ 6 := by norm_num
  have hpow : (4 ^ 6 * 128) ^ K < (9 ^ 6) ^ K :=
    Nat.pow_lt_pow_left hbase (Nat.ne_of_gt hK)
  have hscale : 4 ^ (6 * K) * (h + 1) < 9 ^ (6 * K) := by
    calc
      4 ^ (6 * K) * (h + 1) < 4 ^ (6 * K) * 128 ^ K := by
        exact Nat.mul_lt_mul_of_pos_left hh (by positivity)
      _ = (4 ^ 6 * 128) ^ K := by rw [pow_mul, mul_pow]
      _ < (9 ^ 6) ^ K := hpow
      _ = 9 ^ (6 * K) := by rw [pow_mul]
  obtain ⟨i, hi, hdoub⟩ :=
    exists_dyadic_small_doubling_of_weakCover hb hweak hscale
  refine ⟨i, hi, ?_, hdoub⟩
  have hie : i + 1 ≤ 6 * K := by omega
  calc
    2 ^ (i + 1) ≤ 2 ^ (6 * K) := Nat.pow_le_pow_right (by omega) hie
    _ = 64 ^ K := by norm_num [pow_mul]

end Erdos336
