import Mathlib

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Short-arc rectification

An elementary lift lemma used in the finite-cyclic approach to Erdős problem
336.  If an orbit in `Z / mZ` stays in an arc shorter than one quarter of the
circle, its lifted consecutive increments cannot change by a multiple of `m`.
Thus the orbit lifts to an ordinary arithmetic progression.
-/

namespace Erdos336

lemma eq_of_dvd_sub_of_mem_short_interval
    {a b m W : ℤ} (hW : 0 ≤ W) (hm : 4 * W < m)
    (ha₁ : -2 * W ≤ a) (ha₂ : a ≤ 2 * W)
    (hb₁ : -2 * W ≤ b) (hb₂ : b ≤ 2 * W)
    (hdvd : m ∣ a - b) : a = b := by
  obtain ⟨q, hq⟩ := hdvd
  by_contra hab
  have hq0 : q ≠ 0 := by
    intro hzero
    subst q
    simp at hq
    exact hab (sub_eq_zero.mp hq)
  rcases lt_or_gt_of_ne hq0 with hqneg | hqpos
  · have hqm : m * q ≤ -m := by
      have hmpos : 0 < m := by omega
      nlinarith
    nlinarith
  · have hmq : m ≤ m * q := by
      have hmpos : 0 < m := by omega
      nlinarith
    nlinarith

/-- A sequence of short lifts whose consecutive increments are all congruent
modulo `m` is an honest arithmetic progression. -/
theorem short_arc_orbit_rectification
    {R : ℕ} {m W : ℤ} (y : ℕ → ℤ)
    (hW : 0 ≤ W) (hm : 4 * W < m)
    (hy : ∀ k, k ≤ R → -W ≤ y k ∧ y k ≤ W)
    (hcong : ∀ k, k < R →
      m ∣ (y (k + 1) - y k) - (y 1 - y 0)) :
    ∀ k, k ≤ R → y k = y 0 + (k : ℤ) * (y 1 - y 0) := by
  intro k hk
  induction k with
  | zero => simp
  | succ k ih =>
      have hkR : k < R := Nat.lt_of_succ_le hk
      have hk_le : k ≤ R := Nat.le_trans (Nat.le_succ k) hk
      have h1R : 1 ≤ R := Nat.le_trans (Nat.succ_le_succ (Nat.zero_le k)) hk
      have hyk := hy k hk_le
      have hyks := hy (k + 1) hk
      have hy0 := hy 0 (Nat.zero_le R)
      have hy1 := hy 1 h1R
      have hinc : y (k + 1) - y k = y 1 - y 0 := by
        apply eq_of_dvd_sub_of_mem_short_interval hW hm
        · omega
        · omega
        · omega
        · omega
        · exact hcong k hkR
      have heq : y (k + 1) = y k + (y 1 - y 0) := by omega
      rw [heq, ih hk_le]
      push_cast
      ring

/-- If the lifted orbit starts at zero, confinement also bounds the step by
`W / R` in the integral form `R * |step| ≤ W`. -/
theorem short_arc_step_bound
    {R : ℕ} {m W : ℤ} (y : ℕ → ℤ)
    (hR : 1 ≤ R) (hW : 0 ≤ W) (hm : 4 * W < m)
    (hy0 : y 0 = 0)
    (hy : ∀ k, k ≤ R → -W ≤ y k ∧ y k ≤ W)
    (hcong : ∀ k, k < R →
      m ∣ (y (k + 1) - y k) - (y 1 - y 0)) :
    (R : ℤ) * |y 1 - y 0| ≤ W := by
  have hrect := short_arc_orbit_rectification y hW hm hy hcong R (le_refl R)
  have hyR := hy R (le_refl R)
  simp only [hy0, sub_zero, zero_add] at hrect ⊢
  rw [hrect] at hyR
  have hRz : (0 : ℤ) ≤ R := by positivity
  rcases le_total 0 (y 1) with hd | hd
  · rw [abs_of_nonneg hd]
    exact hyR.2
  · rw [abs_of_nonpos hd]
    nlinarith [hyR.1]

end Erdos336
