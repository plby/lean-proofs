import Mathlib

/-! # A finite interval grid with an explicit number of cells -/

namespace Erdos1148.DukeArithmetic

theorem exists_real_interval_grid {a b w : ℝ} (hab : a ≤ b) (hw : 0 < w) :
    ∃ (N : ℕ) (c : Fin N → ℝ),
      (N : ℝ) ≤ (b - a) / w + 1 ∧
      (∀ i, a ≤ c i) ∧
      ∀ x ∈ Set.Icc a b, ∃ i, x ∈ Set.Icc (c i) (c i + w) := by
  let N := ⌊(b - a) / w⌋₊ + 1
  let c : Fin N → ℝ := fun i => a + w * i.val
  refine ⟨N, c, ?_, ?_, ?_⟩
  · dsimp only [N]
    push_cast
    exact add_le_add (Nat.floor_le (div_nonneg (sub_nonneg.mpr hab) hw.le)) le_rfl
  · intro i
    exact le_add_of_nonneg_right (mul_nonneg hw.le (Nat.cast_nonneg _))
  · intro x hx
    have hx0 : 0 ≤ (x - a) / w := div_nonneg (sub_nonneg.mpr hx.1) hw.le
    have hxb : (x - a) / w ≤ (b - a) / w := div_le_div_of_nonneg_right
      (sub_le_sub_right hx.2 a) hw.le
    let i : Fin N := ⟨⌊(x - a) / w⌋₊, Nat.lt_succ_of_le (Nat.floor_mono hxb)⟩
    refine ⟨i, ?_, ?_⟩
    · change a + w * (⌊(x - a) / w⌋₊ : ℝ) ≤ x
      have h := (le_div_iff₀ hw).mp (Nat.floor_le hx0)
      linarith
    · change x ≤ a + w * (⌊(x - a) / w⌋₊ : ℝ) + w
      have h := (div_lt_iff₀ hw).mp (Nat.lt_floor_add_one ((x - a) / w))
      nlinarith

lemma abs_sub_le_of_mem_same_interval {a w x y : ℝ}
    (hx : x ∈ Set.Icc a (a + w)) (hy : y ∈ Set.Icc a (a + w)) : |x - y| ≤ w := by
  apply abs_le.mpr
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

end Erdos1148.DukeArithmetic
