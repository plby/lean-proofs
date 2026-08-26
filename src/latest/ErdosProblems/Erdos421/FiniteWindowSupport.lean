import Mathlib

/-! # Counting integer points in a real window -/

namespace Erdos421

theorem finite_nat_interval_card_le (S : Finset ℕ) {x b : ℝ} (hx : 0 ≤ x) (hxb : x ≤ b)
    (hS : ∀ n ∈ S, x < (n : ℝ) ∧ (n : ℝ) ≤ b) :
    (S.card : ℝ) ≤ b - x + 1 := by
  have hb : 0 ≤ b := hx.trans hxb
  have hsub : S ⊆ Finset.Icc (⌊x⌋₊ + 1) ⌊b⌋₊ := by
    intro n hn
    exact Finset.mem_Icc.mpr ⟨(Nat.floor_lt hx).mpr (hS n hn).1,
      (Nat.le_floor_iff hb).mpr (hS n hn).2⟩
  have hfloor : ⌊x⌋₊ ≤ ⌊b⌋₊ := Nat.floor_mono hxb
  have hcard : S.card ≤ ⌊b⌋₊ - ⌊x⌋₊ := by
    simpa only [Nat.card_Icc, Nat.add_sub_add_right] using Finset.card_le_card hsub
  have hcardR : (S.card : ℝ) ≤ (⌊b⌋₊ : ℝ) - (⌊x⌋₊ : ℝ) := by
    exact_mod_cast hcard
  have hflo := Nat.lt_floor_add_one x
  have hfhi := Nat.floor_le hb
  linarith

theorem finite_window_band_card_le (S : Finset ℕ) {x δ : ℝ} (hx : 0 ≤ x) (hδ : 0 ≤ δ) :
    ((S.filter (fun n : ℕ ↦ x < (n : ℝ) ∧ (n : ℝ) ≤ (1 + 2 * δ) * x)).card : ℝ) ≤
      2 * δ * x + 1 := by
  have hxb : x ≤ (1 + 2 * δ) * x := by nlinarith
  have hb := finite_nat_interval_card_le
    (S.filter (fun n : ℕ ↦ x < (n : ℝ) ∧ (n : ℝ) ≤ (1 + 2 * δ) * x)) hx hxb
    (fun n hn ↦ (Finset.mem_filter.mp hn).2)
  nlinarith

end Erdos421
