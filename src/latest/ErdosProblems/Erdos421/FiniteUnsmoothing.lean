import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

/-! # Removing a triangular weight by finite differences -/

namespace Erdos421

open Complex

noncomputable def finiteRealPrefix (a : ℕ → ℂ) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.range (⌊x⌋₊ + 1), a n

noncomputable def finiteTriangularSum (a : ℕ → ℂ) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.range (⌊x⌋₊ + 1), a n * ((x - n : ℝ) : ℂ)

theorem finiteTriangularSum_difference (a : ℕ → ℂ) (x : ℝ) {h : ℝ} (hh : 0 ≤ h) :
    finiteTriangularSum a (x + h) - finiteTriangularSum a x =
      (h : ℂ) * finiteRealPrefix a x +
        ∑ n ∈ Finset.Ico (⌊x⌋₊ + 1) (⌊x + h⌋₊ + 1), a n * ((x + h - n : ℝ) : ℂ) := by
  have hn : ⌊x⌋₊ + 1 ≤ ⌊x + h⌋₊ + 1 :=
    Nat.add_le_add_right (Nat.floor_mono (by linarith)) 1
  unfold finiteTriangularSum finiteRealPrefix
  rw [← Finset.sum_range_add_sum_Ico (fun n ↦ a n * ((x + h - n : ℝ) : ℂ)) hn]
  rw [show (∑ n ∈ Finset.range (⌊x⌋₊ + 1), a n * ((x + h - n : ℝ) : ℂ)) +
      (∑ n ∈ Finset.Ico (⌊x⌋₊ + 1) (⌊x + h⌋₊ + 1), a n * ((x + h - n : ℝ) : ℂ)) -
      (∑ n ∈ Finset.range (⌊x⌋₊ + 1), a n * ((x - n : ℝ) : ℂ)) =
      ((∑ n ∈ Finset.range (⌊x⌋₊ + 1), a n * ((x + h - n : ℝ) : ℂ)) -
        (∑ n ∈ Finset.range (⌊x⌋₊ + 1), a n * ((x - n : ℝ) : ℂ))) +
      (∑ n ∈ Finset.Ico (⌊x⌋₊ + 1) (⌊x + h⌋₊ + 1), a n * ((x + h - n : ℝ) : ℂ)) by abel]
  congr 1
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  push_cast
  ring

theorem triangular_boundary_bounds {x h : ℝ} (hx : 0 ≤ x) (hh : 0 ≤ h) {n : ℕ}
    (hn : n ∈ Finset.Ico (⌊x⌋₊ + 1) (⌊x + h⌋₊ + 1)) :
    0 ≤ x + h - n ∧ x + h - n ≤ h := by
  obtain ⟨hl, hu⟩ := Finset.mem_Ico.mp hn
  have hnx : x < (n : ℝ) := (Nat.floor_lt hx).mp (by omega)
  have hnu : (n : ℝ) ≤ x + h :=
    (Nat.cast_le.mpr (by omega : n ≤ ⌊x + h⌋₊)).trans (Nat.floor_le (by linarith))
  constructor <;> linarith

theorem triangular_boundary_card_le {x h : ℝ} (hx : 0 ≤ x) (hh : 0 ≤ h) :
    ((Finset.Ico (⌊x⌋₊ + 1) (⌊x + h⌋₊ + 1)).card : ℝ) ≤ h + 1 := by
  have hn : ⌊x⌋₊ + 1 ≤ ⌊x + h⌋₊ + 1 :=
    Nat.add_le_add_right (Nat.floor_mono (by linarith)) 1
  rw [Nat.card_Ico, Nat.cast_sub hn]
  have hlow := Nat.lt_floor_add_one x
  have hupp := Nat.floor_le (show 0 ≤ x + h by linarith)
  push_cast
  linarith

theorem finiteTriangularSum_unsmoothing_bound (a : ℕ → ℂ) {x h M : ℝ}
    (hx : 0 ≤ x) (hh : 0 < h) (hM : 0 ≤ M)
    (ha : ∀ n ∈ Finset.Ico (⌊x⌋₊ + 1) (⌊x + h⌋₊ + 1), ‖a n‖ ≤ M) :
    ‖finiteRealPrefix a x‖ ≤
      (‖finiteTriangularSum a (x + h)‖ + ‖finiteTriangularSum a x‖) / h + (h + 1) * M := by
  let S := Finset.Ico (⌊x⌋₊ + 1) (⌊x + h⌋₊ + 1)
  let V : ℂ := ∑ n ∈ S, a n * ((x + h - n : ℝ) : ℂ)
  have hV : ‖V‖ ≤ (h + 1) * M * h := by
    have hb : ‖V‖ ≤ (S.card : ℝ) * (M * h) := by
      apply (norm_sum_le _ _).trans
      calc
        _ ≤ ∑ _n ∈ S, M * h := by
          apply Finset.sum_le_sum
          intro n hn
          obtain ⟨hlo, hhi⟩ := triangular_boundary_bounds hx hh.le hn
          rw [norm_mul, Complex.norm_of_nonneg hlo]
          exact mul_le_mul (ha n hn) hhi hlo hM
        _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
    exact hb.trans (by
      have hm := mul_le_mul_of_nonneg_right (triangular_boundary_card_le hx hh.le)
        (mul_nonneg hM hh.le)
      exact hm.trans_eq (by ring))
  have he : (h : ℂ) * finiteRealPrefix a x =
      finiteTriangularSum a (x + h) - finiteTriangularSum a x - V := by
    have h := finiteTriangularSum_difference a x hh.le
    change _ = _ + V at h
    exact eq_sub_of_add_eq h.symm
  have hnorm : h * ‖finiteRealPrefix a x‖ ≤
      ‖finiteTriangularSum a (x + h)‖ + ‖finiteTriangularSum a x‖ + (h + 1) * M * h := by
    have hb := (norm_sub_le
      (finiteTriangularSum a (x + h) - finiteTriangularSum a x) V).trans
        (add_le_add (norm_sub_le _ _) hV)
    rwa [← he, norm_mul, Complex.norm_of_nonneg hh.le] at hb
  apply (mul_le_mul_iff_right₀ hh).mp
  have he' : h * ((‖finiteTriangularSum a (x + h)‖ + ‖finiteTriangularSum a x‖) / h +
      (h + 1) * M) = ‖finiteTriangularSum a (x + h)‖ + ‖finiteTriangularSum a x‖ +
        (h + 1) * M * h := by field_simp
  rwa [he']

end Erdos421
