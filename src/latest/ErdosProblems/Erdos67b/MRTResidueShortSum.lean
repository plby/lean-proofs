import ErdosProblems.Erdos67b.MRTCharacterResidues

/-! # Actual typical residue sums and the single-endpoint length error -/

open scoped BigOperators
open Finset

namespace Erdos67b

noncomputable section

def mrtResidueShortSum (blocks : Finset (ℕ × ℕ)) (Z : ℕ)
    (f : ℕ → ℂ) (n h q b : ℕ) : ℂ :=
  ∑ m ∈ (typicalShortSupport blocks Z n h).filter
    (fun m : ℕ ↦ (m : ZMod q) = (b : ZMod q)), f m

theorem mrtResidueShortSum_eq_typical (blocks : Finset (ℕ × ℕ)) (Z : ℕ)
    (f : ℕ → ℂ) (n h q b : ℕ) :
    mrtResidueShortSum blocks Z f n h q b = typicalModulatedShortSum blocks Z
      (fun m ↦ if (m : ZMod q) = (b : ZMod q) then f m else 0) n h 0 := by
  classical
  rw [typicalModulatedShortSum_eq_support_sum]
  simp [mrtResidueShortSum, Finset.sum_filter, additivePhase]

theorem mrtResidueShortSum_eq_increment_sum (blocks : Finset (ℕ × ℕ)) (Z : ℕ)
    (f : ℕ → ℂ) (n h q b : ℕ) :
    mrtResidueShortSum blocks Z f n h q b =
      ∑ j ∈ Finset.Icc 1 h, if n + j ∈ typicalFactorizationSet blocks Z then
        (if ((n + j : ℕ) : ZMod q) = (b : ZMod q) then f (n + j) else 0) else 0 := by
  rw [mrtResidueShortSum_eq_typical]
  simp only [typicalModulatedShortSum, additivePhase, Complex.ofReal_zero,
    mul_zero, zero_mul, Complex.exp_zero, mul_one]

theorem mrtNorm_residueShortSum_le (blocks : Finset (ℕ × ℕ)) (Z n h q b : ℕ)
    {f : ℕ → ℂ} (hbound : ∀ m, 0 < m → ‖f m‖ ≤ 1) :
    ‖mrtResidueShortSum blocks Z f n h q b‖ ≤ (h : ℝ) := by
  classical
  rw [mrtResidueShortSum_eq_increment_sum]
  calc
    _ ≤ ∑ j ∈ Finset.Icc 1 h, ‖if n + j ∈ typicalFactorizationSet blocks Z then
        (if ((n + j : ℕ) : ZMod q) = (b : ZMod q) then f (n + j) else 0) else 0‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _j ∈ Finset.Icc 1 h, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjpos := (Finset.mem_Icc.1 hj).1
      split_ifs
      · exact hbound _ (by omega)
      · norm_num
      · norm_num
    _ = _ := by simp

theorem mrtResidueShortSum_succ (blocks : Finset (ℕ × ℕ)) (Z : ℕ)
    (f : ℕ → ℂ) (n h q b : ℕ) :
    mrtResidueShortSum blocks Z f n (h + 1) q b =
      mrtResidueShortSum blocks Z f n h q b +
        if n + (h + 1) ∈ typicalFactorizationSet blocks Z then
          (if ((n + (h + 1) : ℕ) : ZMod q) = (b : ZMod q)
            then f (n + (h + 1)) else 0) else 0 := by
  rw [mrtResidueShortSum_eq_increment_sum, mrtResidueShortSum_eq_increment_sum,
    Finset.sum_Icc_succ_top (by omega : 1 ≤ h + 1)]

theorem mrtNorm_residueShortSum_succ_le (blocks : Finset (ℕ × ℕ)) (Z n h q b : ℕ)
    {f : ℕ → ℂ} (hbound : ∀ m, 0 < m → ‖f m‖ ≤ 1) :
    ‖mrtResidueShortSum blocks Z f n (h + 1) q b‖ ≤
      ‖mrtResidueShortSum blocks Z f n h q b‖ + 1 := by
  classical
  rw [mrtResidueShortSum_succ]
  apply (norm_add_le _ _).trans
  apply add_le_add (le_refl _)
  split_ifs
  · exact hbound _ (by omega)
  · norm_num
  · norm_num

theorem mrtNorm_residueShortSum_adjacent_le (blocks : Finset (ℕ × ℕ)) (Z n h k q b : ℕ)
    {f : ℕ → ℂ} (hbound : ∀ m, 0 < m → ‖f m‖ ≤ 1) (hk : k = h ∨ k = h + 1) :
    ‖mrtResidueShortSum blocks Z f n k q b‖ ≤
      ‖mrtResidueShortSum blocks Z f n h q b‖ + 1 := by
  rcases hk with rfl | rfl
  · linarith
  · exact mrtNorm_residueShortSum_succ_le blocks Z n h q b hbound

end

end Erdos67b
