import ErdosProblems.Erdos587.CompleteRootDensity
import ErdosProblems.Erdos587.RankTwoSmoothing

/-!
# Exact smoothed counts with every complete-period mean retained

These identities separate the finite counting problem from its centered
Fourier error. The main term is the full-period smoothed count, not merely
the zero-frequency term.
-/

open scoped BigOperators

namespace Erdos587

noncomputable def nvSmoothedRectangleCount
    (q A B C X Z L U k : ℕ) [NeZero q] : ℕ := by
  classical
  exact ∑ v : Fin k → Fin U,
    ((Finset.range L).filter fun j =>
      ((A * (Z + j) ^ 2 + B * (Z + j) + C : ℕ) : ZMod q) =
        ((X + ∑ i, (v i : ℕ) : ℕ) : ZMod q)).card

lemma nvSmoothedRectangleCount_pos_iff
    (q A B C X Z L U k : ℕ) [NeZero q] :
    0 < nvSmoothedRectangleCount q A B C X Z L U k ↔
      ∃ v : Fin k → Fin U, ∃ j < L,
        ((A * (Z + j) ^ 2 + B * (Z + j) + C : ℕ) : ZMod q) =
          ((X + ∑ i, (v i : ℕ) : ℕ) : ZMod q) := by
  classical
  simp only [nvSmoothedRectangleCount, Finset.sum_pos_iff, Finset.mem_univ, true_and,
    Finset.card_pos, Finset.nonempty_def, Finset.mem_filter, Finset.mem_range]

lemma nv_smoothed_frequency_sum_eq_count
    (q A B C X Z L U k : ℕ) [NeZero q] :
    (∑ h : ZMod q, nvCyclicIntervalCoeff q U h ^ k *
      nvQuadraticIntervalSum q A B C X Z L h) =
      (q : ℂ) * nvSmoothedRectangleCount q A B C X Z L U k := by
  classical
  calc
    _ = ∑ h : ZMod q, ∑ v : Fin k → Fin U, ∑ j ∈ Finset.range L,
        ZMod.stdAddChar
          (h * (((A * (Z + j) ^ 2 + B * (Z + j) + C : ℕ) : ZMod q) -
            ((X + ∑ i, (v i : ℕ) : ℕ) : ZMod q))) := by
      apply Finset.sum_congr rfl
      intro h hh
      exact (nv_smoothed_frequency_factorization q A B C X Z L U k h).symm
    _ = ∑ v : Fin k → Fin U, ∑ j ∈ Finset.range L, ∑ h : ZMod q,
        ZMod.stdAddChar
          (h * (((A * (Z + j) ^ 2 + B * (Z + j) + C : ℕ) : ZMod q) -
            ((X + ∑ i, (v i : ℕ) : ℕ) : ZMod q))) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro v hv
      rw [Finset.sum_comm]
    _ = ∑ v : Fin k → Fin U, ∑ j ∈ Finset.range L,
        if ((A * (Z + j) ^ 2 + B * (Z + j) + C : ℕ) : ZMod q) =
            ((X + ∑ i, (v i : ℕ) : ℕ) : ZMod q) then (q : ℂ) else 0 := by
      apply Finset.sum_congr rfl
      intro v hv
      apply Finset.sum_congr rfl
      intro j hj
      rw [Erdos387.AdditiveOrthogonality.sum_stdAddChar_mul]
      simp only [sub_eq_zero]
    _ = (q : ℂ) * nvSmoothedRectangleCount q A B C X Z L U k := by
      rw [nvSmoothedRectangleCount, Nat.cast_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v hv
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring

noncomputable def nvCenteredQuadraticIntervalSum
    (q A B C X Z L : ℕ) [NeZero q] (h : ZMod q) : ℂ :=
  nvQuadraticIntervalSum q A B C X Z L h -
    (L : ℂ) / q * nvQuadraticIntervalSum q A B C X Z q h

lemma nvCenteredQuadraticIntervalSum_zero
    (q A B C X Z L : ℕ) [NeZero q] :
    nvCenteredQuadraticIntervalSum q A B C X Z L 0 = 0 := by
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
  rw [nvCenteredQuadraticIntervalSum, nvQuadraticIntervalSum_zero, nvQuadraticIntervalSum_zero]
  field_simp
  ring

lemma norm_nvCenteredQuadraticIntervalSum_le
    (q A B C X Z L : ℕ) [NeZero q] (h : ZMod q) :
    ‖nvCenteredQuadraticIntervalSum q A B C X Z L h‖ ≤ 2 * L := by
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne q
  calc
    _ ≤ ‖nvQuadraticIntervalSum q A B C X Z L h‖ +
        ‖(L : ℂ) / q * nvQuadraticIntervalSum q A B C X Z q h‖ := norm_sub_le _ _
    _ = ‖nvQuadraticIntervalSum q A B C X Z L h‖ +
        ((L : ℝ) / q) * ‖nvQuadraticIntervalSum q A B C X Z q h‖ := by
      rw [norm_mul, norm_div, Complex.norm_natCast, Complex.norm_natCast]
    _ ≤ (L : ℝ) + ((L : ℝ) / q) * q :=
      add_le_add (norm_nvQuadraticIntervalSum_le_length q A B C X Z L h)
        (mul_le_mul_of_nonneg_left (norm_nvQuadraticIntervalSum_le_length q A B C X Z q h)
          (div_nonneg (Nat.cast_nonneg L) (Nat.cast_nonneg q)))
    _ = 2 * L := by rw [div_mul_cancel₀ _ hq]; ring

lemma nv_centered_smoothed_frequency_sum_eq_counts
    (q A B C X Z L U k : ℕ) [NeZero q] :
    (∑ h : ZMod q, nvCyclicIntervalCoeff q U h ^ k *
      nvCenteredQuadraticIntervalSum q A B C X Z L h) =
      (q : ℂ) * nvSmoothedRectangleCount q A B C X Z L U k -
        (L : ℂ) * nvSmoothedRectangleCount q A B C X Z q U k := by
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
  calc
    _ = (∑ h : ZMod q, nvCyclicIntervalCoeff q U h ^ k *
        nvQuadraticIntervalSum q A B C X Z L h) -
        ((L : ℂ) / q) * (∑ h : ZMod q, nvCyclicIntervalCoeff q U h ^ k *
          nvQuadraticIntervalSum q A B C X Z q h) := by
      simp only [nvCenteredQuadraticIntervalSum, mul_sub, Finset.sum_sub_distrib]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h hh
      ring
    _ = (q : ℂ) * nvSmoothedRectangleCount q A B C X Z L U k -
        ((L : ℂ) / q) * ((q : ℂ) * nvSmoothedRectangleCount q A B C X Z q U k) := by
      rw [nv_smoothed_frequency_sum_eq_count, nv_smoothed_frequency_sum_eq_count]
    _ = _ := by field_simp

lemma exists_rectangle_of_centered_error
    (q A B C X Z L U k : ℕ) [NeZero q]
    (herror : ‖∑ h : ZMod q, nvCyclicIntervalCoeff q U h ^ k *
        nvCenteredQuadraticIntervalSum q A B C X Z L h‖ <
      (L : ℝ) * (nvSmoothedRectangleCount q A B C X Z q U k : ℝ)) :
    ∃ v : Fin k → Fin U, ∃ j < L,
      ((A * (Z + j) ^ 2 + B * (Z + j) + C : ℕ) : ZMod q) =
        ((X + ∑ i, (v i : ℕ) : ℕ) : ZMod q) := by
  classical
  apply (nvSmoothedRectangleCount_pos_iff q A B C X Z L U k).mp
  by_contra hnot
  have hzero : nvSmoothedRectangleCount q A B C X Z L U k = 0 := Nat.eq_zero_of_not_pos hnot
  have hid := nv_centered_smoothed_frequency_sum_eq_counts q A B C X Z L U k
  rw [hzero, Nat.cast_zero, mul_zero, zero_sub] at hid
  have hnorm := congrArg norm hid
  simp only [norm_neg, norm_mul, Complex.norm_natCast] at hnorm
  rw [hnorm] at herror
  exact (lt_irrefl _) herror

end Erdos587
