import Util.Linnik.CharacterDerivative
import Util.Linnik.ExceptionalPole
import Mathlib.Data.Finsupp.Order

/-!
# Removing one exceptional real zero

The remaining zero divisor stays natural-valued.  A shifted exceptional
zero is removed only at small height, where it is inside the fixed disk;
at larger height the principal pole itself is an exponentially small error.
-/

namespace Linnik

open Complex Metric
open scoped BigOperators Classical

theorem real_zero_mem_radiusSix {beta t : ℝ}
    (hbeta₀ : 0 < beta) (hbeta₁ : beta < 1) (ht : |t| ≤ 4) :
    dist (beta : ℂ) ((2 : ℂ) + t * I) ≤ 6 := by
  have hreal : 0 ≤ 2 - beta := by linarith
  calc
    dist (beta : ℂ) ((2 : ℂ) + t * I) =
        ‖((2 - beta : ℝ) : ℂ) + t * I‖ := by
      rw [dist_comm, dist_eq_norm]
      congr 1
      push_cast
      ring
    _ ≤ ‖((2 - beta : ℝ) : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_add_le _ _
    _ = (2 - beta) + |t| := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hreal,
        norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_I, mul_one]
    _ ≤ 6 := by linarith

theorem one_le_characterDiskZeros_at_real_zero {q : ℕ} [NeZero q]
    (chi1 : DirichletCharacter ℂ q) (hchi1 : chi1 ≠ 1)
    {beta t : ℝ} (hbeta₀ : 0 < beta) (hbeta₁ : beta < 1)
    (hzero : DirichletCharacter.LFunction chi1 (beta : ℂ) = 0) (ht : |t| ≤ 4) :
    1 ≤ characterDiskZeros chi1 t (beta : ℂ) := by
  apply Nat.one_le_iff_ne_zero.mpr
  intro h
  have hd := real_zero_mem_radiusSix hbeta₀ hbeta₁ ht
  have hne := (diskZeros_zero_iff (differentiable_regularizedLFunction chi1)
    (regularizedLFunction_ne_zero_of_one_le_re chi1
      (s := (2 : ℂ) + t * I) (by simp)) hd).mp h
  apply hne
  simpa only [regularizedLFunction, if_neg hchi1] using hzero

theorem reciprocalPowerSum_sub_single_one (D : ℂ →₀ ℕ) {beta : ℂ}
    (hbeta : 1 ≤ D beta) (c : ℂ) (n : ℕ) :
    (D - Finsupp.single beta 1).sum (fun rho m ↦ (m : ℂ) / (c - rho) ^ n) +
        ((c - beta) ^ n)⁻¹ = D.sum (fun rho m ↦ (m : ℂ) / (c - rho) ^ n) := by
  have hle : Finsupp.single beta 1 ≤ D := Finsupp.single_le_iff.mpr hbeta
  have hD : D - Finsupp.single beta 1 + Finsupp.single beta 1 = D := tsub_add_cancel_of_le hle
  have hsum := congrArg (fun Z : ℂ →₀ ℕ ↦
    Z.sum (fun rho m ↦ (m : ℂ) / (c - rho) ^ n)) hD
  rw [Finsupp.sum_add_index' (by intro rho; simp)
    (by intro rho a b; push_cast; ring)] at hsum
  simpa only [Finsupp.sum_single_index, Nat.cast_one, one_div, Nat.cast_zero,
    zero_div] using hsum

noncomputable def remainingCharacterZeros {q : ℕ} [NeZero q]
    (chi1 chi : DirichletCharacter ℂ q) (beta t : ℝ) : ℂ →₀ ℕ :=
  if chi = chi1 ∧ |t| ≤ 4 then
    characterDiskZeros chi t - Finsupp.single (beta : ℂ) 1
  else characterDiskZeros chi t

theorem remainingCharacterZeros_le {q : ℕ} [NeZero q]
    (chi1 chi : DirichletCharacter ℂ q) (beta t : ℝ) :
    remainingCharacterZeros chi1 chi beta t ≤ characterDiskZeros chi t := by
  unfold remainingCharacterZeros
  split_ifs
  · exact tsub_le_self
  · exact le_rfl

noncomputable def removedExceptionalPower {q : ℕ} [NeZero q]
    (chi1 chi : DirichletCharacter ℂ q) (beta t : ℝ) (n : ℕ) : ℂ :=
  if chi = chi1 ∧ |t| ≤ 4 then (((2 : ℂ) + t * I - beta) ^ n)⁻¹ else 0

theorem zeroPowerSum_eq_remaining_add_exceptional {q : ℕ} [NeZero q]
    (chi1 chi : DirichletCharacter ℂ q) (hchi1 : chi1 ≠ 1)
    {beta : ℝ} (hbeta₀ : 0 < beta) (hbeta₁ : beta < 1)
    (hzero : DirichletCharacter.LFunction chi1 (beta : ℂ) = 0) (t : ℝ) (n : ℕ) :
    zeroPowerSum chi t n =
      (remainingCharacterZeros chi1 chi beta t).sum
        (fun rho m ↦ (m : ℂ) / ((2 : ℂ) + t * I - rho) ^ n) +
      removedExceptionalPower chi1 chi beta t n := by
  unfold remainingCharacterZeros removedExceptionalPower
  split_ifs with h
  · obtain ⟨hchi, ht⟩ := h
    subst chi
    exact (reciprocalPowerSum_sub_single_one (characterDiskZeros chi1 t)
      (one_le_characterDiskZeros_at_real_zero chi1 hchi1 hbeta₀ hbeta₁ hzero ht)
      ((2 : ℂ) + t * I) n).symm
  · simp only [zeroPowerSum, add_zero]

end Linnik
