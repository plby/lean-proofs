import ErdosProblems.Erdos67.StationarySamplingLaw

/-!
# Exact finite identities behind conditional dilation

Conditioning the harmonic starting point to be divisible by `d` changes its
cutoff to `N/d`, and multiplies the sampled dilation by `d`.
-/

open scoped BigOperators
open Finset

namespace Erdos67.StationaryModel

theorem toNat_nat_mul (d : ℕ) (z : ℤ) : ((d : ℤ) * z).toNat = d * z.toNat := by
  by_cases hz : 0 ≤ z
  · rw [Int.toNat_mul (Nat.cast_nonneg d) hz, Int.toNat_natCast]
  · have hz' : z ≤ 0 := (lt_of_not_ge hz).le
    rw [Int.toNat_eq_zero.mpr hz', mul_zero,
      Int.toNat_eq_zero.mpr (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg d) hz')]

/-- Only the sign coordinates are needed in conditional dilation. -/
def signDilation (d : ℕ) (ω : Configuration) : ℤ → Bool :=
  fun j ↦ ω.1 ((d : ℤ) * j)

theorem continuous_signDilation (d : ℕ) : Continuous (signDilation d) :=
  continuous_pi fun j ↦ (continuous_apply ((d : ℤ) * j)).comp continuous_fst

theorem signDilation_sample (f : ℕ → Bool) (D d n : ℕ) :
    signDilation d (sample f D (d * n)) = (sample f (d * D) n).1 := by
  funext j
  change f (D * (((d * n : ℕ) : ℤ) + (d : ℤ) * j).toNat) =
    f ((d * D) * ((n : ℤ) + j).toNat)
  rw [Nat.cast_mul, ← mul_add, toNat_nat_mul]
  congr 1
  ring

theorem sum_divisible_succ (N d : ℕ) (hd : 0 < d) (A : ℕ → ℝ) :
    (∑ j ∈ range N, if d ∣ j + 1 then A (j + 1) else 0) =
      ∑ k ∈ range (N / d), A (d * (k + 1)) := by
  classical
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun k _ ↦ d * (k + 1) - 1)
  · intro k hk
    have hk' : k + 1 ≤ N / d := Nat.succ_le_of_lt (Finset.mem_range.mp hk)
    have hmul : d * (k + 1) ≤ N := by
      simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hd).mp hk'
    have hpos : 0 < d * (k + 1) := Nat.mul_pos hd (Nat.succ_pos _)
    have he : d * (k + 1) - 1 + 1 = d * (k + 1) := by omega
    simp only [Finset.mem_filter, Finset.mem_range, he]
    exact ⟨by omega, dvd_mul_right _ _⟩
  · intro k _ l _ hkl
    have hkpos : 0 < d * (k + 1) := Nat.mul_pos hd (Nat.succ_pos _)
    have hlpos : 0 < d * (l + 1) := Nat.mul_pos hd (Nat.succ_pos _)
    have he : d * (k + 1) = d * (l + 1) := by omega
    have hs := mul_left_cancel₀ hd.ne' he
    omega
  · intro j hj
    obtain ⟨hjN, hjd⟩ := Finset.mem_filter.mp hj
    obtain ⟨q, hq⟩ := hjd
    have hqpos : 0 < q := by
      by_contra! hq0
      have : q = 0 := Nat.eq_zero_of_le_zero hq0
      simp [this] at hq
    have hqN : q ≤ N / d := by
      apply (Nat.le_div_iff_mul_le hd).mpr
      have hle : d * q ≤ N := by rw [← hq]; exact (Finset.mem_range.mp hjN)
      simpa only [Nat.mul_comm] using hle
    refine ⟨q - 1, Finset.mem_range.mpr (by omega), ?_⟩
    have he : q - 1 + 1 = q := by omega
    rw [he, ← hq]
    omega
  · intro k _
    have hpos : 0 < d * (k + 1) := Nat.mul_pos hd (Nat.succ_pos _)
    have he : d * (k + 1) - 1 + 1 = d * (k + 1) := by omega
    rw [he]

/-- Exact harmonic change of variables on the divisible starting points. -/
theorem harmonic_sum_divisible_succ (N d : ℕ) (hd : 0 < d) (F : ℕ → ℝ) :
    (d : ℝ) * (∑ j ∈ range N,
      if d ∣ j + 1 then ((j + 1 : ℕ) : ℝ)⁻¹ * F (j + 1) else 0) =
        ∑ k ∈ range (N / d), ((k + 1 : ℕ) : ℝ)⁻¹ * F (d * (k + 1)) := by
  rw [sum_divisible_succ N d hd (fun n ↦ (n : ℝ)⁻¹ * F n), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  have hd' : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  rw [Nat.cast_mul, mul_inv_rev]
  field_simp

end Erdos67.StationaryModel
