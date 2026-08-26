import ErdosProblems.Erdos67b.MRPrimeSquareEnergy
import ErdosProblems.Erdos67b.MRTWindowFourthExpansion

/-! # Short-interval first-moment payment of the Ramaré prime-square correction -/

open scoped BigOperators
open Finset

namespace Erdos67b

noncomputable section

def mrtRawShortSum (g : ℕ → ℂ) (n H : ℕ) (α : ℝ) : ℂ :=
  ∑ r ∈ Finset.Ioc n (n + H), g r * additivePhase α r

theorem mrtSum_short_eq_increments {E : Type*} [AddCommMonoid E]
    (g : ℕ → E) (n H : ℕ) :
    (∑ r ∈ Finset.Ioc n (n + H), g r) = ∑ j ∈ Finset.Icc 1 H, g (n + j) := by
  symm
  apply Finset.sum_bij (fun j _ ↦ n + j)
  · intro j hj
    simp only [Finset.mem_Icc] at hj
    simp only [Finset.mem_Ioc]
    omega
  · intro i hi j hj hij
    omega
  · intro r hr
    simp only [Finset.mem_Ioc] at hr
    refine ⟨r - n, ?_, ?_⟩
    · simp only [Finset.mem_Icc]
      omega
    · omega
  · intro j hj
    rfl

theorem mrtRawShortSum_typical_eq (blocks : Finset (ℕ × ℕ)) (Z : ℕ)
    (f : ℕ → ℂ) (n H : ℕ) (α : ℝ) :
    mrtRawShortSum (mrTypicalValueCoefficient blocks Z f) n H α =
      additivePhase α n * typicalModulatedShortSum blocks Z f n H α := by
  classical
  unfold mrtRawShortSum
  rw [mrtSum_short_eq_increments]
  unfold typicalModulatedShortSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  unfold mrTypicalValueCoefficient
  split_ifs
  · rw [additivePhase_add]
    ring
  · simp

theorem mrtRawShortSum_typical_norm (blocks : Finset (ℕ × ℕ)) (Z : ℕ)
    (f : ℕ → ℂ) (n H : ℕ) (α : ℝ) :
    ‖mrtRawShortSum (mrTypicalValueCoefficient blocks Z f) n H α‖ =
      ‖typicalModulatedShortSum blocks Z f n H α‖ := by
  rw [mrtRawShortSum_typical_eq, norm_mul, norm_additivePhase, one_mul]

theorem mrtSum_short_nonneg_le (H Y : ℕ) (hHY : H ≤ Y) (g : ℕ → ℝ)
    (hg : ∀ r, 0 ≤ g r) :
    (∑ n ∈ Finset.Ioc Y (2 * Y), ∑ r ∈ Finset.Ioc n (n + H), g r) ≤
      H * ∑ r ∈ Finset.Icc 1 (3 * Y), g r := by
  classical
  simp_rw [mrtSum_short_eq_increments]
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ _j ∈ Finset.Icc 1 H, ∑ r ∈ Finset.Icc 1 (3 * Y), g r := by
      apply Finset.sum_le_sum
      intro j hj
      have hsub : (Finset.Ioc Y (2 * Y)).image (fun n ↦ n + j) ⊆ Finset.Icc 1 (3 * Y) := by
        intro r hr
        obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 hr
        simp only [Finset.mem_Ioc] at hn
        simp only [Finset.mem_Icc] at hj ⊢
        omega
      calc
        _ = ∑ r ∈ (Finset.Ioc Y (2 * Y)).image (fun n ↦ n + j), g r := by
          rw [Finset.sum_image]
          intro a ha b hb hab
          exact Nat.add_right_cancel hab
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun r _ _ ↦ hg r)
    _ = _ := by simp

theorem mrtTypicalCommon_difference_le_count
    {blocks : Finset (ℕ × ℕ)} {I : ℕ × ℕ} (hI : I ∈ blocks) {Z : ℕ}
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hf : ∀ r, 0 < r → ‖f r‖ ≤ 1) {r : ℕ} (hr : 0 < r) :
    ‖mrTypicalValueCoefficient blocks Z f r -
      mrTypicalCommonCoefficient blocks Z (primesInBlock I) f r‖ ≤
      2 * (primeSquareDivisorCount (primesInBlock I) r : ℝ) := by
  by_cases hc : primeSquareDivisorCount (primesInBlock I) r = 0
  · have hz := mrPrimeSquareErrorCoefficient_eq_zero_of_count_zero (Z := Z) hI hmul hr hc
    unfold mrPrimeSquareErrorCoefficient at hz
    have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hr
    have hzero := (div_eq_zero_iff.1 hz).resolve_right hr'
    rw [hzero, norm_zero, hc]
    simp
  · have hcount : (1 : ℝ) ≤ primeSquareDivisorCount (primesInBlock I) r := by
      exact_mod_cast (by omega : 1 ≤ primeSquareDivisorCount (primesInBlock I) r)
    have hvalue := norm_mrTypicalValueCoefficient_le_one (blocks := blocks) (Z := Z) hf hr
    have hcommon := norm_mrTypicalCommonCoefficient_le_one (blocks := blocks) (Z := Z)
      (P := primesInBlock I) (fun p hp ↦ (mem_primesInBlock.1 hp).1) hf hr
    exact (norm_sub_le _ _).trans (by linarith only [hvalue, hcommon, hcount])

theorem mrtSum_norm_primeSquare_short_error_le
    {blocks : Finset (ℕ × ℕ)} {I : ℕ × ℕ} (hI : I ∈ blocks) (hL : 0 < I.1)
    (Z H Y : ℕ) (hHY : H ≤ Y) (f : ℕ → ℂ) (α : ℝ)
    (hmul : IsMultiplicativeOnPositiveNat f) (hf : ∀ r, 0 < r → ‖f r‖ ≤ 1) :
    (∑ n ∈ Finset.Ioc Y (2 * Y),
      ‖mrtRawShortSum (mrTypicalValueCoefficient blocks Z f) n H α -
        mrtRawShortSum (mrTypicalCommonCoefficient blocks Z (primesInBlock I) f) n H α‖) ≤
      12 * H * Y / I.1 := by
  have hcount : (∑ r ∈ Finset.Icc 1 (3 * Y),
      (primeSquareDivisorCount (primesInBlock I) r : ℝ)) ≤
      (3 * Y : ℕ) * (2 / (I.1 : ℝ)) := by
    rw [← Nat.cast_sum, sum_primeSquareDivisorCount_Icc]
    exact cast_sum_primesInBlock_nat_div_sq_le_tail I hL
  calc
    _ ≤ ∑ n ∈ Finset.Ioc Y (2 * Y), ∑ r ∈ Finset.Ioc n (n + H),
        2 * (primeSquareDivisorCount (primesInBlock I) r : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      unfold mrtRawShortSum
      rw [← Finset.sum_sub_distrib]
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro r hr
      rw [← sub_mul, norm_mul, norm_additivePhase, mul_one]
      exact mrtTypicalCommon_difference_le_count hI hmul hf
        ((Nat.zero_le n).trans_lt (Finset.mem_Ioc.1 hr).1)
    _ ≤ H * ∑ r ∈ Finset.Icc 1 (3 * Y),
        2 * (primeSquareDivisorCount (primesInBlock I) r : ℝ) :=
      mrtSum_short_nonneg_le H Y hHY _ (fun _ ↦ by positivity)
    _ = (2 * H) * ∑ r ∈ Finset.Icc 1 (3 * Y),
        (primeSquareDivisorCount (primesInBlock I) r : ℝ) := by rw [← Finset.mul_sum]; ring
    _ ≤ (2 * H) * ((3 * Y : ℕ) * (2 / (I.1 : ℝ))) :=
      mul_le_mul_of_nonneg_left hcount (by positivity)
    _ = _ := by push_cast; ring

end

end Erdos67b
