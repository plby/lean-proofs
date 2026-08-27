import ErdosProblems.Erdos587.HooleySmoothLargeDenominator
import ErdosProblems.Erdos587.HooleySmoothReduction

/-! # The centered smooth quadratic mean with a seventh log-log power -/

open scoped BigOperators FourierTransform SchwartzMap

namespace Erdos587

theorem exists_delta_smooth_centered_power_mean {W : Set 𝓢(ℝ, ℂ)}
    (hW : Bornology.IsVonNBounded ℝ W) (r : ℕ) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ a M q D : ℕ, 1 ≤ M → 0 < q → q.Coprime a →
      (q : ℝ) * (M * 2 ^ D : ℕ) ^ (3 / (r : ℝ)) ≤ (M * 2 ^ D : ℕ) →
      ∀ K : ℝ, 1 ≤ K → K ≤ 2 ^ D → ∀ f : ℕ → 𝓢(ℝ, ℂ),
      (∀ m ∈ Finset.Icc 1 M, f m ∈ W) →
      (∑ m ∈ Finset.Icc 1 M, ‖deltaSmoothCenteredQuadratic (f m) K q (a * m)‖ ^ 2) ≤
        C * (M * 2 ^ D : ℕ) * (max 1 (Real.log (Real.log (M * 2 ^ D : ℕ)))) ^ 7 := by
  classical
  obtain ⟨C₀, hC₀, hlarge⟩ := exists_delta_smooth_large_denominator_mean hW r hr
  obtain ⟨C₁, hC₁, hsmall⟩ := exists_delta_small_reduced_denominator_centered_sq_bound hW
  obtain ⟨C₂, hC₂, hmean⟩ := exists_delta_large_reduced_denominator_zero_mode_sq_bound hW
  refine ⟨2 * C₀ + C₁ + 2 * C₂, by positivity, ?_⟩
  intro a M q D hM hq hcop hsep K hK hKD f hf
  let N := M * 2 ^ D
  let F := (max 1 (Real.log (Real.log (N : ℝ)))) ^ 7
  let I := (Finset.Icc 1 M).filter (fun m : ℕ => K < (q / q.gcd m : ℕ))
  let g := fun m : ℕ => ‖deltaSmoothQuadraticSum (f m) K ((a : ℝ) * m / q) 0‖ ^ 2
  have hKpos : 0 < K := by linarith
  have hF : 1 ≤ F := one_le_pow₀ (le_max_left _ _)
  have hpoint (m : ℕ) (hm : m ∈ Finset.Icc 1 M) :
      ‖deltaSmoothCenteredQuadratic (f m) K q (a * m)‖ ^ 2 ≤
        (if K < (q / q.gcd m : ℕ) then 2 * g m else 0) + (C₁ + 2 * C₂) * K := by
    by_cases hden : K < (q / q.gcd m : ℕ)
    · rw [if_pos hden]
      have hz := hmean (f m) (hf m hm) a q hq hcop m K hKpos hden.le
      have hsub : ‖deltaSmoothCenteredQuadratic (f m) K q (a * m)‖ ^ 2 ≤
          2 * g m + 2 * ‖deltaSmoothQuadraticMean (f m) K q (a * m)‖ ^ 2 := by
        simpa only [deltaSmoothCenteredQuadratic, Int.cast_mul, Int.cast_natCast, g] using
          norm_sub_sq_le_twice_sq
            (deltaSmoothQuadraticSum (f m) K ((a : ℝ) * m / q) 0)
            (deltaSmoothQuadraticMean (f m) K q (a * m))
      nlinarith
    · rw [if_neg hden, zero_add]
      have hs := hsmall (f m) (hf m hm) a q hq hcop m K hKpos (le_of_not_gt hden)
      nlinarith
  have hsum : (∑ m ∈ Finset.Icc 1 M, ‖deltaSmoothCenteredQuadratic (f m) K q (a * m)‖ ^ 2) ≤
      2 * (∑ m ∈ I, g m) + (C₁ + 2 * C₂) * M * K := by
    apply (Finset.sum_le_sum hpoint).trans_eq
    rw [Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.mul_sum]
    simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
    ring
  have hI : I ⊆ Finset.Icc 1 M := Finset.filter_subset _ _
  have hlargeSum : (∑ m ∈ I, g m) ≤ C₀ * (N : ℝ) * F :=
    hlarge a M q D hM hq hcop hsep K hK hKD I hI
      (fun m hm => (Finset.mem_filter.mp hm).2) f (fun _ => 0)
      (fun m hm => hf m (hI hm))
  have hMK : (M : ℝ) * K ≤ N := by
    calc
      _ ≤ (M : ℝ) * 2 ^ D := mul_le_mul_of_nonneg_left hKD (Nat.cast_nonneg M)
      _ = _ := by dsimp only [N]; push_cast; rfl
  have htail : (C₁ + 2 * C₂) * M * K ≤ (C₁ + 2 * C₂) * N * F := by
    calc
      _ = (C₁ + 2 * C₂) * ((M : ℝ) * K) := by ring
      _ ≤ (C₁ + 2 * C₂) * N := mul_le_mul_of_nonneg_left hMK (by positivity)
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hF
  calc
    _ ≤ 2 * (∑ m ∈ I, g m) + (C₁ + 2 * C₂) * M * K := hsum
    _ ≤ 2 * (C₀ * N * F) + (C₁ + 2 * C₂) * N * F :=
      add_le_add (mul_le_mul_of_nonneg_left hlargeSum (by norm_num)) htail
    _ = _ := by dsimp only [F, N]; ring

end Erdos587
