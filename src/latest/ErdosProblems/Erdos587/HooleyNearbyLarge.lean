import ErdosProblems.Erdos587.HooleyNearbyGlobalBlock
import ErdosProblems.Erdos587.HooleyGcdBlocks
import ErdosProblems.Erdos587.NearbyPartition

/-! # Summing all large nearby frequencies -/

open scoped BigOperators SchwartzMap

namespace Erdos587

theorem exists_delta_nearby_large_frequency_mean (f : 𝓢(ℝ, ℂ))
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ a u v M M₀ X : ℕ,
      0 < u → 0 < v → a.Coprime u → u.Coprime v → u ∣ a * v + 1 →
      2 ≤ X → u ≤ X → ∀ L : ℝ, 0 < L → (u : ℝ) * v / L ^ 2 < M₀ + 1 →
      4 * L * (X : ℝ) ^ κ ≤ v → 4 * (M : ℝ) * L ≤ u * v →
      (4 * L + 16 * u) * M ≤ X →
      (∑ m ∈ nearbyLargeFrequencies u v M M₀ L,
        ‖nearbyQuadraticRemainder f u m v (a : ℤ) L‖) ≤
        C * M * Real.sqrt L * (max 1 (Real.log (Real.log (X : ℝ)))) ^ (9 / 2 : ℝ) := by
  obtain ⟨C, hC, hblock⟩ := exists_delta_nearby_high_block_global_mean f hκ
  obtain ⟨B, hB, hmass⟩ := exists_delta_gcd_dyadic_mass_bound
  refine ⟨C * B, by positivity, ?_⟩
  intro a u v M M₀ X hu hv ha huv hav hX huX L hL hcutoff hsep hglobal hsize
  let F := max 1 (Real.log (Real.log (X : ℝ)))
  have hF : 0 < F := by dsimp [F]; positivity
  have hpoint (d : ℕ) (hd : d ∈ u.divisors) (k : ℕ) :
      (∑ r ∈ nearbyHighBlock (u / d) v M M₀ d (2 ^ k) L,
        ‖nearbyQuadraticRemainder f u (d * r) v (a : ℤ) L‖) ≤
        C * (2 : ℝ) ^ k * Real.sqrt L * F ^ (7 / 2 : ℝ) := by
    have hh := hblock a u v M M₀ X hu hv ha huv hav hX huX L hL hcutoff hsep hglobal hsize
      d hd (2 ^ k) (pow_pos (by norm_num) k)
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hh
  apply (sum_nearby_large_le_blocks f a u v M M₀ hu L).trans
  calc
    _ ≤ ∑ d ∈ u.divisors, ∑ k ∈ dyadicBlockIndices (M / d),
        C * (2 : ℝ) ^ k * Real.sqrt L * F ^ (7 / 2 : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      exact Finset.sum_le_sum (fun k _ => hpoint d hd k)
    _ = (C * Real.sqrt L * F ^ (7 / 2 : ℝ)) *
        (∑ d ∈ u.divisors, ∑ k ∈ dyadicBlockIndices (M / d), (2 : ℝ) ^ k) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ ≤ (C * Real.sqrt L * F ^ (7 / 2 : ℝ)) * (B * M * F) :=
      mul_le_mul_of_nonneg_left (hmass u M X hu huX) (by positivity)
    _ = (C * B) * M * Real.sqrt L * (F ^ (7 / 2 : ℝ) * F) := by ring
    _ = _ := by rw [delta_rpow_seventh_half_mul_self hF]

end Erdos587
