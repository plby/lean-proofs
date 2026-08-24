import ErdosProblems.Erdos587.CenteredMean
import ErdosProblems.Erdos587.ChirpWeights
import ErdosProblems.Erdos587.FresnelSeries

/-!
# Smoothly weighted centered quadratic means

The bounded quadratic-modulation family has uniformly summable block
variation. The centered interval mean therefore controls its full series.
-/

open scoped BigOperators SchwartzMap

namespace Erdos587

noncomputable def centeredChirpSeries (f : 𝓢(ℝ, ℂ)) (q : ℕ) (a : ℤ) (A δ : ℝ) : ℂ :=
  ∑' n : ℤ, quadraticChirpMul A f (δ * n) *
    (quadraticResiduePhase q a n - completeQuadraticGaussSum q a 0 / q)

lemma summable_centered_chirp_series (f : 𝓢(ℝ, ℂ)) (q : ℕ) (a : ℤ) (A : ℝ)
    {δ : ℝ} (hδ : δ ≠ 0) :
    Summable (fun n : ℤ => quadraticChirpMul A f (δ * n) *
      (quadraticResiduePhase q a n - completeQuadraticGaussSum q a 0 / q)) := by
  have hw : Summable (fun n : ℤ => quadraticChirpMul A f (δ * n)) :=
    summable_schwartz_int (dilateSchwartz (quadraticChirpMul A f) δ hδ)
  apply (hw.norm.mul_right (1 + ‖completeQuadraticGaussSum q a 0 / q‖)).of_norm_bounded
  intro n
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  have hnorm : ‖quadraticResiduePhase q a n‖ = 1 := norm_phase _
  simpa only [hnorm] using norm_sub_le (quadraticResiduePhase q a n)
    (completeQuadraticGaussSum q a 0 / q)

theorem exists_centered_chirp_series_mean_bound (f : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 < C ∧ ∃ O : ℕ, 0 < O ∧ ∀ (a q M K : ℕ),
      let X := 2 * M * K
      let D := Nat.sqrt (Nat.sqrt X)
      a.Coprime q → 0 < q → 0 < K → 3 ≤ D → q - 1 ≤ X → q * D ≤ X →
        ∀ δ : ℝ, 0 < δ → 1 / 2 ≤ δ * K → δ * K ≤ 2 →
          ∀ A : ℕ → ℝ, (∀ m ∈ Finset.Icc 1 M, |A m| ≤ 1) →
          (∑ m ∈ Finset.Icc 1 M, ‖centeredChirpSeries f q ((a * m : ℕ) : ℤ) (A m) δ‖) ≤
            C * M * Real.sqrt K * Real.log (X : ℝ) ^ O := by
  obtain ⟨C₀, hC₀, hvar⟩ := exists_uniform_chirp_block_variation_bound f 2
  obtain ⟨C₁, hC₁, O, hO, hmean⟩ := exists_centered_quadratic_mean_bound
  let Z : ℝ := ∑' j : ℤ, 1 / (1 + |(j : ℝ)|) ^ 2
  have hZ : 0 ≤ Z := tsum_nonneg (fun j => by positivity)
  refine ⟨C₀ * (C₁ + 1) * Z + 1, by positivity, O, hO, ?_⟩
  intro a q M K
  dsimp only
  let X := 2 * M * K
  let D := Nat.sqrt (Nat.sqrt X)
  intro haq hq hK hD hqX hqD δ hδ hlo hhi A hA
  let F : ℝ := Real.log (X : ℝ) ^ O
  have hXthree : 3 ≤ X := hD.trans ((Nat.sqrt_le_self (Nat.sqrt X)).trans (Nat.sqrt_le_self X))
  have hF : 1 ≤ F := one_le_pow₀ (one_le_log_nat_of_three_le hXthree)
  have hB : 0 ≤ C₁ * M * K * F := by positivity
  have hinter (s : ℕ → ℤ) (l : ℕ → ℕ) (hl : ∀ m ∈ Finset.Icc 1 M, l m ≤ K) :
      (∑ m ∈ Finset.Icc 1 M, ‖∑ n ∈ Finset.range (l m),
        (quadraticResiduePhase q ((a * m : ℕ) : ℤ) (s m + n) -
          completeQuadraticGaussSum q ((a * m : ℕ) : ℤ) 0 / q)‖ ^ 2) ≤ C₁ * M * K * F := by
    simp_rw [← centeredQuadraticInterval_eq_sum]
    exact hmean a q M K haq hq hD hqX hqD s l hl
  have hwvar (m : ℕ) (hm : m ∈ Finset.Icc 1 M) (j : ℤ) :
      finiteVariationNorm (fun n => quadraticChirpMul (A m) f
        (δ * (((K : ℤ) * j + n : ℤ) : ℝ))) K ≤ C₀ / (1 + |(j : ℝ)|) ^ 2 := by
    have h := hvar (A m) (δ * K) 0 δ K j (hA m hm) hlo (by simp) hδ.le hhi
    convert h using 1
    congr 1
    funext n
    congr 1
    push_cast
    ring
  have hseries := sum_norm_weighted_series_le_of_interval_means (Finset.Icc 1 M) K hK
    (fun m n => quadraticResiduePhase q ((a * m : ℕ) : ℤ) n -
      completeQuadraticGaussSum q ((a * m : ℕ) : ℤ) 0 / q)
    (fun m n => quadraticChirpMul (A m) f (δ * n)) hC₀ hB hinter hwvar
    (fun m _ => summable_centered_chirp_series f q ((a * m : ℕ) : ℤ) (A m) hδ.ne')
  have hroot : Real.sqrt ((M : ℝ) * (C₁ * M * K * F)) ≤
      (C₁ + 1) * M * Real.sqrt K * F :=
    sqrt_card_reciprocal_mean_le hC₁.le hF (by omega : M ≤ 2 * M)
  have hseries' : (∑ m ∈ Finset.Icc 1 M, ‖centeredChirpSeries f q ((a * m : ℕ) : ℤ) (A m) δ‖) ≤
      (C₀ * Real.sqrt ((M : ℝ) * (C₁ * M * K * F))) * Z := by
    simpa only [centeredChirpSeries, Z, Nat.card_Icc, Nat.add_sub_cancel] using hseries
  apply hseries'.trans
  calc
    _ ≤ (C₀ * ((C₁ + 1) * M * Real.sqrt K * F)) * Z :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hroot hC₀) hZ
    _ = (C₀ * (C₁ + 1) * Z) * M * Real.sqrt K * F := by ring
    _ ≤ (C₀ * (C₁ + 1) * Z + 1) * M * Real.sqrt K * F := by gcongr; linarith

end Erdos587
