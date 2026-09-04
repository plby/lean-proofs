import Util.Bernays.NormFiberCounts
import Util.Bernays.ClassCharacterSummatory
import Util.Bernays.SummatoryMellin

/-!
# Analytic continuation of nontrivial quadratic ideal-class series
-/

open Filter Topology Asymptotics
open scoped Classical

namespace Bernays

noncomputable def weightedIdealNormCoeff {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    (F : Ideal (QuadraticAlgebra ℤ d b)) :
    letI := quadraticOrderIsDomain hD
    (ClassGroup (QuadraticAlgebra ℤ d b) → ℂ) → ℕ → ℂ :=
  letI := quadraticOrderIsDomain hD
  letI := quadraticOrderClassGroupFintype hD
  fun w n => ∑ C, w C * (idealClassNormCount C F n : ℂ)

theorem weightedIdealNormCoeff_cumsum {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    (F : Ideal (QuadraticAlgebra ℤ d b)) :
    letI := quadraticOrderIsDomain hD
    ∀ (w : ClassGroup (QuadraticAlgebra ℤ d b) → ℂ) (N : ℕ),
      (∑ n ∈ Finset.Icc 1 N, weightedIdealNormCoeff hD F w n) =
        weightedIdealClassCount hD F w N := by
  let := quadraticOrderIsDomain hD
  let := quadraticOrderClassGroupFintype hD
  intro w N
  unfold weightedIdealNormCoeff weightedIdealClassCount
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro C _
  rw [← Finset.mul_sum, ← Nat.cast_sum, idealClassNormCount_cumsum hD]

theorem weightedIdealNormCoeff_norm_cumsum_le {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    (F : Ideal (QuadraticAlgebra ℤ d b)) :
    letI := quadraticOrderIsDomain hD
    letI := quadraticOrderClassGroupFintype hD
    ∀ (w : ClassGroup (QuadraticAlgebra ℤ d b) → ℂ) (N : ℕ),
      (∑ n ∈ Finset.Icc 1 N, ‖weightedIdealNormCoeff hD F w n‖) ≤
        ∑ C, ‖w C‖ * (Nat.card (RestrictedIdealClassBall (QuadraticAlgebra ℤ d b) C N
          (fun J => IsCoprime (J : Ideal (QuadraticAlgebra ℤ d b)) F)) : ℝ) := by
  let := quadraticOrderIsDomain hD
  let := quadraticOrderClassGroupFintype hD
  intro w N
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 N, ∑ C, ‖w C‖ * (idealClassNormCount C F n : ℝ) := by
      apply Finset.sum_le_sum
      intro n _
      simpa only [weightedIdealNormCoeff, norm_mul, Complex.norm_natCast] using
        norm_sum_le (s := Finset.univ) (f := fun C => w C * (idealClassNormCount C F n : ℂ))
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro C _
      rw [← Finset.mul_sum, ← Nat.cast_sum, idealClassNormCount_cumsum hD]

theorem weightedIdealNormCoeff_summable {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    (F : Ideal (QuadraticAlgebra ℤ d b)) :
    letI := quadraticOrderIsDomain hD
    ∀ (w : ClassGroup (QuadraticAlgebra ℤ d b) → ℂ) (s : ℂ), 1 < s.re →
      LSeriesSummable (weightedIdealNormCoeff hD F w) s := by
  let := quadraticOrderIsDomain hD
  let := quadraticOrderClassGroupFintype hD
  intro w s hs
  obtain ⟨B, _, hB⟩ := exists_uniform_natCard_idealClassBall_le hD
  have hle (C : ClassGroup (QuadraticAlgebra ℤ d b)) (N : ℕ) :
      Nat.card (RestrictedIdealClassBall (QuadraticAlgebra ℤ d b) C N
        (fun J => IsCoprime (J : Ideal (QuadraticAlgebra ℤ d b)) F)) ≤ B * N := by
    let := finite_idealClassBall hD C N
    exact (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective).trans (hB C N)
  have hsum (N : ℕ) : (∑ n ∈ Finset.Icc 1 N, ‖weightedIdealNormCoeff hD F w n‖) ≤
      (∑ C, ‖w C‖ * B) * N := by
    apply (weightedIdealNormCoeff_norm_cumsum_le hD F w N).trans
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro C _
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact_mod_cast hle C N
  have hO : (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, ‖weightedIdealNormCoeff hD F w n‖)
      =O[atTop] fun N : ℕ => (N : ℝ) ^ (1 : ℝ) := by
    apply IsBigO.of_bound (∑ C, ‖w C‖ * B)
    exact Filter.Eventually.of_forall (fun N => by
      rw [Real.rpow_one, Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _)),
        Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg N)]
      exact hsum N)
  exact LSeriesSummable_of_sum_norm_bigO hO zero_le_one hs

theorem classCharacterLSeries_continuation {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    (F : Ideal (QuadraticAlgebra ℤ d b)) (hF₀ : F ≠ ⊥) (hF₁ : F ≠ ⊤) :
    letI := quadraticOrderIsDomain hD
    ∀ ψ : AddChar (Additive (ClassGroup (QuadraticAlgebra ℤ d b))) ℂ, ψ ≠ 0 →
      ∃ G : ℂ → ℂ,
        (∀ s : ℂ, (1 / 2 : ℝ) < s.re → DifferentiableAt ℂ G s) ∧
        (∀ s : ℂ, 1 < s.re → G s =
          LSeries (weightedIdealNormCoeff hD F (fun C => ψ (Additive.ofMul C))) s) := by
  let := quadraticOrderIsDomain hD
  intro ψ hψ
  let a := weightedIdealNormCoeff hD F (fun C => ψ (Additive.ofMul C))
  have hO : (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, a n)
      =O[atTop] fun N : ℕ => (N : ℝ) ^ (1 / 2 : ℝ) := by
    simpa only [a, weightedIdealNormCoeff_cumsum] using idealClassCharacterCount_bigO hD F hF₀ hF₁ ψ hψ
  refine ⟨summatoryLSeries a, ?_, ?_⟩
  · intro s hs
    exact summatoryLSeries_differentiableAt (by norm_num) hO hs
  · intro s hs
    exact summatoryLSeries_eq (by norm_num) hO (by linarith)
      (weightedIdealNormCoeff_summable hD F _ s hs)

end Bernays
