import Util.Bernays.IdealClassAreaAsymptotic
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality

/-!
# Square-root cancellation in weighted ideal-class counts
-/

open Filter Topology Asymptotics
open scoped Classical

namespace Bernays

theorem weighted_common_term_error {ι : Type*} [Fintype ι]
    (w : ι → ℂ) (A K : ι → ℝ) (C B : ℝ) (hw : ∑ i, w i = 0)
    (hA : ∀ i, |A i - C| ≤ K i * B) :
    ‖∑ i, w i * (A i : ℂ)‖ ≤ (∑ i, ‖w i‖ * K i) * B := by
  have heq : (∑ i, w i * (A i : ℂ)) = ∑ i, w i * ((A i - C : ℝ) : ℂ) := by
    simp only [Complex.ofReal_sub, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hw,
      zero_mul, sub_zero]
  rw [heq]
  calc
    _ ≤ ∑ i, ‖w i * ((A i - C : ℝ) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖w i‖ * (K i * B) := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hA i) (norm_nonneg _)
    _ = _ := by simp only [← mul_assoc, Finset.sum_mul]

noncomputable def weightedIdealClassCount {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    (F : Ideal (QuadraticAlgebra ℤ d b)) :
    letI := quadraticOrderIsDomain hD
    (ClassGroup (QuadraticAlgebra ℤ d b) → ℂ) → ℕ → ℂ :=
  letI := quadraticOrderIsDomain hD
  letI := quadraticOrderClassGroupFintype hD
  fun w N => ∑ C, w C * (Nat.card (RestrictedIdealClassBall (QuadraticAlgebra ℤ d b) C N
    (fun J => IsCoprime (J : Ideal (QuadraticAlgebra ℤ d b)) F)) : ℂ)

theorem weightedIdealClassCount_error {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    (F : Ideal (QuadraticAlgebra ℤ d b)) (hF₀ : F ≠ ⊥) (hF₁ : F ≠ ⊤) :
    letI := quadraticOrderIsDomain hD
    letI := quadraticOrderClassGroupFintype hD
    ∀ w : ClassGroup (QuadraticAlgebra ℤ d b) → ℂ, (∑ C, w C) = 0 →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ,
        ‖weightedIdealClassCount hD F w N‖ ≤ K * (Real.sqrt (N : ℝ) + 1) := by
  let := quadraticOrderIsDomain hD
  let := quadraticOrderClassGroupFintype hD
  intro w hw
  choose K hKpos hK using idealClassArea_error hD F hF₀ hF₁
  refine ⟨∑ C, ‖w C‖ * K C, Finset.sum_nonneg (fun C _ => mul_nonneg (norm_nonneg _) (hKpos C).le), ?_⟩
  intro N
  have h := weighted_common_term_error w
    (fun C => (Nat.card (RestrictedIdealClassBall (QuadraticAlgebra ℤ d b) C N
      (fun J => IsCoprime (J : Ideal (QuadraticAlgebra ℤ d b)) F)) : ℝ))
    K (idealClassAreaConstant d b F * N) (Real.sqrt (N : ℝ) + 1) hw (fun C => hK C N)
  simpa only [weightedIdealClassCount, Complex.ofReal_natCast] using h

theorem sqrt_error_isBigO {f : ℕ → ℂ} {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ N : ℕ, ‖f N‖ ≤ K * (Real.sqrt (N : ℝ) + 1)) :
    f =O[atTop] fun N : ℕ => (N : ℝ) ^ (1 / 2 : ℝ) := by
  apply IsBigO.of_bound (2 * K)
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hs : (1 : ℝ) ≤ Real.sqrt (N : ℝ) := by
    exact (Real.le_sqrt (by norm_num) (Nat.cast_nonneg N)).mpr (by simpa using hNR)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _), ← Real.sqrt_eq_rpow]
  exact (h N).trans (by nlinarith)

theorem idealClassCharacter_sum_zero {G : Type*} [CommGroup G] [Fintype G]
    (ψ : AddChar (Additive G) ℂ) (hψ : ψ ≠ 0) :
    (∑ C : G, ψ (Additive.ofMul C)) = 0 := by
  have hsum : (∑ C : G, ψ (Additive.ofMul C)) = ∑ C : Additive G, ψ C :=
    Fintype.sum_equiv (Additive.ofMul : G ≃ Additive G) _ _ (fun _ => rfl)
  rw [hsum]
  exact AddChar.sum_eq_zero_iff_ne_zero.mpr hψ

theorem idealClassCharacterCount_bigO {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    (F : Ideal (QuadraticAlgebra ℤ d b)) (hF₀ : F ≠ ⊥) (hF₁ : F ≠ ⊤) :
    letI := quadraticOrderIsDomain hD
    ∀ ψ : AddChar (Additive (ClassGroup (QuadraticAlgebra ℤ d b))) ℂ, ψ ≠ 0 →
      (fun N => weightedIdealClassCount hD F (fun C => ψ (Additive.ofMul C)) N)
        =O[atTop] fun N : ℕ => (N : ℝ) ^ (1 / 2 : ℝ) := by
  let := quadraticOrderIsDomain hD
  let := quadraticOrderClassGroupFintype hD
  intro ψ hψ
  obtain ⟨K, hK, hbound⟩ := weightedIdealClassCount_error hD F hF₀ hF₁
    (fun C => ψ (Additive.ofMul C)) (idealClassCharacter_sum_zero ψ hψ)
  exact sqrt_error_isBigO hK hbound

end Bernays
