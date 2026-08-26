import ErdosProblems.Erdos421.DirichletArithmeticCoefficients
import ErdosProblems.Erdos421.HigherHalasz

/-! # Higher-moment and Halász bounds for actual vertical Dirichlet polynomials -/

namespace Erdos421

open Complex

noncomputable def dirichletMomentEnergy (M U k : ℕ) : ℝ :=
  ((M : ℝ)⁻¹) ^ (2 * k) * (U ^ k : ℕ) * (1 + Real.log (U ^ k : ℕ)) ^ (k ^ 2)

theorem dirichletPolynomial_higher_large_values (S : Finset ℕ) (a : ℕ → ℂ)
    {M U : ℕ} (hM : 1 ≤ M) (hS : ∀ n ∈ S, M ≤ n ∧ n ≤ U)
    (ha : ∀ n ∈ S, ‖a n‖ ≤ 1) {σ : ℝ} (hσ : 1 ≤ σ) (k : ℕ)
    (F : Finset ℕ) (t : ℕ → ℝ) {u v V : ℝ} (huv : u ≤ v)
    (ht : ∀ i ∈ F, u ≤ t i ∧ t i ≤ v)
    (hsep : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → 1 ≤ |t i - t j|)
    (hV : 0 ≤ V) (hlarge : ∀ i ∈ F, V ≤ ‖dirichletPolynomial S a (σ + t i * I)‖) :
    F.card * V ^ (2 * k) ≤ (2 + (Real.log (U ^ k : ℕ)) ^ 2) *
      (v + 1 - u + 4 * (U ^ k : ℕ) * (1 + Real.log (U ^ k : ℕ))) *
        dirichletMomentEnergy M U k := by
  let f := dirichletArithmeticCoefficients S a σ
  have hf : SupportedThrough f U :=
    dirichletArithmeticCoefficients_supported S a σ (fun n hn ↦ (hS n hn).2)
  have hc : ∀ n, n ≠ 0 → ‖f n‖ ≤ (M : ℝ)⁻¹ := fun n _ ↦
    dirichletArithmeticCoefficients_norm_le S a hM (fun n hn ↦ (hS n hn).1) ha hσ n
  have hpos : ∀ n ∈ S, 0 < n ∧ n ≤ U := fun n hn ↦
    ⟨by have := (hS n hn).1; omega, (hS n hn).2⟩
  have ht' : ∀ i ∈ F, -v ≤ -t i ∧ -t i ≤ -u := fun i hi ↦
    ⟨neg_le_neg (ht i hi).2, neg_le_neg (ht i hi).1⟩
  have hsep' : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → 1 ≤ |-t i - -t j| := by
    intro i hi j hj hij
    simpa only [neg_sub_neg, abs_sub_comm] using hsep i hi j hj hij
  have hlarge' : ∀ i ∈ F,
      V ≤ ‖exponentialSum (Finset.Icc 1 U) f (fun n ↦ Real.log n) (-t i)‖ := by
    intro i hi
    rw [← dirichletPolynomial_eq_arithmetic_exponential S a hpos σ (t i)]
    exact hlarge i hi
  have hb := finite_dirichlet_higher_large_values_bound f hf
    (by positivity : 0 ≤ (M : ℝ)⁻¹) hc k F (fun i ↦ -t i) (neg_le_neg huv) ht' hsep' hV hlarge'
  rw [show -u + 1 - -v = v + 1 - u by ring] at hb
  exact hb

theorem dirichletPolynomial_higher_halasz (S : Finset ℕ) (a : ℕ → ℂ)
    {M U : ℕ} (hM : 1 ≤ M) (hS : ∀ n ∈ S, M ≤ n ∧ n ≤ U)
    (ha : ∀ n ∈ S, ‖a n‖ ≤ 1) {σ : ℝ} (hσ : 1 ≤ σ) (k : ℕ) {K : ℕ}
    (hK : 0 < K) (hUK : U ^ k < 2 ^ K)
    (F : Finset ℕ) (t : ℕ → ℝ) {u v V : ℝ} (huv : u ≤ v)
    (ht : ∀ i ∈ F, u ≤ t i ∧ t i ≤ v)
    (hsep : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → 1 ≤ |t i - t j|)
    (hV : 0 < V) (hlarge : ∀ i ∈ F, V ≤ ‖dirichletPolynomial S a (σ + t i * I)‖) :
    (F.card : ℝ) ≤ 10240 * K * (2 ^ K : ℕ) * Real.log ((2 ^ K : ℕ) + 2 : ℝ) *
      (dirichletMomentEnergy M U k / (V ^ k / K) ^ 2 +
        1280 ^ 2 * (dirichletMomentEnergy M U k) ^ 3 * (v - u) / (V ^ k / K) ^ 6) := by
  let f := dirichletArithmeticCoefficients S a σ
  have hf : SupportedThrough f U :=
    dirichletArithmeticCoefficients_supported S a σ (fun n hn ↦ (hS n hn).2)
  have hc : ∀ n, n ≠ 0 → ‖f n‖ ≤ (M : ℝ)⁻¹ := fun n _ ↦
    dirichletArithmeticCoefficients_norm_le S a hM (fun n hn ↦ (hS n hn).1) ha hσ n
  have hpos : ∀ n ∈ S, 0 < n ∧ n ≤ U := fun n hn ↦
    ⟨by have := (hS n hn).1; omega, (hS n hn).2⟩
  have ht' : ∀ i ∈ F, -v ≤ -t i ∧ -t i ≤ -u := fun i hi ↦
    ⟨neg_le_neg (ht i hi).2, neg_le_neg (ht i hi).1⟩
  have hsep' : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → 1 ≤ |-t i - -t j| := by
    intro i hi j hj hij
    simpa only [neg_sub_neg, abs_sub_comm] using hsep i hi j hj hij
  have hlarge' : ∀ i ∈ F,
      V ≤ ‖exponentialSum (Finset.Icc 1 U) f (fun n ↦ Real.log n) (-t i)‖ := by
    intro i hi
    rw [← dirichletPolynomial_eq_arithmetic_exponential S a hpos σ (t i)]
    exact hlarge i hi
  have hb := finite_dirichlet_higher_halasz_bound f hf
    (by positivity : 0 ≤ (M : ℝ)⁻¹) hc k hK hUK F (fun i ↦ -t i)
    (neg_le_neg huv) ht' hsep' hV hlarge'
  dsimp only at hb
  rw [show -u - -v = v - u by ring] at hb
  exact hb

end Erdos421
