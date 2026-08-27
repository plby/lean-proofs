import ErdosProblems.Erdos4.FGKMTRationalExpansion
import ErdosProblems.Erdos4.IndicatorProducts
import ErdosProblems.Erdos4.AffineNormalization

/-! Exact energy main term and the algebraic transfer of finite CRT counting errors. -/

open scoped BigOperators

namespace Erdos4.FGKMT

open Classical LocalOrthogonality DivisibilityExpansion IndicatorProducts

section MainTerm

variable {P : Type*} [Fintype P] [DecidableEq P] {k : ℕ}

theorem rational_coefficient_joint_sum_eq_energy (b : ℝ) (R : ℕ) (ell : P → ℕ)
    (hell : ∀ p, (k : ℝ) < ell p) :
    (∑ a : P → Option (Fin k), ∑ c : P → Option (Fin k),
      (rationalDivisorCoefficient b R ell a * rationalDivisorCoefficient b R ell c) *
        jointDensity ell a c) = RestrictedProductNorm.energy (rationalCoefficient (k := k) b R ell) := by
  have hbase := ProductOrthogonality.mean_expansion_sq (fun p => (ell p : ℝ)) hell
    (rationalCoefficient (k := k) b R ell)
  have hexpand : ∀ s : P → Option (Fin k),
      ProductOrthogonality.expansion (fun p => (ell p : ℝ)) (rationalCoefficient b R ell) s =
        ∑ c, rationalDivisorCoefficient b R ell c * evaluation s c :=
    fun s => (rational_expansion_eq b R ell s).symm
  have hpoint : ∀ s : P → Option (Fin k),
      (∑ a, rationalDivisorCoefficient b R ell a * evaluation s a) ^ 2 =
        ∑ a, ∑ c, (rationalDivisorCoefficient b R ell a * rationalDivisorCoefficient b R ell c) *
          (evaluation s a * evaluation s c) := by
    intro s
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun c _ => by ring)
  simp_rw [hexpand, hpoint, ProductOrthogonality.mean_sum,
    ProductOrthogonality.mean_const_mul, mean_evaluation_mul ell hell] at hbase
  exact hbase

end MainTerm

variable {P Q : Type*} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q] {k : ℕ}
    (ell₀ : P → ℕ) (ell₁ : Q → ℕ)
    [∀ p, Fact (ell₀ p).Prime] [∀ q, Fact (ell₁ q).Prime]

noncomputable def maskedTranslatedPairCount (h : Fin k → ℕ) (Y p : ℕ)
    (a c : Q → Option (Fin k)) : ℝ :=
  ∑ n ∈ Finset.Icc 1 (2 * Y), translatedSmallMask ell₀ h Y p n *
    (evaluation (translatedResidueState ell₁ h Y n p) a *
      evaluation (translatedResidueState ell₁ h Y n p) c)

noncomputable def maskedTranslatedNormalizer (b : ℝ) (R : ℕ)
    (h : Fin k → ℕ) (Y p : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 (2 * Y), maskedTranslatedWeight ell₀ ell₁ b R h Y p n

theorem maskedTranslatedNormalizer_nonneg (b : ℝ) (R : ℕ)
    (h : Fin k → ℕ) (Y p : ℕ) : 0 ≤ maskedTranslatedNormalizer ell₀ ell₁ b R h Y p :=
  Finset.sum_nonneg (fun n _ => maskedTranslatedWeight_nonneg ell₀ ell₁ b R h Y p n)

theorem maskedTranslatedWeight_expansion (b : ℝ) (R : ℕ)
    (h : Fin k → ℕ) (Y p n : ℕ) :
    maskedTranslatedWeight ell₀ ell₁ b R h Y p n =
      ∑ a : Q → Option (Fin k), ∑ c : Q → Option (Fin k),
        (rationalDivisorCoefficient b R ell₁ a * rationalDivisorCoefficient b R ell₁ c) *
          (translatedSmallMask ell₀ h Y p n *
            (evaluation (translatedResidueState ell₁ h Y n p) a *
              evaluation (translatedResidueState ell₁ h Y n p) c)) := by
  have hsq : rationalTranslatedAmplitude ell₁ b R h Y p n ^ 2 =
      ∑ a : Q → Option (Fin k), ∑ c : Q → Option (Fin k),
        (rationalDivisorCoefficient b R ell₁ a * rationalDivisorCoefficient b R ell₁ c) *
          (evaluation (translatedResidueState ell₁ h Y n p) a *
            evaluation (translatedResidueState ell₁ h Y n p) c) := by
    unfold rationalTranslatedAmplitude
    rw [← rational_expansion_eq, pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun c _ => by ring)
  rw [maskedTranslatedWeight, hsq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun c _ => by ring)

theorem maskedTranslatedNormalizer_eq_pairs (b : ℝ) (R : ℕ)
    (h : Fin k → ℕ) (Y p : ℕ) :
    maskedTranslatedNormalizer ell₀ ell₁ b R h Y p =
      ∑ a : Q → Option (Fin k), ∑ c : Q → Option (Fin k),
        (rationalDivisorCoefficient b R ell₁ a * rationalDivisorCoefficient b R ell₁ c) *
          maskedTranslatedPairCount ell₀ ell₁ h Y p a c := by
  unfold maskedTranslatedNormalizer
  simp_rw [maskedTranslatedWeight_expansion]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  exact (Finset.mul_sum _ _ _).symm

theorem maskedTranslatedNormalizer_error_le (b : ℝ) (R : ℕ)
    (hell : ∀ l, (k : ℝ) < ell₁ l) (h : Fin k → ℕ) (Y p : ℕ) {α B : ℝ}
    (hcount : ∀ a c : Q → Option (Fin k),
      |maskedTranslatedPairCount ell₀ ell₁ h Y p a c - α * (2 * Y : ℕ) * jointDensity ell₁ a c| ≤ B) :
    |maskedTranslatedNormalizer ell₀ ell₁ b R h Y p -
      α * (2 * Y : ℕ) * RestrictedProductNorm.energy (rationalCoefficient (k := k) b R ell₁)| ≤
        B * (∑ a : Q → Option (Fin k), |rationalDivisorCoefficient b R ell₁ a|) ^ 2 := by
  have hid : maskedTranslatedNormalizer ell₀ ell₁ b R h Y p -
      α * (2 * Y : ℕ) * RestrictedProductNorm.energy (rationalCoefficient (k := k) b R ell₁) =
        ∑ a : Q → Option (Fin k), ∑ c : Q → Option (Fin k),
          (rationalDivisorCoefficient b R ell₁ a * rationalDivisorCoefficient b R ell₁ c) *
            (maskedTranslatedPairCount ell₀ ell₁ h Y p a c -
              α * (2 * Y : ℕ) * jointDensity ell₁ a c) := by
    rw [maskedTranslatedNormalizer_eq_pairs, ← rational_coefficient_joint_sum_eq_energy b R ell₁ hell]
    simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro c _
    ring
  rw [hid]
  exact AffineNormalization.quadratic_error_le (rationalDivisorCoefficient b R ell₁) _ hcount

end Erdos4.FGKMT
