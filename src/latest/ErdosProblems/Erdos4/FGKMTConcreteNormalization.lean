import ErdosProblems.Erdos4.FGKMTTranslatedResidues
import ErdosProblems.Erdos4.FGKMTTranslatedMaskResidues
import ErdosProblems.Erdos4.FGKMTAllowedResidueCount
import ErdosProblems.Erdos4.FGKMTRationalNormalization

/-! Concrete CRT normalization of the actual translated rational sieve weights. -/

open scoped BigOperators

namespace Erdos4.FGKMT

open Classical DivisorCoefficients DivisibilityExpansion IndicatorProducts ProductCharacterEncoding

variable {P Q : Type*} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q] {k : ℕ}
    (ell₀ : P → ℕ) (ell₁ : Q → ℕ)
    [∀ l, Fact (ell₀ l).Prime] [∀ l, Fact (ell₁ l).Prime]

noncomputable def maskedTranslatedLabelCount (h : Fin k → ℕ) (Y p : ℕ)
    (a : Q → Option (Fin k)) : ℝ :=
  ∑ n ∈ Finset.Icc 1 (2 * Y), translatedSmallMask ell₀ h Y p n *
    evaluation (translatedResidueState ell₁ h Y n p) a

theorem maskedTranslatedLabelCount_error
    (hcop₀ : Pairwise (fun l r => (ell₀ l).Coprime (ell₀ r)))
    (hcop₁ : Pairwise (fun l r => (ell₁ l).Coprime (ell₁ r)))
    (hcross : ∀ l, (modulus ell₀).Coprime (ell₁ l))
    (h : Fin k → ℕ) (hinj : ∀ l, Function.Injective (fun i => (h i : ZMod (ell₁ l))))
    (Y p : ℕ) (hp₀ : ∀ l, (p : ZMod (ell₀ l)) ≠ 0) (hp₁ : p.Coprime (modulus ell₁))
    (a : Q → Option (Fin k)) :
    |maskedTranslatedLabelCount ell₀ ell₁ h Y p a -
      smallProductDensity ell₀ (fun l i => (h i : ZMod (ell₀ l))) * (2 * Y : ℕ) /
        totalDivisor ell₁ a| ≤
      smallProductDensity ell₀ (fun l i => (h i : ZMod (ell₀ l))) * (modulus ell₀ : ℝ) := by
  obtain ⟨r, hr⟩ := translated_evaluation_is_residue ell₁ hcop₁ h hinj Y p hp₁ a
  let S := translatedAllowedResidues ell₀ h Y p
  have heq : maskedTranslatedLabelCount ell₀ ell₁ h Y p a =
      allowedResidueCount (2 * Y) (modulus ell₀) (totalDivisor ell₁ a) r S := by
    unfold maskedTranslatedLabelCount allowedResidueCount
    apply Finset.sum_congr rfl
    intro n _
    rw [translatedSmallMask_eq_allowed, hr n]
    by_cases hm : n % modulus ell₀ ∈ S <;> by_cases hd : n ≡ r [MOD totalDivisor ell₁ a] <;>
      simp only [S] at hm ⊢ <;> simp only [hm, hd, true_and, false_and, if_true, if_false,
        one_mul, zero_mul]
  have hM : 0 < modulus ell₀ := Finset.prod_pos (fun l _ => (Fact.out : (ell₀ l).Prime).pos)
  have hd : 0 < totalDivisor ell₁ a := totalDivisor_pos ell₁
    (fun l => (Fact.out : (ell₁ l).Prime).pos) a
  have hcop : (modulus ell₀).Coprime (totalDivisor ell₁ a) :=
    LabelResidueClass.coprime_totalDivisor ell₁ (modulus ell₀) hcross a
  have hSden : (S.card : ℝ) / modulus ell₀ =
      smallProductDensity ell₀ (fun l i => (h i : ZMod (ell₀ l))) :=
    translatedAllowedResidues_density ell₀ hcop₀ h Y p hp₀
  have hScard : (S.card : ℝ) =
      smallProductDensity ell₀ (fun l i => (h i : ZMod (ell₀ l))) * (modulus ell₀ : ℝ) :=
    translatedAllowedResidues_card ell₀ hcop₀ h Y p hp₀
  have hh := allowedResidueCount_density_error (2 * Y) (modulus ell₀) (totalDivisor ell₁ a)
    r S hM hd (translatedAllowedResidues_subset ell₀ h Y p) hcop
  rw [← heq, hSden, hScard] at hh
  exact hh

theorem maskedTranslatedPairCount_error
    (hcop₀ : Pairwise (fun l r => (ell₀ l).Coprime (ell₀ r)))
    (hcop₁ : Pairwise (fun l r => (ell₁ l).Coprime (ell₁ r)))
    (hcross : ∀ l, (modulus ell₀).Coprime (ell₁ l))
    (h : Fin k → ℕ) (hinj : ∀ l, Function.Injective (fun i => (h i : ZMod (ell₁ l))))
    (Y p : ℕ) (hp₀ : ∀ l, (p : ZMod (ell₀ l)) ≠ 0) (hp₁ : p.Coprime (modulus ell₁))
    (a c : Q → Option (Fin k)) :
    |maskedTranslatedPairCount ell₀ ell₁ h Y p a c -
      smallProductDensity ell₀ (fun l i => (h i : ZMod (ell₀ l))) * (2 * Y : ℕ) *
        jointDensity ell₁ a c| ≤
      smallProductDensity ell₀ (fun l i => (h i : ZMod (ell₀ l))) * (modulus ell₀ : ℝ) := by
  unfold maskedTranslatedPairCount
  simp_rw [evaluation_mul, jointDensity_eq]
  by_cases hac : CompatibleLabels a c
  · simp only [if_pos hac]
    simpa only [maskedTranslatedLabelCount, div_eq_mul_inv] using
      maskedTranslatedLabelCount_error ell₀ ell₁ hcop₀ hcop₁ hcross h hinj Y p hp₀ hp₁
        (joinLabels a c)
  · simp only [if_neg hac, mul_zero, Finset.sum_const_zero, sub_zero, abs_zero]
    exact mul_nonneg (smallProductDensity_nonneg ell₀ _) (Nat.cast_nonneg _)

theorem maskedTranslatedNormalizer_crt_error (b : ℝ) (R : ℕ)
    (hell : ∀ l, (k : ℝ) < ell₁ l)
    (hcop₀ : Pairwise (fun l r => (ell₀ l).Coprime (ell₀ r)))
    (hcop₁ : Pairwise (fun l r => (ell₁ l).Coprime (ell₁ r)))
    (hcross : ∀ l, (modulus ell₀).Coprime (ell₁ l))
    (h : Fin k → ℕ) (hinj : ∀ l, Function.Injective (fun i => (h i : ZMod (ell₁ l))))
    (Y p : ℕ) (hp₀ : ∀ l, (p : ZMod (ell₀ l)) ≠ 0) (hp₁ : p.Coprime (modulus ell₁)) :
    |maskedTranslatedNormalizer ell₀ ell₁ b R h Y p -
      smallProductDensity ell₀ (fun l i => (h i : ZMod (ell₀ l))) * (2 * Y : ℕ) *
        RestrictedProductNorm.energy (rationalCoefficient (k := k) b R ell₁)| ≤
      (smallProductDensity ell₀ (fun l i => (h i : ZMod (ell₀ l))) * (modulus ell₀ : ℝ)) *
        (∑ a : Q → Option (Fin k), |rationalDivisorCoefficient b R ell₁ a|) ^ 2 :=
  maskedTranslatedNormalizer_error_le ell₀ ell₁ b R hell h Y p
    (maskedTranslatedPairCount_error ell₀ ell₁ hcop₀ hcop₁ hcross h hinj Y p hp₀ hp₁)

theorem maskedTranslatedNormalizer_tail_error {b : ℝ} (hb : 0 ≤ b) (R : ℕ)
    (hell : ∀ l, k + 2 ≤ ell₁ l)
    (htail : (k : ℝ) * LocalIndicatorExpansion.rowCost k * ∑ l, 1 / (ell₁ l : ℝ) ^ 2 ≤ 1)
    (hcop₀ : Pairwise (fun l r => (ell₀ l).Coprime (ell₀ r)))
    (hcop₁ : Pairwise (fun l r => (ell₁ l).Coprime (ell₁ r)))
    (hcross : ∀ l, (modulus ell₀).Coprime (ell₁ l))
    (h : Fin k → ℕ) (hinj : ∀ l, Function.Injective (fun i => (h i : ZMod (ell₁ l))))
    (Y p : ℕ) (hp₀ : ∀ l, (p : ZMod (ell₀ l)) ≠ 0) (hp₁ : p.Coprime (modulus ell₁)) :
    |maskedTranslatedNormalizer ell₀ ell₁ b R h Y p -
      smallProductDensity ell₀ (fun l i => (h i : ZMod (ell₀ l))) * (2 * Y : ℕ) *
        RestrictedProductNorm.energy (rationalCoefficient (k := k) b R ell₁)| ≤
      (smallProductDensity ell₀ (fun l i => (h i : ZMod (ell₀ l))) * (modulus ell₀ : ℝ)) *
        (Real.exp 1 ^ 2 * (R : ℝ) ^ 4) := by
  have hmass := (rational_sum_abs_coefficient_le_mass hb R ell₁ hell).trans
    (CutoffMass.mass_le_of_small_tail R ell₁ (fun l => by have := hell l; omega)
      (LocalIndicatorExpansion.rowCost_nonneg k) htail)
  have hsq := pow_le_pow_left₀
    (Finset.sum_nonneg (fun a _ => abs_nonneg (rationalDivisorCoefficient b R ell₁ a))) hmass 2
  rw [mul_pow, ← pow_mul] at hsq
  exact (maskedTranslatedNormalizer_crt_error ell₀ ell₁ b R
    (fun l => by exact_mod_cast (show k < ell₁ l by have := hell l; omega))
    hcop₀ hcop₁ hcross h hinj Y p hp₀ hp₁).trans
      (mul_le_mul_of_nonneg_left hsq
        (mul_nonneg (smallProductDensity_nonneg ell₀ _) (Nat.cast_nonneg _)))

theorem maskedTranslatedNormalizer_bounds {b : ℝ} (hb : 0 ≤ b) {R : ℕ} (hR : 1 ≤ R)
    (hell : ∀ l, k + 2 ≤ ell₁ l)
    (htail : (k : ℝ) * LocalIndicatorExpansion.rowCost k * ∑ l, 1 / (ell₁ l : ℝ) ^ 2 ≤ 1)
    (hcop₀ : Pairwise (fun l r => (ell₀ l).Coprime (ell₀ r)))
    (hcop₁ : Pairwise (fun l r => (ell₁ l).Coprime (ell₁ r)))
    (hcross : ∀ l, (modulus ell₀).Coprime (ell₁ l))
    (h : Fin k → ℕ) (hinj : ∀ l, Function.Injective (fun i => (h i : ZMod (ell₁ l))))
    (Y p : ℕ) (hp₀ : ∀ l, (p : ZMod (ell₀ l)) ≠ 0) (hp₁ : p.Coprime (modulus ell₁))
    (hbudget : (modulus ell₀ : ℝ) * (Real.exp 1 ^ 2 * (R : ℝ) ^ 4) ≤ Y) :
    let α := smallProductDensity ell₀ (fun l i => (h i : ZMod (ell₀ l)))
    let E := RestrictedProductNorm.energy (rationalCoefficient (k := k) b R ell₁)
    α * Y * E ≤ maskedTranslatedNormalizer ell₀ ell₁ b R h Y p ∧
      maskedTranslatedNormalizer ell₀ ell₁ b R h Y p ≤ 3 * (α * Y * E) := by
  dsimp only
  let α := smallProductDensity ell₀ (fun l i => (h i : ZMod (ell₀ l)))
  let E := RestrictedProductNorm.energy (rationalCoefficient (k := k) b R ell₁)
  have hα : 0 ≤ α := smallProductDensity_nonneg ell₀ _
  have hE : 1 ≤ E := one_le_rationalCoefficient_energy b hR ell₁
  have he := maskedTranslatedNormalizer_tail_error ell₀ ell₁ hb R hell htail
    hcop₀ hcop₁ hcross h hinj Y p hp₀ hp₁
  have hbnd : (α * (modulus ell₀ : ℝ)) * (Real.exp 1 ^ 2 * (R : ℝ) ^ 4) ≤
      α * Y * E := by
    calc
      _ = α * ((modulus ell₀ : ℝ) * (Real.exp 1 ^ 2 * (R : ℝ) ^ 4)) := by ring
      _ ≤ α * Y := mul_le_mul_of_nonneg_left hbudget hα
      _ ≤ α * Y * E := by
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hE (mul_nonneg hα (Nat.cast_nonneg Y))
  have herr : |maskedTranslatedNormalizer ell₀ ell₁ b R h Y p - 2 * (α * Y * E)| ≤
      α * Y * E := by
    have hh := he.trans hbnd
    change |maskedTranslatedNormalizer ell₀ ell₁ b R h Y p - α * (2 * Y : ℕ) * E| ≤
      α * Y * E at hh
    have hmain : α * (2 * Y : ℕ) * E = 2 * (α * Y * E) := by
      rw [Nat.cast_mul, Nat.cast_ofNat]
      ring
    rwa [hmain] at hh
  have hh := abs_le.mp herr
  change α * Y * E ≤ _ ∧ _ ≤ 3 * (α * Y * E)
  constructor <;> linarith [hh.1, hh.2]

theorem maskedTranslatedNormalizer_pos_of_lower (b : ℝ) {R : ℕ} (hR : 1 ≤ R)
    (h : Fin k → ℕ)
    (hadm : ∀ l, ∃ x, SmallPrimeGood (fun i => (h i : ZMod (ell₀ l))) x)
    {Y : ℕ} (hY : 1 ≤ Y) (p : ℕ)
    (hlower : smallProductDensity ell₀ (fun l i => (h i : ZMod (ell₀ l))) * Y *
      RestrictedProductNorm.energy (rationalCoefficient (k := k) b R ell₁) ≤
        maskedTranslatedNormalizer ell₀ ell₁ b R h Y p) :
    0 < maskedTranslatedNormalizer ell₀ ell₁ b R h Y p := by
  have hα := smallProductDensity_pos ell₀ _ hadm
  have hE := one_le_rationalCoefficient_energy (k := k) b hR ell₁
  have hYr : (0 : ℝ) < Y := by exact_mod_cast (show 0 < Y by omega)
  exact (mul_pos (mul_pos hα hYr) (lt_of_lt_of_le zero_lt_one hE)).trans_le hlower

end Erdos4.FGKMT
