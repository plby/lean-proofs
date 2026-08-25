import Util.Bernays.GenusCharacters
import Util.Bernays.GoodNormPrimePowers
import Util.Bernays.PrimePowerConvolution

/-!
# Genus twists of the local norm indicator and ideal coefficients
-/

open scoped Classical

namespace Bernays

noncomputable def genusLocalAF {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    AddChar (Additive (GenusGroup (QuadraticAlgebra ℤ d b))) ℂ → ArithmeticFunction ℂ :=
  letI := quadraticOrderIsDomain hD
  fun ψ => ((localParityAF (fun p => discriminantCharacter _ hD.ne p = -1)).pmul
    (coprimeAF (discriminantLevel (b ^ 2 + 4 * d)))).pmul (genusWeightAF hD ψ)

noncomputable def genusIdealAF {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    AddChar (Additive (GenusGroup (QuadraticAlgebra ℤ d b))) ℂ → ArithmeticFunction ℂ :=
  letI := quadraticOrderIsDomain hD
  fun ψ => (goodIdealNormAF hD).pmul (genusWeightAF hD ψ)

theorem genusLocalAF_isMultiplicative {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ ψ : AddChar (Additive (GenusGroup (QuadraticAlgebra ℤ d b))) ℂ,
      (genusLocalAF hD ψ).IsMultiplicative := by
  letI := quadraticOrderIsDomain hD
  intro ψ
  exact ((localParityAF_isMultiplicative _).pmul (coprimeAF_isMultiplicative _)).pmul
    (genusWeightAF_isMultiplicative hD ψ)

theorem genusIdealAF_isMultiplicative {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ ψ : AddChar (Additive (GenusGroup (QuadraticAlgebra ℤ d b))) ℂ,
      (genusIdealAF hD ψ).IsMultiplicative := by
  letI := quadraticOrderIsDomain hD
  intro ψ
  exact (goodIdealNormAF_isMultiplicative hD).pmul (genusWeightAF_isMultiplicative hD ψ)

theorem genusIdealAF_eq_coeff {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ ψ : AddChar (Additive (GenusGroup (QuadraticAlgebra ℤ d b))) ℂ,
      ⇑(genusIdealAF hD ψ) = weightedIdealNormCoeff hD (quadraticBadIdeal d b)
        (fun C => ψ (Additive.ofMul (genusMap C))) := by
  letI := quadraticOrderIsDomain hD
  intro ψ
  funext n
  rw [genusWeightedIdealNormCoeff hD]
  by_cases hn : n = 0
  · subst n
    rw [ArithmeticFunction.map_zero, goodIdealNormFiber_card_zero hD, Nat.cast_zero, mul_zero]
  · rw [genusIdealAF, ArithmeticFunction.pmul_apply, genusWeightAF_apply hD ψ n hn]
    exact mul_comm _ _

theorem genusLocalAF_split_primePower {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ ψ : AddChar (Additive (GenusGroup (QuadraticAlgebra ℤ d b))) ℂ,
    ∀ p : ℕ, p.Prime → p.Coprime (discriminantLevel (b ^ 2 + 4 * d)) →
      discriminantCharacter _ hD.ne p ≠ -1 → ∀ e : ℕ,
      genusLocalAF hD ψ (p ^ e) = ψ (Additive.ofMul (primeGenus hD p)) ^ e := by
  letI := quadraticOrderIsDomain hD
  intro ψ p hp hc hχ e
  rcases Nat.eq_zero_or_pos e with rfl | he
  · rw [pow_zero, (genusLocalAF_isMultiplicative hD ψ).1, pow_zero]
  · rw [genusLocalAF, ArithmeticFunction.pmul_apply, ArithmeticFunction.pmul_apply,
      genusWeightAF_primePower hD ψ p hp e, coprimeAF_primePower _ hp he, if_pos hc]
    change (localParity _ (p ^ e) : ℂ) * 1 * _ = _
    rw [localParity_prime_pow _ hp]
    simp only [hχ, false_and, ↓reduceIte, Complex.ofReal_one, one_mul]

theorem genusIdealAF_split_primePower {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ ψ : AddChar (Additive (GenusGroup (QuadraticAlgebra ℤ d b))) ℂ,
    ∀ p : ℕ, p.Prime → p.Coprime (discriminantLevel (b ^ 2 + 4 * d)) →
      discriminantCharacter _ hD.ne p ≠ -1 → ∀ e : ℕ,
      genusIdealAF hD ψ (p ^ e) = (e + 1 : ℕ) * ψ (Additive.ofMul (primeGenus hD p)) ^ e := by
  letI := quadraticOrderIsDomain hD
  intro ψ p hp hc hχ e
  obtain ⟨s, hs⟩ := exists_splitPrime_of_coprime_not_inert hD hp hc hχ
  have hnorm : goodIdealNormAF hD (p ^ e) = (e + 1 : ℕ) := by
    rw [← hs]
    exact goodIdealNormAF_split_primePower hD s (hs.symm ▸ hc) e
  rw [genusIdealAF, ArithmeticFunction.pmul_apply, hnorm, genusWeightAF_primePower hD ψ p hp e]

theorem genusLocalAF_inert_primePower {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ ψ : AddChar (Additive (GenusGroup (QuadraticAlgebra ℤ d b))) ℂ,
    ∀ p : ℕ, p.Prime → p.Coprime (discriminantLevel (b ^ 2 + 4 * d)) →
      discriminantCharacter _ hD.ne p = -1 → ∀ e : ℕ,
      genusLocalAF hD ψ (p ^ e) = if Even e then 1 else 0 := by
  letI := quadraticOrderIsDomain hD
  intro ψ p hp hc hχ e
  rcases Nat.eq_zero_or_pos e with rfl | he
  · rw [pow_zero, (genusLocalAF_isMultiplicative hD ψ).1, if_pos Even.zero]
  · rw [genusLocalAF, ArithmeticFunction.pmul_apply, ArithmeticFunction.pmul_apply,
      genusWeightAF_primePower hD ψ p hp e, coprimeAF_primePower _ hp he, if_pos hc]
    change (localParity _ (p ^ e) : ℂ) * 1 * _ = _
    rw [localParity_prime_pow _ hp]
    by_cases hE : Even e
    · rw [if_neg (by simpa only [hχ, true_and] using Nat.not_odd_iff_even.mpr hE),
        if_pos hE, Complex.ofReal_one, one_mul, one_mul]
      exact pow_even_eq_one_of_sq_eq_one (genusChar_sq ψ _) hE
    · simp only [hχ, true_and, Nat.not_even_iff_odd.mp hE, ↓reduceIte, Complex.ofReal_zero,
        zero_mul, hE]

theorem genusIdealAF_inert_primePower {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ ψ : AddChar (Additive (GenusGroup (QuadraticAlgebra ℤ d b))) ℂ,
    ∀ p : ℕ, p.Prime → p.Coprime (discriminantLevel (b ^ 2 + 4 * d)) →
      discriminantCharacter _ hD.ne p = -1 → ∀ e : ℕ,
      genusIdealAF hD ψ (p ^ e) = if Even e then 1 else 0 := by
  letI := quadraticOrderIsDomain hD
  intro ψ p hp hc hχ e
  rw [genusIdealAF, ArithmeticFunction.pmul_apply, goodIdealNormAF_inert_primePower hD hp hc hχ,
    genusWeightAF_primePower hD ψ p hp e]
  by_cases hE : Even e
  · rw [if_pos hE, one_mul]
    exact pow_even_eq_one_of_sq_eq_one (genusChar_sq ψ _) hE
  · rw [if_neg hE, zero_mul]

theorem genusLocalAF_bad_primePower {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ ψ : AddChar (Additive (GenusGroup (QuadraticAlgebra ℤ d b))) ℂ,
    ∀ p : ℕ, p.Prime → ¬ p.Coprime (discriminantLevel (b ^ 2 + 4 * d)) → ∀ e : ℕ,
      genusLocalAF hD ψ (p ^ e) = if e = 0 then 1 else 0 := by
  letI := quadraticOrderIsDomain hD
  intro ψ p hp hc e
  rcases Nat.eq_zero_or_pos e with rfl | he
  · rw [pow_zero, (genusLocalAF_isMultiplicative hD ψ).1, if_pos rfl]
  · rw [genusLocalAF, ArithmeticFunction.pmul_apply, ArithmeticFunction.pmul_apply,
      coprimeAF_primePower _ hp he, if_neg hc, mul_zero, zero_mul, if_neg he.ne']

theorem genusIdealAF_bad_primePower {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ ψ : AddChar (Additive (GenusGroup (QuadraticAlgebra ℤ d b))) ℂ,
    ∀ p : ℕ, ¬ p.Coprime (discriminantLevel (b ^ 2 + 4 * d)) → ∀ e : ℕ,
      genusIdealAF hD ψ (p ^ e) = if e = 0 then 1 else 0 := by
  letI := quadraticOrderIsDomain hD
  intro ψ p hc e
  rcases Nat.eq_zero_or_pos e with rfl | he
  · rw [pow_zero, (genusIdealAF_isMultiplicative hD ψ).1, if_pos rfl]
  · rw [genusIdealAF, ArithmeticFunction.pmul_apply,
      goodIdealNormAF_bad_primePower hD hc he, zero_mul, if_neg he.ne']

end Bernays
