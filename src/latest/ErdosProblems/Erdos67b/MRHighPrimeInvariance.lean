import ErdosProblems.Erdos67b.MRCofactorPerron
import ErdosProblems.Erdos67b.MRGSA9GeneralizedMangoldt
import ErdosProblems.Erdos67b.MRGSA10HighMangoldtSupport

/-!
# Common high-prime factors under low-prime modification

Prime deletion and denominator scaling supported below the splitting
threshold leave the high arithmetic function and its generalized
Mangoldt coefficient unchanged. No assertion of multiplicativity is
made for a typical-set restriction.
-/

namespace Erdos67b

open MRHalaszBands

noncomputable section

theorem mrHigh_primeBandCoefficient_eq (f : ℕ → ℂ)
    (P : ℕ → Prop) [DecidablePred P] (y : ℕ)
    (hsmall : ∀ p, ¬ P p → p ≤ y) :
    gsA9High (primeBandCoefficient f P) y = gsA9High f y := by
  unfold gsA9High
  rw [primeBandCoefficient_nested]
  apply primeBandCoefficient_congr_pred
  intro p
  constructor
  · exact fun hp ↦ hp.2
  · intro hp
    refine ⟨?_, hp⟩
    by_contra hP
    exact hp (hsmall p hP)

theorem mrPrimeDivisorCount_high_eq_zero
    {A : Finset ℕ} (hA : ∀ p ∈ A, p.Prime) {y n : ℕ}
    (hsmall : ∀ p ∈ A, p ≤ y)
    (hn : PrimeSupported (fun p ↦ ¬ p ≤ y) n) :
    primeDivisorCount A n = 0 := by
  have hempty : primeDivisorSet A n = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    have hdata := mem_primeDivisorSet.mp hp
    have hpf : p ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hA p hdata.1, hdata.2, hn.1⟩
    exact hn.2 p hpf (hsmall p hdata.1)
  simp only [primeDivisorCount, hempty, Finset.card_empty]

theorem mrHigh_primeScaledCoefficient_eq
    (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime) (f : ℕ → ℂ) (y : ℕ)
    (hsmall : ∀ p ∈ A, p ≤ y) (u : ℝ) :
    gsA9High (mrPrimeScaledCoefficient A f u) y = gsA9High f y := by
  funext n
  unfold gsA9High primeBandCoefficient
  by_cases hn : PrimeSupported (fun p ↦ ¬ p ≤ y) n
  · rw [if_pos hn, if_pos hn]
    simp only [mrPrimeScaledCoefficient, mrPrimeDivisorCount_high_eq_zero hA hsmall hn,
      pow_zero, Complex.ofReal_one, mul_one]
  · rw [if_neg hn, if_neg hn]

theorem mrHighArithmetic_congr_of_high_eq
    {f g : ℕ → ℂ} {y : ℕ} (hhigh : gsA9High f y = gsA9High g y) :
    gsA9HighArithmetic f y = gsA9HighArithmetic g y := by
  ext n
  simp only [gsA9HighArithmetic, hhigh]

theorem mrGeneralizedMangoldt_congr
    {a b : ArithmeticFunction ℂ} (hab : a = b)
    (ha : Invertible (a 1)) (hb : Invertible (b 1)) :
    gsGeneralizedMangoldt a ha = gsGeneralizedMangoldt b hb := by
  subst b
  have hh : ha = hb := Subsingleton.elim _ _
  rw [hh]

theorem mrHighGeneralizedMangoldt_congr_of_high_eq
    {f g : ℕ → ℂ} (hf : IsMultiplicativeOnPositiveNat f)
    (hg : IsMultiplicativeOnPositiveNat g) {y : ℕ}
    (hhigh : gsA9High f y = gsA9High g y) :
    gsA9HighGeneralizedMangoldt hf y = gsA9HighGeneralizedMangoldt hg y := by
  unfold gsA9HighGeneralizedMangoldt
  exact mrGeneralizedMangoldt_congr (mrHighArithmetic_congr_of_high_eq hhigh) _ _

theorem mrHighArithmetic_primeBandCoefficient_eq
    (f : ℕ → ℂ) (P : ℕ → Prop) [DecidablePred P] (y : ℕ)
    (hsmall : ∀ p, ¬ P p → p ≤ y) :
    gsA9HighArithmetic (primeBandCoefficient f P) y = gsA9HighArithmetic f y :=
  mrHighArithmetic_congr_of_high_eq (mrHigh_primeBandCoefficient_eq f P y hsmall)

theorem mrHighArithmetic_primeScaledCoefficient_eq
    (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime) (f : ℕ → ℂ) (y : ℕ)
    (hsmall : ∀ p ∈ A, p ≤ y) (u : ℝ) :
    gsA9HighArithmetic (mrPrimeScaledCoefficient A f u) y = gsA9HighArithmetic f y :=
  mrHighArithmetic_congr_of_high_eq (mrHigh_primeScaledCoefficient_eq A hA f y hsmall u)

theorem mrHighArithmetic_scaled_mask_eq
    (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime)
    (f : ℕ → ℂ) (P : ℕ → Prop) [DecidablePred P] (y : ℕ)
    (hAsmall : ∀ p ∈ A, p ≤ y) (hPsmall : ∀ p, ¬ P p → p ≤ y) (u : ℝ) :
    gsA9HighArithmetic (mrPrimeScaledCoefficient A (primeBandCoefficient f P) u) y =
      gsA9HighArithmetic f y := by
  rw [mrHighArithmetic_primeScaledCoefficient_eq A hA _ y hAsmall u,
    mrHighArithmetic_primeBandCoefficient_eq f P y hPsmall]

theorem mrHighGeneralizedMangoldt_scaled_mask_eq
    (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime)
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (P : ℕ → Prop) [DecidablePred P] (y : ℕ)
    (hAsmall : ∀ p ∈ A, p ≤ y) (hPsmall : ∀ p, ¬ P p → p ≤ y) (u : ℝ) :
    gsA9HighGeneralizedMangoldt
      (mrPrimeScaledCoefficient_isMultiplicative hA
        (primeBandCoefficient_isMultiplicativeOnPositiveNat hmul P) u) y =
      gsA9HighGeneralizedMangoldt hmul y := by
  unfold gsA9HighGeneralizedMangoldt
  exact mrGeneralizedMangoldt_congr
    (mrHighArithmetic_scaled_mask_eq A hA f P y hAsmall hPsmall u) _ _

end

end Erdos67b
