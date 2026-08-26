/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Counting the prime-exponent profiles available to each arithmetic-frame tag.
Informal source: BBMST Lemma 5.3 and Section 8.3 of the selected writeup.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.PrimeProfiles

namespace Erdos1189

open Finset

abbrev OtherPrime {N : ℕ} (c : PrimeCoordinate N) := {p : N.primeFactors // p ≠ c.1}

abbrev ArithmeticProfile {N : ℕ} (rank : PrimeCoordinate N → ℕ) (c : PrimeCoordinate N) :=
  (p : OtherPrime c) → Fin (precedingExponent rank c p.val + 1)

def ArithmeticProfile.exponents {N : ℕ} {rank : PrimeCoordinate N → ℕ}
    {c : PrimeCoordinate N} (F : ArithmeticProfile rank c) (p : N.primeFactors) : ℕ :=
  if hp : p = c.1 then c.2.val + 1 else (F ⟨p, hp⟩).val

def ArithmeticProfile.modulus {N : ℕ} {rank : PrimeCoordinate N → ℕ}
    {c : PrimeCoordinate N} (F : ArithmeticProfile rank c) : ℕ :=
  primePowerProfile N F.exponents

lemma ArithmeticProfile.exponents_self {N : ℕ} {rank : PrimeCoordinate N → ℕ}
    {c : PrimeCoordinate N} (F : ArithmeticProfile rank c) :
    F.exponents c.1 = c.2.val + 1 := by simp [exponents]

lemma ArithmeticProfile.exponents_other {N : ℕ} {rank : PrimeCoordinate N → ℕ}
    {c : PrimeCoordinate N} (F : ArithmeticProfile rank c) (p : OtherPrime c) :
    F.exponents p.val = (F p).val := by simp [exponents, p.property]

lemma ArithmeticProfile.exponents_le {N : ℕ} {rank : PrimeCoordinate N → ℕ}
    {c : PrimeCoordinate N} (F : ArithmeticProfile rank c) (p : N.primeFactors) :
    F.exponents p ≤ N.factorization p := by
  by_cases hp : p = c.1
  · subst p
    rw [F.exponents_self]
    exact c.2.isLt
  · have hF := (F ⟨p, hp⟩).isLt
    dsimp only at hF
    have hpre := precedingExponent_le rank c p
    simp only [exponents, dif_neg hp]
    omega

lemma ArithmeticProfile.modulus_injective {N : ℕ} (rank : PrimeCoordinate N → ℕ)
    (c : PrimeCoordinate N) : Function.Injective (@ArithmeticProfile.modulus N rank c) := by
  intro F G h
  have he : F.exponents = G.exponents := primePowerProfile_injective N h
  funext p
  apply Fin.ext
  have hp := congrFun he p.val
  simpa only [exponents_other] using hp

lemma ArithmeticProfile.modulus_dvd {N : ℕ} (hN : N ≠ 0)
    {rank : PrimeCoordinate N → ℕ} {c : PrimeCoordinate N} (F : ArithmeticProfile rank c) :
    F.modulus ∣ N := primePowerProfile_dvd hN F.exponents_le

lemma ArithmeticProfile.modulus_factorization {N : ℕ} {rank : PrimeCoordinate N → ℕ}
    {c : PrimeCoordinate N} (F : ArithmeticProfile rank c) (p : N.primeFactors) :
    F.modulus.factorization p = F.exponents p :=
  primePowerProfile_factorization N F.exponents p

lemma arithmeticRank_le {N : ℕ} {rank : PrimeCoordinate N → ℕ}
    (hrank : IsArithmeticRank rank) {i c : PrimeCoordinate N}
    (hip : i.1 = c.1) (hie : i.2.val ≤ c.2.val) : i = c ∨ rank i < rank c := by
  cases i with
  | mk p e =>
      cases c with
      | mk q f =>
          dsimp at hip hie
          subst q
          rcases hie.eq_or_lt with he | he
          · left
            have hef : e = f := Fin.ext he
            subst f
            rfl
          · exact Or.inr (hrank p he)

lemma ArithmeticProfile.modulus_ordered {N : ℕ} {rank : PrimeCoordinate N → ℕ}
    (hrank : IsArithmeticRank rank) {c : PrimeCoordinate N} (F : ArithmeticProfile rank c)
    (i : PrimeCoordinate N) (hi : i.2.val < F.modulus.factorization i.1) :
    i = c ∨ rank i < rank c := by
  rw [F.modulus_factorization] at hi
  by_cases hip : i.1 = c.1
  · have hei : F.exponents i.1 = c.2.val + 1 := by
      rw [hip, F.exponents_self]
    rw [hei] at hi
    exact arithmeticRank_le hrank hip (by omega)
  · have hei : F.exponents i.1 = (F ⟨i.1, hip⟩).val := by simp [exponents, hip]
    rw [hei] at hi
    have hF := (F ⟨i.1, hip⟩).isLt
    dsimp only at hF
    exact Or.inr ((lt_precedingExponent_iff hrank c i.1 i.2).mp (by omega))

lemma ArithmeticProfile.modulus_admissible {N : ℕ} (hN : N ≠ 0)
    {rank : PrimeCoordinate N → ℕ} (hrank : IsArithmeticRank rank)
    {c : PrimeCoordinate N} (F : ArithmeticProfile rank c) (hcenter : F.modulus ≠ N) :
    F.modulus ∈ admissibleFrameModuli rank c := by
  apply mem_admissibleFrameModuli.mpr
  refine ⟨F.modulus_dvd hN, hN, hcenter, ?_, F.modulus_ordered hrank⟩
  apply (Nat.prime_of_mem_primeFactors c.1.2).pow_dvd_iff_le_factorization
    (primePowerProfile_ne_zero N F.exponents) |>.mpr
  rw [primePowerProfile_factorization, F.exponents_self]

def profileModuli {N : ℕ} (rank : PrimeCoordinate N → ℕ) (c : PrimeCoordinate N) :
    Finset ℕ := univ.image (@ArithmeticProfile.modulus N rank c)

lemma card_profileModuli {N : ℕ} (rank : PrimeCoordinate N → ℕ) (c : PrimeCoordinate N) :
    (profileModuli rank c).card =
      ∏ p : OtherPrime c, (precedingExponent rank c p.val + 1) := by
  rw [profileModuli, card_image_of_injective _ (ArithmeticProfile.modulus_injective rank c),
    card_univ, Fintype.card_pi]
  simp only [Fintype.card_fin]

theorem profile_count_le_admissible_add_one {N : ℕ} (hN : N ≠ 0)
    {rank : PrimeCoordinate N → ℕ} (hrank : IsArithmeticRank rank) (c : PrimeCoordinate N) :
    (∏ p : OtherPrime c, (precedingExponent rank c p.val + 1)) ≤
      (admissibleFrameModuli rank c).card + 1 := by
  have hsub : (profileModuli rank c).erase N ⊆ admissibleFrameModuli rank c := by
    intro d hd
    obtain ⟨hdN, hd⟩ := mem_erase.mp hd
    obtain ⟨F, _, rfl⟩ := mem_image.mp hd
    exact F.modulus_admissible hN hrank hdN
  have hcard := card_le_card hsub
  by_cases hmem : N ∈ profileModuli rank c
  · have hdiff := card_erase_add_one hmem
    rw [card_profileModuli] at hdiff
    omega
  · rw [erase_eq_of_notMem hmem, card_profileModuli] at hcard
    omega

lemma ArithmeticProfile.modulus_ne_center_of_later {N : ℕ}
    {rank : PrimeCoordinate N → ℕ} (hrank : IsArithmeticRank rank)
    {c i : PrimeCoordinate N} (F : ArithmeticProfile rank c) (hi : rank c < rank i) :
    F.modulus ≠ N := by
  intro h
  have hfix : i.2.val < F.modulus.factorization i.1 := by rw [h]; exact i.2.isLt
  rcases F.modulus_ordered hrank i hfix with hie | hlt
  · rw [hie] at hi
    exact lt_irrefl _ hi
  · omega

theorem profile_count_le_admissible_of_later {N : ℕ} (hN : N ≠ 0)
    {rank : PrimeCoordinate N → ℕ} (hrank : IsArithmeticRank rank)
    {c i : PrimeCoordinate N} (hi : rank c < rank i) :
    (∏ p : OtherPrime c, (precedingExponent rank c p.val + 1)) ≤
      (admissibleFrameModuli rank c).card := by
  rw [← card_profileModuli]
  apply card_le_card
  intro d hd
  obtain ⟨F, _, rfl⟩ := mem_image.mp hd
  exact F.modulus_admissible hN hrank (F.modulus_ne_center_of_later hrank hi)

end Erdos1189
