import ErdosProblems.Erdos4.FGKMTPrimeCharacterCancellation
import ErdosProblems.Erdos4.FGKMTLowCharacterFamily

/-! The low Fourier modes are controlled on actual intervals of source primes. -/

open scoped BigOperators

namespace Erdos4.FGKMT

open Classical ProductCharacterEncoding FiniteCharacterSupport

section OneFamily

variable {P : Type*} [Fintype P] [DecidableEq P]
    (ell : P → ℕ) [∀ l, Fact (ell l).Prime]

theorem productEntry_nonprincipal (hinj : Function.Injective ell)
    (χ : ∀ l, DirichletCharacter ℂ (ell l)) (hχ : χ ≠ fun _ => 1) : (entry ell χ).2 ≠ 1 := by
  intro hprim
  change (character ell χ).primitiveCharacter = 1 at hprim
  have hchar : character ell χ = 1 := by
    rw [← DirichletCharacter.changeLevel_primitiveCharacter (character ell χ)]
    rw [hprim, DirichletCharacter.changeLevel_one]
  have hone : character ell (fun _ => 1) = 1 := by
    unfold character
    simp only [DirichletCharacter.changeLevel_one, Finset.prod_const_one]
  exact hχ ((character_injective ell (pairwise_coprime_of_prime ell
    (fun l => (Fact.out : (ell l).Prime)) hinj)) (hchar.trans hone.symm))

theorem productEntry_coprime (χ : ∀ l, DirichletCharacter ℂ (ell l)) {B : ℕ}
    (hB : ∀ l, (ell l).Coprime B) : (entry ell χ).1.Coprime B := by
  have hfull : (modulus ell).Coprime B := Nat.Coprime.prod_left (fun l _ => hB l)
  exact hfull.of_dvd_left (character ell χ).conductor_dvd_level

theorem product_interval_sum_eq_primitive (χ : ∀ l, DirichletCharacter ℂ (ell l))
    (a b : ℕ)
    (hs : ∀ p ∈ ChebyshevIntervals.primeInterval a b, p.Coprime (modulus ell)) :
    (∑ p : ChebyshevIntervals.primeInterval a b, ProductPrimeMeanSquare.value ell χ p.val) =
      ∑ p ∈ ChebyshevIntervals.primeInterval a b, (entry ell χ).2 (p : ZMod (entry ell χ).1) := by
  rw [Finset.sum_coe_sort (ChebyshevIntervals.primeInterval a b)
    (fun p : ℕ => ProductPrimeMeanSquare.value ell χ p)]
  apply Finset.sum_congr rfl
  intro p hp
  exact (entry_value_eq_product ell χ p (hs p hp)).symm

end OneFamily

theorem excisedPrimeSum_nonneg (x Q B : ℕ) : 0 ≤ excisedPrimeSum x Q B :=
  Finset.sum_nonneg (fun q _ => primeDiscrepancyUpTo_nonneg x q)

variable {P Q : Type*} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
    (ell₀ : P → ℕ) (ell₁ : Q → ℕ)
    [∀ l, Fact (ell₀ l).Prime] [∀ l, Fact (ell₁ l).Prime]

theorem low_product_interval_sum_le (M : ℕ) (hinj : Function.Injective (Sum.elim ell₀ ell₁))
    {a b x N B : ℕ} (ha : 2 ≤ a) (hab : a ≤ b) (hbx : b ≤ x)
    (hN : modulus ell₀ ≤ N) (hB : ∀ l, (Sum.elim ell₀ ell₁ l).Coprime B)
    (hs : ∀ p ∈ ChebyshevIntervals.primeInterval a b,
      p.Coprime (modulus (Sum.elim ell₀ ell₁)))
    (χ : smallCharacters (Sum.elim ell₀ ell₁) M)
    (hχ : χ ∈ lowMaskedIndices ell₀ ell₁ M) :
    ‖∑ p : ChebyshevIntervals.primeInterval a b,
      ProductPrimeMeanSquare.value (Sum.elim ell₀ ell₁) χ.val p.val‖ ≤
        2 * (modulus ell₀ : ℝ) * excisedPrimeSum x N B := by
  let c := entry (Sum.elim ell₀ ell₁) χ.val
  have hcpos : 0 < c.1 := (family_valid (Sum.elim ell₀ ell₁) χ).1
  letI : NeZero c.1 := ⟨hcpos.ne'⟩
  have hcne : c.2 ≠ 1 := productEntry_nonprincipal (Sum.elim ell₀ ell₁) hinj χ.val
    ((mem_smallCharacters (Sum.elim ell₀ ell₁) M χ.val).mp χ.property).1
  have hcle : c.1 ≤ modulus ell₀ := low_primitive_conductor_le ell₀ ell₁ χ.val
    ((mem_lowMaskedIndices ell₀ ell₁ M χ).mp hχ)
  have hccop : c.1.Coprime B := productEntry_coprime (Sum.elim ell₀ ell₁) χ.val hB
  have hh := norm_primeCharacterInterval_le_excised c.2 hcne ha hab hbx (hcle.trans hN) hccop
  rw [product_interval_sum_eq_primitive (Sum.elim ell₀ ell₁) χ.val a b hs]
  exact hh.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (by exact_mod_cast hcle) (by norm_num : (0 : ℝ) ≤ 2))
      (excisedPrimeSum_nonneg x N B))

theorem low_masked_interval_error {k : ℕ} (β : ℝ) (R M : ℕ)
    (h₀ : ∀ l, Fin k → ZMod (ell₀ l)) (h₁ : ∀ l, Fin k → ZMod (ell₁ l))
    (hinj : Function.Injective (Sum.elim ell₀ ell₁))
    {a b x N B : ℕ} (ha : 2 ≤ a) (hab : a ≤ b) (hbx : b ≤ x)
    (hN : modulus ell₀ ≤ N) (hB : ∀ l, (Sum.elim ell₀ ell₁ l).Coprime B)
    (hs : ∀ p ∈ ChebyshevIntervals.primeInterval a b,
      p.Coprime (modulus (Sum.elim ell₀ ell₁)))
    (q : ℕ) {K : ℝ} (hK : 0 ≤ K)
    (hc : ∀ χ, ‖lowMaskedCoefficient ell₀ ell₁ β R M h₀ h₁ χ‖ ≤ K) :
    ‖ProductPrimeMeanSquare.weightedSourceError (Sum.elim ell₀ ell₁) M
      (lowMaskedCoefficient ell₀ ell₁ β R M h₀ h₁)
      (ChebyshevIntervals.primeInterval a b) (fun _ => 1) q‖ ≤
        2 * (modulus ell₀ : ℝ) ^ 3 * K * excisedPrimeSum x N B := by
  have he : 0 ≤ 2 * (modulus ell₀ : ℝ) * excisedPrimeSum x N B :=
    mul_nonneg (by positivity) (excisedPrimeSum_nonneg x N B)
  have hh := low_masked_source_error_le ell₀ ell₁ β R M h₀ h₁ hinj
    (ChebyshevIntervals.primeInterval a b) (fun _ => 1) q hK he hc
    (fun χ hχ => by simpa only [one_mul] using
      low_product_interval_sum_le ell₀ ell₁ M hinj ha hab hbx hN hB hs χ hχ)
  exact hh.trans_eq (by ring)

end Erdos4.FGKMT
