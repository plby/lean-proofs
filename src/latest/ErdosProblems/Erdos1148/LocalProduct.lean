import ErdosProblems.Erdos1148.GlobalToLocal

/-!
# The finite product of local orbit counts

Only primes dividing the binary discriminant can contribute nontrivial local
factors. The global-to-local injection therefore gives a finite product bound.
-/

namespace Erdos1148.DukeArithmetic

abbrev BadPairPrime (d ℓ : ℤ) := {r : ℕ // r ∈ (ℓ ^ 2 - 4 * d ^ 2).natAbs.primeFactors}

def BadLocalPairOrbit (d ℓ : ℤ) (r : BadPairPrime d ℓ) :=
  letI : Fact r.1.Prime := ⟨Nat.prime_of_mem_primeFactors r.2⟩
  SpecialPairOrbits (PadicInt r.1) d ℓ

noncomputable def badPrimeOrbitMap {d ℓ : ℤ} (x : SpecialPairOrbits ℤ d ℓ) :
    ∀ r : BadPairPrime d ℓ, BadLocalPairOrbit d ℓ r := fun r => by
  let : Fact r.1.Prime := ⟨Nat.prime_of_mem_primeFactors r.2⟩
  exact specialPairOrbitBaseChange (Int.castRingHom (PadicInt r.1)) x

lemma badPrimeOrbitMap_injective {d ℓ : ℤ} (hnd : ℓ ^ 2 ≠ 4 * d ^ 2) :
    Function.Injective (badPrimeOrbitMap (d := d) (ℓ := ℓ)) := by
  intro x y hxy
  induction x, y using Quotient.inductionOn₂ with | h src dst =>
    apply integer_pairOrbit_eq_of_local_eq src dst hnd
    intro r hr
    by_cases hbad : r ∈ (ℓ ^ 2 - 4 * d ^ 2).natAbs.primeFactors
    · have h := congrFun hxy ⟨r, hbad⟩
      exact h
    · have hgood : ¬ (r : ℤ) ∣ ℓ ^ 2 - 4 * d ^ 2 := by
        intro hdiv
        apply hbad
        exact (Fact.out : r.Prime).mem_primeFactors (Int.natCast_dvd.mp hdiv)
          (Int.natAbs_ne_zero.mpr (sub_ne_zero.mpr hnd))
      let := specialPairOrbits_subsingleton_of_unit (padic_isUnit_pair_discriminant r d ℓ hgood)
      exact Subsingleton.elim _ _

lemma finite_badLocalPairOrbit {d ℓ : ℤ} (base : FormPair ℤ d ℓ)
    (hnd : ℓ ^ 2 ≠ 4 * d ^ 2) (r : BadPairPrime d ℓ) : Finite (BadLocalPairOrbit d ℓ r) := by
  let : Fact r.1.Prime := ⟨Nat.prime_of_mem_primeFactors r.2⟩
  exact finite_padic_specialPairOrbits r.1 (mapFormPair (Int.castRingHom (PadicInt r.1)) base)
    (map_nondegenerate (Int.castRingHom (PadicInt r.1)) Int.cast_injective hnd)

/-- The global number of embeddings is bounded by the product of the local numbers. -/
theorem card_integer_specialPairOrbits_le_local_product {d ℓ : ℤ} (base : FormPair ℤ d ℓ)
    (hnd : ℓ ^ 2 ≠ 4 * d ^ 2) :
    Nat.card (SpecialPairOrbits ℤ d ℓ) ≤
      ∏ r : BadPairPrime d ℓ, Nat.card (BadLocalPairOrbit d ℓ r) := by
  let : ∀ r : BadPairPrime d ℓ, Finite (BadLocalPairOrbit d ℓ r) :=
    finite_badLocalPairOrbit base hnd
  have h := Nat.card_le_card_of_injective _ (badPrimeOrbitMap_injective hnd)
  rwa [Nat.card_pi] at h

end Erdos1148.DukeArithmetic
