import ErdosProblems.Erdos1148.IntegerLocalCount
import ErdosProblems.Erdos1148.SquareContent
import ErdosProblems.Erdos1148.OrbitComparison
import ErdosProblems.Erdos1148.DivisorBounds

/-!
# The global pair-orbit counting estimate

The checked local bounds and global-to-local injection give the arithmetic
count used in the basic lemma. The common square-divisor factor is linear;
all remaining prime-exponent factors have subpower growth.
-/

namespace Erdos1148.DukeArithmetic

lemma bad_local_card_le_factor (d ℓ : ℤ) (base : FormPair ℤ d ℓ)
    (hd : d ≠ 0) (hnd : ℓ ^ 2 ≠ 4 * d ^ 2) (r : BadPairPrime d ℓ) :
    (Nat.card (BadLocalPairOrbit d ℓ r) : ℝ) ≤
      (16 * (((ℓ ^ 2 - 4 * d ^ 2).natAbs.factorization r : ℝ) + 1) ^ 2) *
        (r : ℝ) ^ (pairSquareContent d ℓ).factorization r := by
  let : Fact r.1.Prime := ⟨Nat.prime_of_mem_primeFactors r.2⟩
  have h := card_padicPairOrbits_le_factorization r.1 base hd hnd
  rw [← pairSquareContent_factorization] at h
  have hR : (Nat.card (BadLocalPairOrbit d ℓ r) : ℝ) ≤
      16 * (((ℓ ^ 2 - 4 * d ^ 2).natAbs.factorization r : ℝ) + 1) *
        (r : ℝ) ^ (pairSquareContent d ℓ).factorization r := by exact_mod_cast h
  have hfac : ((ℓ ^ 2 - 4 * d ^ 2).natAbs.factorization r : ℝ) + 1 ≤
      (((ℓ ^ 2 - 4 * d ^ 2).natAbs.factorization r : ℝ) + 1) ^ 2 := by
    have hnonneg : 0 ≤ ((ℓ ^ 2 - 4 * d ^ 2).natAbs.factorization r : ℝ) := by positivity
    nlinarith
  exact hR.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hfac (by norm_num)) (by positivity))

/-- The unconditional arithmetic pair-counting estimate. -/
theorem exists_integral_pair_orbit_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (d ℓ : ℤ) (_base : FormPair ℤ d ℓ),
      d ≠ 0 → ℓ ^ 2 ≠ 4 * d ^ 2 →
      (Nat.card (IntegralPairOrbits d ℓ) : ℝ) ≤
        C * pairSquareContent d ℓ * ((ℓ ^ 2 - 4 * d ^ 2).natAbs : ℝ) ^ ε := by
  classical
  obtain ⟨C, hC, hprod⟩ := exists_local_factor_product_le (c := 16) (by norm_num) hε
  refine ⟨2 * C, by positivity, ?_⟩
  intro d ℓ base hd hnd
  let D := (ℓ ^ 2 - 4 * d ^ 2).natAbs
  let f := pairSquareContent d ℓ
  have hD : D ≠ 0 := Int.natAbs_ne_zero.mpr (sub_ne_zero.mpr hnd)
  have hf : f ∣ D := pairSquareContent_dvd_binary_discriminant d ℓ
  have hcard : (Nat.card (IntegralPairOrbits d ℓ) : ℝ) ≤
      2 * ∏ r : BadPairPrime d ℓ, (Nat.card (BadLocalPairOrbit d ℓ r) : ℝ) := by
    exact_mod_cast card_integralPairOrbits_le_local_product base hnd
  have hlocal : (∏ r : BadPairPrime d ℓ, (Nat.card (BadLocalPairOrbit d ℓ r) : ℝ)) ≤
      ∏ r ∈ D.primeFactors, (16 * ((D.factorization r : ℝ) + 1) ^ 2) *
        (r : ℝ) ^ f.factorization r := by
    calc
      _ ≤ ∏ r : BadPairPrime d ℓ, (16 * ((D.factorization r : ℝ) + 1) ^ 2) *
          (r : ℝ) ^ f.factorization r := by
        apply Finset.prod_le_prod (fun _ _ => by positivity)
        intro r _
        exact bad_local_card_le_factor d ℓ base hd hnd r
      _ = _ := by
        simpa only [BadPairPrime, D] using Finset.prod_coe_sort D.primeFactors
          (fun r : ℕ => (16 * ((D.factorization r : ℝ) + 1) ^ 2) *
            (r : ℝ) ^ f.factorization r)
  have hbound : (Nat.card (IntegralPairOrbits d ℓ) : ℝ) ≤ 2 * (C * f * (D : ℝ) ^ ε) :=
    hcard.trans ((mul_le_mul_of_nonneg_left hlocal (by norm_num)).trans
      (mul_le_mul_of_nonneg_left (hprod D f hD hf) (by norm_num)))
  simpa only [D, f, mul_assoc] using hbound

theorem exists_integral_pair_orbit_bound_all {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ d ℓ : ℤ, d ≠ 0 → ℓ ^ 2 ≠ 4 * d ^ 2 →
      (Nat.card (IntegralPairOrbits d ℓ) : ℝ) ≤
        C * pairSquareContent d ℓ * ((ℓ ^ 2 - 4 * d ^ 2).natAbs : ℝ) ^ ε := by
  classical
  obtain ⟨C, hC, hbound⟩ := exists_integral_pair_orbit_bound hε
  refine ⟨C, hC, ?_⟩
  intro d ℓ hd hnd
  by_cases hp : Nonempty (FormPair ℤ d ℓ)
  · exact hbound d ℓ (Classical.choice hp) hd hnd
  · let : IsEmpty (FormPair ℤ d ℓ) := not_nonempty_iff.mp hp
    have : IsEmpty (IntegralPairOrbits d ℓ) := inferInstance
    simp only [Nat.card_of_isEmpty, Nat.cast_zero]
    positivity

end Erdos1148.DukeArithmetic
