/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierAffineAsymptotic

/-!
# Exact physical pre-sieve normalization

The small-prime singular product is the actual density of admissible
CRT classes divided by the zero-exponent reference product. Evenness
of the cofactor gives the positive density needed for cancellation.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

theorem smallDoubledFourierReferenceProduct_zero_eq_nat_prime_product (K w : ℕ) :
    smallDoubledFourierReferenceProduct (ι := Fin K) w (fun _ _ ↦ 0) =
      ∏ p ∈ Nat.primesLE w, (1 - 1 / (p : ℂ)) ^ (2 * K) := by
  unfold smallDoubledFourierReferenceProduct
  simp_rw [doubledFourierReferenceFactor_zero]
  simp only [Fintype.card_sum, Fintype.card_fin, ← two_mul]
  exact Finset.prod_subtype_of_mem
    (fun p : ℕ ↦ (1 - 1 / (p : ℂ)) ^ (2 * K))
    (fun p hp ↦ (Nat.mem_primesLE.mp hp).2)

theorem complex_largeGapSingularSeries_preSieveCutoff
    {K w m q : ℕ} (hK : 0 < K) :
    (largeGapSingularSeries (preSievedShifts K w) m q w : ℂ) =
      (preSieveDensity w m : ℂ) /
        smallDoubledFourierReferenceProduct (ι := Fin K) w (fun _ _ ↦ 0) := by
  rw [largeGapSingularSeries_preSieveCutoff hK,
    smallDoubledFourierReferenceProduct_zero_eq_nat_prime_product]
  push_cast
  simp only [div_eq_mul_inv, ← Finset.prod_inv_distrib, inv_pow]

def fullActualAffineSingularProduct (K w m q : ℕ) : ℂ :=
  (largeGapSingularSeries (preSievedShifts K w) m q w : ℂ) *
    ∏' p : Nat.Primes, roughActualAffineSingularFactor (preSievedShifts K w) w m q p

def fullAffineFourierNormalization (K w m q : ℕ) (L : (Fin K ⊕ Fin K) → ℝ) : ℂ :=
  (∏ i, (L i : ℂ)) / fullActualAffineSingularProduct K w m q

theorem hasProd_small_actualAffineSingularFactors (H : Finset ℕ) (w m q : ℕ) :
    HasProd (fun p : Nat.Primes ↦ if p.val ≤ w then (largeGapLocalFactor H m q p : ℂ) else 1)
      (largeGapSingularSeries H m q w : ℂ) := by
  classical
  let f (p : Nat.Primes) : ℂ := if p.val ≤ w then (largeGapLocalFactor H m q p : ℂ) else 1
  have hfin : HasProd f (∏ p ∈ boundedFourierPrimes w, f p) :=
    hasProd_prod_of_ne_finset_one (s := boundedFourierPrimes w) (f := f)
      (fun p hp ↦ if_neg (fun h ↦ hp ((mem_boundedFourierPrimes w p).mpr h)))
  have heq : (∏ p ∈ boundedFourierPrimes w, f p) = (largeGapSingularSeries H m q w : ℂ) := by
    calc
      _ = ∏ p ∈ boundedFourierPrimes w, (largeGapLocalFactor H m q p : ℂ) := by
        apply Finset.prod_congr rfl
        intro p hp
        exact if_pos ((mem_boundedFourierPrimes w p).mp hp)
      _ = ∏ p ∈ Nat.primesLE w, (largeGapLocalFactor H m q p : ℂ) :=
        Finset.prod_subtype_of_mem (fun p : ℕ ↦ (largeGapLocalFactor H m q p : ℂ))
          (fun p hp ↦ (Nat.mem_primesLE.mp hp).2)
      _ = _ := by simp only [largeGapSingularSeries, Complex.ofReal_prod]
  exact heq ▸ hfin

theorem hasProd_fullActualAffineSingularProduct
    {K w m q : ℕ} (hm : 0 < m) (hq : q.Prime) (hKw : K ≤ w) (hwq : w < q)
    (hlarge : 7 * (Fintype.card (preSievedShifts K w ⊕ preSievedShifts K w) : ℝ) ≤ w) :
    HasProd (fun p : Nat.Primes ↦ (largeGapLocalFactor (preSievedShifts K w) m q p : ℂ))
      (fullActualAffineSingularProduct K w m q) := by
  have hs := hasProd_small_actualAffineSingularFactors (preSievedShifts K w) w m q
  have hr := (hasProd_roughActualAffineSingularFactor hm hq hKw hwq hlarge).multipliable.hasProd
  convert! hs.mul hr using 1
  ext p
  by_cases hpw : p.val ≤ w
  · simp only [if_pos hpw, roughActualAffineSingularFactor, if_neg (Nat.not_lt.mpr hpw), mul_one]
  · simp only [if_neg hpw, roughActualAffineSingularFactor, if_pos (Nat.lt_of_not_ge hpw), one_mul]

theorem fullAffineFourierNormalization_mul_preSieveDensity
    {K w m q : ℕ} (L : (Fin K ⊕ Fin K) → ℝ) (hK : 0 < K) (hm : Even m) :
    fullAffineFourierNormalization K w m q L * (preSieveDensity w m : ℂ) =
      actualAffineFourierNormalization K w m q L := by
  have hd : (preSieveDensity w m : ℂ) ≠ 0 := by
    exact_mod_cast (preSieveDensity_pos_of_even hm).ne'
  unfold fullAffineFourierNormalization fullActualAffineSingularProduct
    actualAffineFourierNormalization
  rw [complex_largeGapSingularSeries_preSieveCutoff hK]
  simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, hd]

theorem fullAffineFourierNormalization_mul_physical_class_density
    {K w m q : ℕ} (L : (Fin K ⊕ Fin K) → ℝ)
    (hK : 0 < K) (hw : 2 ≤ w) (hm : 0 < m) (hmeven : Even m) :
    fullAffineFourierNormalization K w m q L *
      ((((allowedPreSieveResidues (primorial w) m).card : ℝ) / primorial w : ℝ) : ℂ) =
        actualAffineFourierNormalization K w m q L := by
  rw [card_allowedPreSieveResidues_div_primorial hw hm]
  exact fullAffineFourierNormalization_mul_preSieveDensity L hK hmeven

end

end Erdos4b
