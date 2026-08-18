/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos1211.External.Erdos4.ResidualPrimeFiberBeta
import ErdosProblems.Erdos851.EulerMass
import ErdosProblems.Erdos387.PrimeReciprocalBound

/-!
# Mertens simplification for residual prime fibres

This file extracts the primes dividing the residual cofactor from the local
Euler product.  The primes not dividing the cofactor contribute an ordinary
Mertens product; the omitted primes contribute an explicit finite correction.
-/

namespace Erdos4

noncomputable section

open scoped BigOperators

/-- Odd sieving primes which are omitted because they divide the cofactor. -/
def residualCofactorSievePrimes (y m : ℕ) : Finset ℕ :=
  (Erdos851.sievePrimes 2 y).filter fun p ↦ p ∣ m

theorem residual_and_cofactor_sievePrimes (y m : ℕ) (hmEven : Even m) :
    residualSievePrimes y m ∪ residualCofactorSievePrimes y m =
      Erdos851.sievePrimes 2 y := by
  ext p
  simp only [Finset.mem_union, residualSievePrimes,
    residualCofactorSievePrimes, Finset.mem_filter,
    Nat.mem_primesLE, Erdos851.mem_sievePrimes]
  constructor
  · rintro (⟨⟨hpy, hpPrime⟩, hpNotDiv⟩ |
      ⟨⟨hpTwo, hpy, hpPrime⟩, hpDiv⟩)
    · refine ⟨?_, hpy, hpPrime⟩
      have hpTwoLe := hpPrime.two_le
      have hpNeTwo : p ≠ 2 := by
        intro hp
        subst p
        exact hpNotDiv hmEven.two_dvd
      omega
    · exact ⟨hpTwo, hpy, hpPrime⟩
  · rintro ⟨hpTwo, hpy, hpPrime⟩
    by_cases hpDiv : p ∣ m
    · exact Or.inr ⟨⟨hpTwo, hpy, hpPrime⟩, hpDiv⟩
    · exact Or.inl ⟨⟨hpy, hpPrime⟩, hpDiv⟩

theorem residual_cofactor_sievePrimes_disjoint (y m : ℕ) :
    Disjoint (residualSievePrimes y m)
      (residualCofactorSievePrimes y m) := by
  rw [Finset.disjoint_left]
  intro p hpResidual hpCofactor
  exact (Finset.mem_filter.mp hpResidual).2
    (Finset.mem_filter.mp hpCofactor).2

/-- The product of the local factors omitted at primes dividing `m`. -/
def residualCofactorLocalProduct (y m : ℕ) : ℝ :=
  ∏ p ∈ residualCofactorSievePrimes y m,
    (1 - residualPrimeDensity p)

/-- The reciprocal correction introduced by omitting primes dividing `m`. -/
noncomputable def residualCofactorInverseProduct (y m : ℕ) : ℝ :=
  ∏ p ∈ residualCofactorSievePrimes y m,
    (1 - residualPrimeDensity p)⁻¹

theorem residualCofactorLocalProduct_pos
    {y m : ℕ} (hmEven : Even m) :
    0 < residualCofactorLocalProduct y m := by
  unfold residualCofactorLocalProduct
  apply Finset.prod_pos
  intro p hp
  have hpData := Erdos851.mem_sievePrimes.mp
    (Finset.mem_filter.mp hp).1
  exact sub_pos.mpr (residualPrimeDensity_lt_one hpData.2.2 (by omega))

theorem residualPrimeLocalEulerProduct_mul_cofactor
    (y m : ℕ) (hmEven : Even m) :
    residualPrimeLocalEulerProduct y m *
        residualCofactorLocalProduct y m =
      Erdos851.localEulerProduct residualPrimeDensity 2 y := by
  unfold residualPrimeLocalEulerProduct residualCofactorLocalProduct
    Erdos851.localEulerProduct
  rw [← Finset.prod_union (residual_cofactor_sievePrimes_disjoint y m),
    residual_and_cofactor_sievePrimes y m hmEven]

theorem residualCofactorInverseProduct_eq_inv
    (y m : ℕ) :
    residualCofactorInverseProduct y m =
      (residualCofactorLocalProduct y m)⁻¹ := by
  simp only [residualCofactorInverseProduct,
    residualCofactorLocalProduct, Finset.prod_inv_distrib]

/-- Exact extraction of the cofactor correction from the residual product. -/
theorem residualPrimeLocalEulerProduct_eq_all_mul_cofactorInverse
    (y m : ℕ) (hmEven : Even m) :
    residualPrimeLocalEulerProduct y m =
      Erdos851.localEulerProduct residualPrimeDensity 2 y *
        residualCofactorInverseProduct y m := by
  rw [residualCofactorInverseProduct_eq_inv]
  have hcofactor := residualCofactorLocalProduct_pos (y := y) hmEven
  calc
    residualPrimeLocalEulerProduct y m =
        (residualPrimeLocalEulerProduct y m *
          residualCofactorLocalProduct y m) *
            (residualCofactorLocalProduct y m)⁻¹ := by
      rw [mul_assoc, mul_inv_cancel₀ hcofactor.ne', mul_one]
    _ = Erdos851.localEulerProduct residualPrimeDensity 2 y *
          (residualCofactorLocalProduct y m)⁻¹ := by
      rw [residualPrimeLocalEulerProduct_mul_cofactor y m hmEven]

theorem residualPrime_localFactor_le_oneShift
    {p : ℕ} (hp : p.Prime) (hpTwo : 2 < p) :
    1 - residualPrimeDensity p ≤
      1 - Erdos851.oneShiftDensity p := by
  rw [residualPrimeDensity_eq_inv_pred hp]
  unfold Erdos851.oneShiftDensity
  have hpPos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpredPos : (0 : ℝ) < (p - 1 : ℕ) := by
    exact_mod_cast Nat.sub_pos_of_lt hp.one_lt
  have hpredLe : ((p - 1 : ℕ) : ℝ) ≤ p := by
    exact_mod_cast Nat.sub_le p 1
  have hinv : (p : ℝ)⁻¹ ≤ ((p - 1 : ℕ) : ℝ)⁻¹ :=
    (inv_le_inv₀ hpPos hpredPos).2 hpredLe
  linarith

/-- The complete residual-density product over odd primes is no larger than
the ordinary direct Mertens product. -/
theorem residualPrime_allLocalEulerProduct_le_oneShift (y : ℕ) :
    Erdos851.localEulerProduct residualPrimeDensity 2 y ≤
      Erdos851.localEulerProduct Erdos851.oneShiftDensity 2 y := by
  unfold Erdos851.localEulerProduct
  apply Finset.prod_le_prod
  · intro p hp
    have hpData := Erdos851.mem_sievePrimes.mp hp
    exact (sub_pos.mpr
      (residualPrimeDensity_lt_one hpData.2.2 (by omega))).le
  · intro p hp
    have hpData := Erdos851.mem_sievePrimes.mp hp
    exact residualPrime_localFactor_le_oneShift hpData.2.2 (by omega)

private theorem partial_euler_product_two : partial_euler_product 2 = 2 := by
  have hprimes : (Finset.Icc 1 2).filter Nat.Prime = {2} := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Icc,
      Finset.mem_singleton]
    constructor
    · rintro ⟨⟨_hpOne, hpTwo⟩, hpPrime⟩
      have hpLower := hpPrime.two_le
      omega
    · rintro rfl
      norm_num
  rw [partial_euler_product, hprimes]
  norm_num

theorem oneShift_localEulerProduct_two_eq (y : ℕ) (hy : 2 ≤ y) :
    Erdos851.localEulerProduct Erdos851.oneShiftDensity 2 y =
      2 / partial_euler_product y := by
  have hratio := Erdos851.oneShift_inverseLocalEulerProduct_eq hy
  rw [Erdos851.inverseLocalEulerProduct_eq_inv,
    partial_euler_product_two] at hratio
  have hpepPos : 0 < partial_euler_product y :=
    lt_of_lt_of_le (by norm_num) partial_euler_trivial_lower_bound
  calc
    Erdos851.localEulerProduct Erdos851.oneShiftDensity 2 y =
        (Erdos851.localEulerProduct
          Erdos851.oneShiftDensity 2 y)⁻¹⁻¹ := by rw [inv_inv]
    _ = (partial_euler_product y / 2)⁻¹ := by rw [hratio]
    _ = 2 / partial_euler_product y := by
      field_simp [hpepPos.ne']

/-- Weak Mertens in direct-product form at the fixed lower endpoint `2`. -/
theorem exists_oneShift_directMertens_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℕ, 2 ≤ y →
      Erdos851.localEulerProduct Erdos851.oneShiftDensity 2 y ≤
        C / Real.log (y : ℝ) := by
  obtain ⟨Cl, hCl, hlower⟩ := weak_mertens_third_lower_all
  refine ⟨2 / Cl, by positivity, ?_⟩
  intro y hy
  have hyR : (1 : ℝ) < y := by exact_mod_cast (show 1 < y by omega)
  have hlog : 0 < Real.log (y : ℝ) := Real.log_pos hyR
  have hpepPos : 0 < partial_euler_product y :=
    lt_of_lt_of_le (by norm_num) partial_euler_trivial_lower_bound
  have hlower' : Cl * Real.log (y : ℝ) ≤ partial_euler_product y := by
    simpa [Real.norm_of_nonneg hlog.le,
      Real.norm_of_nonneg (zero_le_one.trans
        (partial_euler_trivial_lower_bound (n := y)))]
      using hlower (y : ℝ) hyR.le
  rw [oneShift_localEulerProduct_two_eq y hy]
  calc
    2 / partial_euler_product y ≤
        2 / (Cl * Real.log (y : ℝ)) := by
      rw [div_le_div_iff₀ hpepPos (mul_pos hCl hlog)]
      nlinarith
    _ = (2 / Cl) / Real.log (y : ℝ) := by
      field_simp [hCl.ne', hlog.ne']

/-! ## The cofactor correction -/

/-- The ordinary inverse factors at the omitted cofactor primes. -/
noncomputable def residualCofactorOrdinaryInverseProduct
    (y m : ℕ) : ℝ :=
  ∏ p ∈ residualCofactorSievePrimes y m,
    (1 - Erdos851.oneShiftDensity p)⁻¹

/-- The convergent second-order factors at the omitted cofactor primes. -/
noncomputable def residualCofactorSecondOrderProduct
    (y m : ℕ) : ℝ :=
  ∏ p ∈ residualCofactorSievePrimes y m,
    Erdos851.secondOrderCorrection p

theorem residualCofactorInverseProduct_eq_ordinary_mul_secondOrder
    (y m : ℕ) :
    residualCofactorInverseProduct y m =
      residualCofactorOrdinaryInverseProduct y m *
        residualCofactorSecondOrderProduct y m := by
  unfold residualCofactorInverseProduct
    residualCofactorOrdinaryInverseProduct
    residualCofactorSecondOrderProduct
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have hpData := Erdos851.mem_sievePrimes.mp
    (Finset.mem_filter.mp hp).1
  exact residualPrimeDensity_inverse_factor_eq hpData.2.2 (by omega)

theorem residualCofactorSecondOrderProduct_le_two (y m : ℕ) :
    residualCofactorSecondOrderProduct y m ≤ 2 := by
  unfold residualCofactorSecondOrderProduct
  calc
    (∏ p ∈ residualCofactorSievePrimes y m,
        Erdos851.secondOrderCorrection p) ≤
        ∏ p ∈ Erdos851.sievePrimes 2 y,
          Erdos851.secondOrderCorrection p := by
      apply Finset.prod_le_prod_of_subset_of_one_le
      · exact Finset.filter_subset _ _
      · intro p hp
        exact (Erdos851.one_le_secondOrderCorrection (by
          have hpData := Erdos851.mem_sievePrimes.mp
            (Finset.mem_filter.mp hp).1
          omega)).trans' (by norm_num)
      · intro p hp _hpNot
        exact Erdos851.one_le_secondOrderCorrection (by
          have hpData := Erdos851.mem_sievePrimes.mp hp
          omega)
    _ ≤ 2 := Erdos851.secondOrderCorrection_product_le_two
      (by norm_num)

private theorem cofactor_ratio_eq_primeFactors_product_rat
    (m : ℕ) (hm : m ≠ 0) :
    (m : ℚ) / Nat.totient m =
      ∏ p ∈ m.primeFactors, ((p : ℚ) / (p - 1)) := by
  have hphi : (Nat.totient m : ℚ) =
      (m : ℚ) * ∏ p ∈ m.primeFactors,
        (1 - (p : ℚ)⁻¹) :=
    Nat.totient_eq_mul_prod_factors m
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm
  have hprodNe :
      (∏ p ∈ m.primeFactors, (1 - (p : ℚ)⁻¹)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro p hp
    have hpPrime := Nat.prime_of_mem_primeFactors hp
    have hpZero : (p : ℚ) ≠ 0 := by exact_mod_cast hpPrime.ne_zero
    have hpOne : (p : ℚ) ≠ 1 := by exact_mod_cast hpPrime.ne_one
    rw [show 1 - (p : ℚ)⁻¹ = ((p : ℚ) - 1) / p by
      field_simp [hpZero]]
    exact div_ne_zero (sub_ne_zero.mpr hpOne) hpZero
  have hphiNe : (Nat.totient m : ℚ) ≠ 0 := by
    rw [hphi]
    exact mul_ne_zero hmQ hprodNe
  calc
    (m : ℚ) / Nat.totient m =
        (∏ p ∈ m.primeFactors, (1 - (p : ℚ)⁻¹))⁻¹ := by
      rw [hphi]
      field_simp [hmQ, hprodNe]
    _ = ∏ p ∈ m.primeFactors, ((p : ℚ) / (p - 1)) := by
      rw [← Finset.prod_inv_distrib]
      apply Finset.prod_congr rfl
      intro p hp
      have hpPrime := Nat.prime_of_mem_primeFactors hp
      have hpZero : (p : ℚ) ≠ 0 := by exact_mod_cast hpPrime.ne_zero
      have hpOne : (p : ℚ) ≠ 1 := by exact_mod_cast hpPrime.ne_one
      field_simp [hpZero, hpOne]

theorem cofactor_ratio_eq_primeFactors_product
    (m : ℕ) (hm : m ≠ 0) :
    (m : ℝ) / Nat.totient m =
      ∏ p ∈ m.primeFactors,
        ((p : ℝ) / ((p : ℝ) - 1)) := by
  have hcast := congrArg (fun q : ℚ ↦ (q : ℝ))
    (cofactor_ratio_eq_primeFactors_product_rat m hm)
  simpa [Rat.cast_prod] using hcast

theorem oneShift_inverseFactor_eq_primeRatio
    {p : ℕ} (hp : p.Prime) :
    (1 - Erdos851.oneShiftDensity p)⁻¹ =
      (p : ℝ) / ((p : ℝ) - 1) := by
  have hpPos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpOne : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  unfold Erdos851.oneShiftDensity
  field_simp [hpPos.ne', (sub_pos.mpr hpOne).ne']

theorem one_le_oneShift_inverseFactor
    {p : ℕ} (hp : p.Prime) :
    1 ≤ (1 - Erdos851.oneShiftDensity p)⁻¹ := by
  exact (one_le_inv₀ (Erdos851.oneShift_localFactor_pos hp)).2
    (sub_le_self _ (Erdos851.oneShiftDensity_pos hp).le)

theorem residualCofactorOrdinaryInverseProduct_le_ratio
    {y m : ℕ} (hm : 0 < m) :
    residualCofactorOrdinaryInverseProduct y m ≤
      (m : ℝ) / Nat.totient m := by
  have hsubset : residualCofactorSievePrimes y m ⊆ m.primeFactors := by
    intro p hp
    have hpFilter := Finset.mem_filter.mp hp
    have hpPrime := (Erdos851.mem_sievePrimes.mp hpFilter.1).2.2
    exact Nat.mem_primeFactors.mpr ⟨hpPrime, hpFilter.2, hm.ne'⟩
  rw [cofactor_ratio_eq_primeFactors_product m hm.ne']
  unfold residualCofactorOrdinaryInverseProduct
  calc
    (∏ p ∈ residualCofactorSievePrimes y m,
        (1 - Erdos851.oneShiftDensity p)⁻¹) ≤
        ∏ p ∈ m.primeFactors,
          (1 - Erdos851.oneShiftDensity p)⁻¹ := by
      apply Finset.prod_le_prod_of_subset_of_one_le hsubset
      · intro p hp
        exact (one_le_oneShift_inverseFactor
          ((Erdos851.mem_sievePrimes.mp
            (Finset.mem_filter.mp hp).1).2.2)).trans' (by norm_num)
      · intro p hp _hpNot
        exact one_le_oneShift_inverseFactor
          (Nat.prime_of_mem_primeFactors hp)
    _ = ∏ p ∈ m.primeFactors,
        ((p : ℝ) / ((p : ℝ) - 1)) := by
      apply Finset.prod_congr rfl
      intro p hp
      exact oneShift_inverseFactor_eq_primeRatio
        (Nat.prime_of_mem_primeFactors hp)

/-- The omitted-prime correction is at most twice the standard totient
ratio.  The factor two is the complete convergent second-order Euler product. -/
theorem residualCofactorInverseProduct_le_two_mul_ratio
    {y m : ℕ} (hm : 0 < m) :
    residualCofactorInverseProduct y m ≤
      2 * ((m : ℝ) / Nat.totient m) := by
  rw [residualCofactorInverseProduct_eq_ordinary_mul_secondOrder]
  have hordNonneg :
      0 ≤ residualCofactorOrdinaryInverseProduct y m := by
    unfold residualCofactorOrdinaryInverseProduct
    apply Finset.prod_nonneg
    intro p hp
    exact (one_le_oneShift_inverseFactor
      ((Erdos851.mem_sievePrimes.mp
        (Finset.mem_filter.mp hp).1).2.2)).trans' (by norm_num)
  have hsecondNonneg :
      0 ≤ residualCofactorSecondOrderProduct y m := by
    unfold residualCofactorSecondOrderProduct
    apply Finset.prod_nonneg
    intro p hp
    exact (Erdos851.one_le_secondOrderCorrection (by
      have hpData := Erdos851.mem_sievePrimes.mp
        (Finset.mem_filter.mp hp).1
      omega)).trans' (by norm_num)
  have hratioNonneg : 0 ≤ (m : ℝ) / Nat.totient m := by positivity
  calc
    residualCofactorOrdinaryInverseProduct y m *
        residualCofactorSecondOrderProduct y m ≤
      residualCofactorOrdinaryInverseProduct y m * 2 :=
        mul_le_mul_of_nonneg_left
          (residualCofactorSecondOrderProduct_le_two y m) hordNonneg
    _ ≤ ((m : ℝ) / Nat.totient m) * 2 :=
      mul_le_mul_of_nonneg_right
        (residualCofactorOrdinaryInverseProduct_le_ratio hm)
        (by norm_num)
    _ = 2 * ((m : ℝ) / Nat.totient m) := by ring

/-- The residual local product has the standard Mertens upper bound with
the exact cofactor dependence needed in Maynard's residual-set estimate. -/
theorem exists_residualPrimeLocalEulerProduct_mertens_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ {y m : ℕ}, 2 ≤ y → 0 < m → Even m →
        residualPrimeLocalEulerProduct y m ≤
          C * ((m : ℝ) / Nat.totient m) /
            Real.log (y : ℝ) := by
  obtain ⟨C, hC, hMertens⟩ := exists_oneShift_directMertens_bound
  refine ⟨2 * C, by positivity, ?_⟩
  intro y m hy hm hmEven
  have hlog : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hcofactorNonneg :
      0 ≤ residualCofactorInverseProduct y m := by
    rw [residualCofactorInverseProduct_eq_inv]
    exact inv_nonneg.mpr (residualCofactorLocalProduct_pos hmEven).le
  have hratioNonneg : 0 ≤ (m : ℝ) / Nat.totient m := by positivity
  rw [residualPrimeLocalEulerProduct_eq_all_mul_cofactorInverse
    y m hmEven]
  calc
    Erdos851.localEulerProduct residualPrimeDensity 2 y *
        residualCofactorInverseProduct y m ≤
      Erdos851.localEulerProduct Erdos851.oneShiftDensity 2 y *
        residualCofactorInverseProduct y m :=
      mul_le_mul_of_nonneg_right
        (residualPrime_allLocalEulerProduct_le_oneShift y)
        hcofactorNonneg
    _ ≤ (C / Real.log (y : ℝ)) *
        residualCofactorInverseProduct y m :=
      mul_le_mul_of_nonneg_right (hMertens y hy) hcofactorNonneg
    _ ≤ (C / Real.log (y : ℝ)) *
        (2 * ((m : ℝ) / Nat.totient m)) := by
      exact mul_le_mul_of_nonneg_left
        (residualCofactorInverseProduct_le_two_mul_ratio hm)
        (div_nonneg hC.le hlog.le)
    _ = (2 * C) * ((m : ℝ) / Nat.totient m) /
        Real.log (y : ℝ) := by ring

/-! ## End-to-end residual-fibre estimate -/

theorem residualPrimeCandidates_card_le_primeCounting
    {U z m : ℕ} (hm : 0 < m) :
    (residualPrimeCandidates U z m).card ≤
      Nat.primeCounting (U / m) := by
  rw [residualPrimeCandidates_eq_interval hm,
    ← Nat.primesLE_card_eq_primeCounting]
  apply Finset.card_le_card
  intro p hp
  have hpData := Finset.mem_filter.mp hp
  exact Nat.mem_primesLE.mpr ⟨(Finset.mem_Ioc.mp hpData.1).2,
    hpData.2⟩

/-- Combining the finite beta sieve, Mertens, and the uniform Chebyshev
upper bound gives the full pointwise residual-fibre estimate, with only the
two Bombieri--Vinogradov endpoint errors left unevaluated. -/
theorem exists_residualPrimeFiber_beta_mertens_upper_bound :
    ∃ Aβ Cπ CV : ℝ,
      1 ≤ Aβ ∧ 0 < Cπ ∧ 0 < CV ∧
      ∀ {theta B CBV : ℝ} {X₀ U y z m S : ℕ},
        0 < m → Even m → z ≤ U / m → 1 < y → 101 ≤ S →
        Real.log Aβ ≤ 2 * (S - 100 : ℕ) / 99 →
        BoundedGaps.Maynard.PrimeLevelWitness theta B CBV X₀ →
        X₀ ≤ U / m → X₀ ≤ z →
        y ^ S ≤ BoundedGaps.Maynard.modulusCutoff theta (U / m) →
        y ^ S ≤ BoundedGaps.Maynard.modulusCutoff theta z →
        2 ≤ U / m →
        let eta := (4 * Aβ / 3) * (1 / 4 : ℝ) ^ (S - 100)
        ((residualPrimeFiber U y z m).card : ℝ) ≤
          (Cπ * ((U / m : ℕ) : ℝ) /
              Real.log ((U / m : ℕ) : ℝ)) *
            ((1 + eta) *
              (CV * ((m : ℝ) / Nat.totient m) /
                Real.log (y : ℝ))) +
          CBV * ((U / m : ℕ) : ℝ) /
              Real.rpow (Real.log ((U / m : ℕ) : ℝ)) B +
            CBV * (z : ℝ) /
              Real.rpow (Real.log (z : ℝ)) B := by
  obtain ⟨Aβ, hAβ, hbeta⟩ := exists_residualPrimeFiber_beta_upper_bound
  obtain ⟨Cπ, hCπ, hprime⟩ :=
    Erdos387.PrimeReciprocal.exists_uniform_primeCounting_le_div_log_all
  obtain ⟨CV, hCV, hlocal⟩ :=
    exists_residualPrimeLocalEulerProduct_mertens_bound
  refine ⟨Aβ, Cπ, CV, hAβ, hCπ, hCV, ?_⟩
  intro theta B CBV X₀ U y z m S hm hmEven hzU hy hS hlog hw
    hupper hlower hDupper hDlower hUtwo
  dsimp only
  have hbeta' := hbeta hm hmEven hzU hy hS hlog hw hupper hlower
    hDupper hDlower
  dsimp only at hbeta'
  have hyTwo : 2 ≤ y := by omega
  have hlocal' := hlocal hyTwo hm hmEven
  have hcountNat := residualPrimeCandidates_card_le_primeCounting
    (U := U) (z := z) hm
  have hcountCast :
      ((residualPrimeCandidates U z m).card : ℝ) ≤
        (Nat.primeCounting (U / m) : ℝ) := by
    exact_mod_cast hcountNat
  have hcount := hcountCast.trans (hprime (U / m) hUtwo)
  have heta : 0 ≤
      (4 * Aβ / 3) * (1 / 4 : ℝ) ^ (S - 100) := by
    positivity
  have hlocalMain :
      (1 + (4 * Aβ / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
          residualPrimeLocalEulerProduct y m ≤
        (1 + (4 * Aβ / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
          (CV * ((m : ℝ) / Nat.totient m) /
            Real.log (y : ℝ)) := by
    exact mul_le_mul_of_nonneg_left hlocal' (by linarith)
  calc
    ((residualPrimeFiber U y z m).card : ℝ) ≤
        ((residualPrimeCandidates U z m).card : ℝ) *
            ((1 + (4 * Aβ / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
              residualPrimeLocalEulerProduct y m) +
          CBV * ((U / m : ℕ) : ℝ) /
              Real.rpow (Real.log ((U / m : ℕ) : ℝ)) B +
            CBV * (z : ℝ) /
              Real.rpow (Real.log (z : ℝ)) B := hbeta'
    _ ≤ ((residualPrimeCandidates U z m).card : ℝ) *
            ((1 + (4 * Aβ / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
              (CV * ((m : ℝ) / Nat.totient m) /
                Real.log (y : ℝ))) +
          CBV * ((U / m : ℕ) : ℝ) /
              Real.rpow (Real.log ((U / m : ℕ) : ℝ)) B +
            CBV * (z : ℝ) /
              Real.rpow (Real.log (z : ℝ)) B := by
      have hmul := mul_le_mul_of_nonneg_left hlocalMain
        (Nat.cast_nonneg (residualPrimeCandidates U z m).card)
      simpa only [add_assoc, add_comm, add_left_comm] using
        add_le_add_right
          (add_le_add_right hmul
            (CBV * ((U / m : ℕ) : ℝ) /
              Real.rpow (Real.log ((U / m : ℕ) : ℝ)) B))
          (CBV * (z : ℝ) /
            Real.rpow (Real.log (z : ℝ)) B)
    _ ≤ (Cπ * ((U / m : ℕ) : ℝ) /
            Real.log ((U / m : ℕ) : ℝ)) *
          ((1 + (4 * Aβ / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
            (CV * ((m : ℝ) / Nat.totient m) /
              Real.log (y : ℝ))) +
        CBV * ((U / m : ℕ) : ℝ) /
            Real.rpow (Real.log ((U / m : ℕ) : ℝ)) B +
          CBV * (z : ℝ) /
            Real.rpow (Real.log (z : ℝ)) B := by
      have hmainNonneg : 0 ≤
          (1 + (4 * Aβ / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
            (CV * ((m : ℝ) / Nat.totient m) /
              Real.log (y : ℝ)) := by
        positivity
      have hmul := mul_le_mul_of_nonneg_right hcount hmainNonneg
      simpa only [add_assoc, add_comm, add_left_comm] using
        add_le_add_right
          (add_le_add_right hmul
            (CBV * ((U / m : ℕ) : ℝ) /
              Real.rpow (Real.log ((U / m : ℕ) : ℝ)) B))
          (CBV * (z : ℝ) /
            Real.rpow (Real.log (z : ℝ)) B)

end

end Erdos4
