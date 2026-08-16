import Wikipedia.GreenTao.Sieve.CFZCanonicalDivisorRankinTruncation

/-!
# Polylogarithmic growth of the canonical Rankin mass

The canonical coordinatewise-truncation estimate leaves a sharp arithmetic
Rankin mass.  This file proves that mass grows only polylogarithmically in
the selected CFZ, primorial, and reduced-residue regime.

There are two contributions.

* In the coordinatewise-truncated fibers, every divisor phase has norm at
  most one.  Every nonempty good-prime support costs at least `1 / p`, while
  a support at a prime dividing the primorial has zero density.  The
  truncated contribution is therefore bounded by the existing harmonic-LCM
  Euler majorant.
* The unrestricted Rpow coefficient mass factors over primes.  Its empty
  local support contributes one.  The total coefficient weight of all
  supports is at most `4 ^ m`, where `m` is the number of selected forms,
  and every nonempty support again costs `1 / p`.

The canonical carry-cell densities are nonnegative and sum exactly to one,
so these bounds are uniform in the carry vector.  Finally the existing
Selberg-scale estimate supplies one additional logarithm per selected form.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter Topology
open scoped BigOperators

/-! ## The canonical carry cells form a probability partition -/

/-- A canonical carry-cell density is its cardinality divided by the
cardinality of the ambient natural box. -/
theorem cfzCanonicalCarryCellDensity_eq_card_div
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (forms : κ → CFZFormIndex k)
    (carry : κ → ℤ) :
    cfzCanonicalCarryCellDensity (N := N) forms carry =
      ((cfzCanonicalCarryCell (N := N) forms carry).card : ℝ) /
        ∏ _v : CFZVariable k, (N : ℝ) := by
  unfold cfzCanonicalCarryCellDensity boxMean
  rw [boxSum_eq_sum_natBox]
  unfold cfzCanonicalCarryCell cfzCanonicalCarryIndicator
  simp

theorem cfzCanonicalCarryCellDensity_nonneg
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (forms : κ → CFZFormIndex k)
    (carry : κ → ℤ) :
    0 ≤ cfzCanonicalCarryCellDensity (N := N) forms carry := by
  rw [cfzCanonicalCarryCellDensity_eq_card_div]
  positivity

/-- The canonical carry-cell densities sum to one. -/
theorem sum_cfzCanonicalCarryCellDensity_eq_one
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (forms : κ → CFZFormIndex k) :
    ∑ carry ∈ cfzCanonicalCarryVectorChoices κ k,
        cfzCanonicalCarryCellDensity (N := N) forms carry = 1 := by
  simp_rw [cfzCanonicalCarryCellDensity_eq_card_div]
  rw [← Finset.sum_div]
  have hpartition :=
    sum_cfzCanonicalCarryCell_eq_sum_natBox
      (N := N) forms (fun _ => (1 : ℝ))
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hpartition
  rw [hpartition, card_natBox, Nat.cast_prod]
  exact div_self (by
    apply Finset.prod_ne_zero_iff.mpr
    intro v _hv
    exact_mod_cast (NeZero.ne N))

/-! ## Divisor phases and fixed-carry support densities -/

theorem pairedDivisorRankinWeight_nonneg
    {κ : Type*} [Fintype κ]
    (R : ℕ) (z : κ → ℕ × ℕ) :
    0 ≤ pairedDivisorRankinWeight R z := by
  unfold pairedDivisorRankinWeight
  positivity

/-- On a positive squarefree divisor family, every exact divisor-phase
weight is at most one. -/
theorem pairedDivisorRankinWeight_le_one
    {κ : Type*} [Fintype κ]
    {R : ℕ} (hR : 2 ≤ R)
    (z : κ → ℕ × ℕ)
    (hz : SquarefreePairedDivisorChoice z) :
    pairedDivisorRankinWeight R z ≤ 1 := by
  have hlog : 0 ≤ Real.log (R : ℝ) := by
    exact (Real.log_pos (by exact_mod_cast hR : (1 : ℝ) < R)).le
  have hexponent :
      -(Real.log (R : ℝ))⁻¹ ≤ 0 := by
    exact neg_nonpos.mpr (inv_nonneg.mpr hlog)
  unfold pairedDivisorRankinWeight
  apply Finset.prod_le_one
  · intro q _hq
    positivity
  · intro q _hq
    apply mul_le_one₀
    · exact
        Real.rpow_le_one_of_one_le_of_nonpos
          (by
            exact_mod_cast
              (Nat.one_le_iff_ne_zero.mpr (hz q).1.ne_zero))
          hexponent
    · positivity
    · exact
        Real.rpow_le_one_of_one_le_of_nonpos
          (by
            exact_mod_cast
              (Nat.one_le_iff_ne_zero.mpr (hz q).2.ne_zero))
          hexponent

/-- For a selected carry-adjusted family, every nonempty local support has
density at most `1 / p` once primes outside `W` are above the exceptional
cutoff.  Supports at primes dividing `W` vanish. -/
theorem selectedCFZCarryVectorPrimeSupportDensity_le_inv
    {k N W b : ℕ} [NeZero N]
    (hk : 2 ≤ k) (hWb : W.Coprime b)
    (e : LinearFormsExponent k)
    (carry : SelectedCFZFormIndex e → ℤ)
    (hcover :
      ∀ p : ℕ, p.Prime → ¬p ∣ W →
        exceptionalPrimeBound
            (fun q : CFZFormIndex k => cfzAffineForm q) < p)
    {p : ℕ} [NeZero p] (hp : p.Prime)
    (s : Finset (SelectedCFZFormIndex e))
    (hs : s.Nonempty) :
    affineFamilyZeroDensity p
        (cfzCarryAdjustedFamilyAtVector
          N W b (fun q : SelectedCFZFormIndex e => q.1) carry)
        s ≤
      (1 : ℝ) / (p : ℝ) := by
  change
    affineFamilyZeroDensity p
        (fun q : SelectedCFZFormIndex e =>
          cfzCarryAdjustedAffineForm N W b q.1 (carry q))
        s ≤
      (1 : ℝ) / (p : ℝ)
  by_cases hpW : p ∣ W
  · rw [affineFamilyZeroDensity_cfzCarryAdjusted_eq_zero_of_prime_dvd
      N W b hp hpW hWb
      (fun q : SelectedCFZFormIndex e => q.1) carry s hs]
    positivity
  · have hlarge :
        exceptionalPrimeBound
            (fun q : CFZFormIndex k => cfzAffineForm q) <
          p :=
      hcover p hp hpW
    have hnonzero :
        AffineNonzeroGoodPrime p
          (fun q : SelectedCFZFormIndex e =>
            cfzCarryAdjustedAffineForm N W b q.1 (carry q)) := by
      exact
        affineNonzeroGoodPrime_cfzCarryAdjusted
          N W b (fun q : SelectedCFZFormIndex e => q.1) carry
          (selectedCFZAffineNonzeroGoodPrime hk hp hlarge e)
          hpW
    have hrank :
        AffineRankTwoGoodPrime p
          (fun q : SelectedCFZFormIndex e =>
            cfzCarryAdjustedAffineForm N W b q.1 (carry q)) := by
      exact
        affineRankTwoGoodPrime_cfzCarryAdjusted
          N W b (fun q : SelectedCFZFormIndex e => q.1) carry
          (selectedCFZAffineRankTwoGoodPrime hk hp hlarge e)
          hpW
    by_cases hone : s.card = 1
    · obtain ⟨q, rfl⟩ := Finset.card_eq_one.mp hone
      exact
        (affineFamilyZeroDensity_singleton_of_nonzeroGoodPrime
          hnonzero q).le
    · have hcard : 2 ≤ s.card := by
        have hpos := hs.card_pos
        omega
      have hnontrivial : s.Nontrivial :=
        Finset.one_lt_card_iff_nontrivial.mp hcard
      calc
        affineFamilyZeroDensity p
            (fun q : SelectedCFZFormIndex e =>
              cfzCarryAdjustedAffineForm N W b q.1 (carry q))
            s ≤
            (1 : ℝ) / (p : ℝ) ^ 2 :=
          affineFamilyZeroDensity_le_inv_sq_of_goodPrime
            hrank s hnontrivial
        _ ≤ (1 : ℝ) / (p : ℝ) := by
          apply one_div_le_one_div_of_le
          · exact_mod_cast hp.pos
          · have hpone : (1 : ℝ) ≤ (p : ℝ) := by
              exact_mod_cast hp.one_le
            nlinarith

theorem norm_primeAffineFamilyZeroDensity_selectedCarry_le_inv
    {k N W b : ℕ} [NeZero N]
    (hk : 2 ≤ k) (hWb : W.Coprime b)
    (e : LinearFormsExponent k)
    (carry : SelectedCFZFormIndex e → ℤ)
    (hcover :
      ∀ p : ℕ, p.Prime → ¬p ∣ W →
        exceptionalPrimeBound
            (fun q : CFZFormIndex k => cfzAffineForm q) < p)
    (p : Nat.Primes)
    (s : Finset (SelectedCFZFormIndex e))
    (hs : s.Nonempty) :
    ‖primeAffineFamilyZeroDensity
        (cfzCarryAdjustedFamilyAtVector
          N W b (fun q : SelectedCFZFormIndex e => q.1) carry)
        (p : ℕ) s‖ ≤
      (1 : ℝ) / (p : ℝ) := by
  letI : NeZero (p : ℕ) := ⟨p.prop.ne_zero⟩
  rw [primeAffineFamilyZeroDensity_of_prime _ p.prop,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg
      (affineFamilyZeroDensity_nonneg
        (p : ℕ)
        (cfzCarryAdjustedFamilyAtVector
          N W b (fun q : SelectedCFZFormIndex e => q.1) carry)
        s)]
  exact
    selectedCFZCarryVectorPrimeSupportDensity_le_inv
      hk hWb e carry hcover p.prop s hs

/-- The density of an actual squarefree support assignment is at most the
reciprocal paired divisor LCM. -/
theorem norm_fixedFamilyPrimeSupportDensity_selectedCarry_assignment_le_inv_lcm
    {k N W b : ℕ} [NeZero N]
    (hk : 2 ≤ k) (hWb : W.Coprime b)
    (e : LinearFormsExponent k)
    (carry : SelectedCFZFormIndex e → ℤ)
    (hcover :
      ∀ p : ℕ, p.Prime → ¬p ∣ W →
        exceptionalPrimeBound
            (fun q : CFZFormIndex k => cfzAffineForm q) < p)
    {R : ℕ}
    {z : SelectedCFZFormIndex e → ℕ × ℕ}
    (hzR : z ∈ smoothDivisorFamilyChoices
      (SelectedCFZFormIndex e) R)
    (hz : SquarefreePairedDivisorChoice z) :
    ‖fixedFamilyPrimeSupportDensity
        (cfzCarryAdjustedFamilyAtVector
          N W b (fun q : SelectedCFZFormIndex e => q.1) carry)
        (fixedFamilyPrimeSupportAssignmentOf
          (primesLEAsPrimes R) z)‖ ≤
      (1 : ℝ) / (pairedDivisorLcm z : ℝ) := by
  rw [fixedFamilyPrimeSupportDensity_assignmentOf_eq_eulerProduct
    _ hzR hz, norm_prod]
  rw [← SmoothSieveCutoff.prod_inv_primeFactors_eq_inv_of_squarefree
    (squarefree_pairedDivisorLcm hz)]
  apply Finset.prod_le_prod
  · intro p _hp
    exact norm_nonneg _
  · intro p _hp
    letI : NeZero (p : ℕ) :=
      ⟨(Nat.prime_of_mem_primeFactors p.2).ne_zero⟩
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg
        (affineFamilyZeroDensity_nonneg
          (p : ℕ)
          (cfzCarryAdjustedFamilyAtVector
            N W b (fun q : SelectedCFZFormIndex e => q.1) carry)
          (pairedPrimeSupport z p))]
    exact
      selectedCFZCarryVectorPrimeSupportDensity_le_inv
        hk hWb e carry hcover
        (Nat.prime_of_mem_primeFactors p.2)
        (pairedPrimeSupport z p)
        (((mem_primeFactors_pairedDivisorLcm_iff
          hz (p : ℕ)).mp p.2).2)

/-! ## The coordinatewise-truncated part -/

/-- Reorganize the sum of exact Rankin fiber masses by the underlying
squarefree paired divisor family. -/
theorem sum_coordinatewiseTruncatedSupportRankinMass_mul_norm_density
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (R : ℕ) (forms : κ → AffineForm ι ℤ)
    (P : Finset Nat.Primes) :
    ∑ support ∈ fixedFamilyPrimeSupportAssignmentChoices κ P,
        coordinatewiseTruncatedSupportRankinMass R P support *
          ‖fixedFamilyPrimeSupportDensity forms support‖ =
      ∑ z ∈
          SmoothSieveCutoff.squarefreeSmoothPairedDivisorChoices κ R,
        pairedDivisorRankinWeight R z *
          ‖fixedFamilyPrimeSupportDensity forms
            (fixedFamilyPrimeSupportAssignmentOf P z)‖ := by
  classical
  let s :=
    SmoothSieveCutoff.squarefreeSmoothPairedDivisorChoices κ R
  let choices := fixedFamilyPrimeSupportAssignmentChoices κ P
  let encode :
      (κ → ℕ × ℕ) → FixedFamilyPrimeSupportAssignment κ P :=
    fixedFamilyPrimeSupportAssignmentOf P
  have hmaps : ∀ z ∈ s, encode z ∈ choices := by
    intro z _hz
    exact fixedFamilyPrimeSupportAssignmentOf_mem_choices P z
  calc
    (∑ support ∈ choices,
        coordinatewiseTruncatedSupportRankinMass R P support *
          ‖fixedFamilyPrimeSupportDensity forms support‖) =
        ∑ support ∈ choices,
          ∑ z ∈ s with encode z = support,
            pairedDivisorRankinWeight R z *
              ‖fixedFamilyPrimeSupportDensity forms support‖ := by
      apply Finset.sum_congr rfl
      intro support _hsupport
      rw [← Finset.sum_mul]
      rfl
    _ =
        ∑ support ∈ choices,
          ∑ z ∈ s with encode z = support,
            pairedDivisorRankinWeight R z *
              ‖fixedFamilyPrimeSupportDensity forms (encode z)‖ := by
      apply Finset.sum_congr rfl
      intro support _hsupport
      apply Finset.sum_congr rfl
      intro z hz
      rw [(Finset.mem_filter.mp hz).2]
    _ =
        ∑ z ∈ s,
          pairedDivisorRankinWeight R z *
            ‖fixedFamilyPrimeSupportDensity forms (encode z)‖ :=
      Finset.sum_fiberwise_of_maps_to hmaps
        (fun z =>
          pairedDivisorRankinWeight R z *
            ‖fixedFamilyPrimeSupportDensity forms (encode z)‖)
    _ = _ := rfl

/-- Uniform fixed-carry harmonic-LCM bound for the truncated fiber mass. -/
theorem selectedCFZCarryVectorTruncatedRankinMass_le_harmonicLcmMass
    {k N W b : ℕ} [NeZero N]
    (hk : 2 ≤ k) (hWb : W.Coprime b)
    (e : LinearFormsExponent k)
    (carry : SelectedCFZFormIndex e → ℤ)
    (hcover :
      ∀ p : ℕ, p.Prime → ¬p ∣ W →
        exceptionalPrimeBound
            (fun q : CFZFormIndex k => cfzAffineForm q) < p)
    {R : ℕ} (hR : 2 ≤ R) :
    ∑ support ∈ fixedFamilyPrimeSupportAssignmentChoices
        (SelectedCFZFormIndex e) (primesLEAsPrimes R),
      coordinatewiseTruncatedSupportRankinMass
          R (primesLEAsPrimes R) support *
        ‖fixedFamilyPrimeSupportDensity
          (cfzCarryAdjustedFamilyAtVector
            N W b (fun q : SelectedCFZFormIndex e => q.1) carry)
          support‖ ≤
      SmoothSieveCutoff.pairedDivisorHarmonicLcmMass
        (κ := SelectedCFZFormIndex e) R := by
  rw [sum_coordinatewiseTruncatedSupportRankinMass_mul_norm_density]
  rw [SmoothSieveCutoff.pairedDivisorHarmonicLcmMass_eq_sum_squarefree]
  apply Finset.sum_le_sum
  intro z hz
  have hzData :=
    SmoothSieveCutoff.mem_squarefreeSmoothPairedDivisorChoices.mp hz
  have hdensity :
      ‖fixedFamilyPrimeSupportDensity
          (cfzCarryAdjustedFamilyAtVector
            N W b (fun q : SelectedCFZFormIndex e => q.1) carry)
          (fixedFamilyPrimeSupportAssignmentOf
            (primesLEAsPrimes R) z)‖ ≤
        (pairedDivisorLcm z : ℝ)⁻¹ := by
    simpa only [one_div] using
      norm_fixedFamilyPrimeSupportDensity_selectedCarry_assignment_le_inv_lcm
        (N := N) hk hWb e carry hcover hzData.1 hzData.2
  exact
    mul_le_mul
      (pairedDivisorRankinWeight_le_one hR z hzData.2)
      hdensity
      (norm_nonneg _)
      (by positivity)

/-! ## The unrestricted Rpow part -/

/-- The natural coefficient paying for every local paired occurrence
pattern.  We use `4 ^ m`, retaining one harmless extra `1 / p` beyond the
sharp `4 ^ m - 1`; this makes the local empty-support split transparent. -/
def selectedCFZCanonicalRankinEulerCoefficient
    {k : ℕ} (e : LinearFormsExponent k) : ℕ :=
  4 ^ Fintype.card (SelectedCFZFormIndex e)

/-- Euler majorant for the unrestricted Rpow support mass. -/
noncomputable def selectedCFZCanonicalRankinRpowEulerMajorant
    {k : ℕ} (e : LinearFormsExponent k) (R : ℕ) : ℝ :=
  ∏ p ∈ Nat.primesLE R,
    (1 +
      (selectedCFZCanonicalRankinEulerCoefficient e : ℝ) /
        (p : ℝ))

theorem selectedCFZCanonicalRankinRpowEulerMajorant_nonneg
    {k : ℕ} (e : LinearFormsExponent k) (R : ℕ) :
    0 ≤ selectedCFZCanonicalRankinRpowEulerMajorant e R := by
  unfold selectedCFZCanonicalRankinRpowEulerMajorant
  exact Finset.prod_nonneg fun p _hp => by positivity

/-- Exact primewise factorization of the unrestricted Rpow support mass. -/
theorem
    sum_fixedFamilyPrimeSupportRpowCoefficientMass_mul_norm_density_eq_prod
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (R : ℕ) (forms : κ → AffineForm ι ℤ)
    (P : Finset Nat.Primes) :
    ∑ support ∈ fixedFamilyPrimeSupportAssignmentChoices κ P,
        fixedFamilyPrimeSupportRpowCoefficientMass R support *
          ‖fixedFamilyPrimeSupportDensity forms support‖ =
      ∏ p : {p // p ∈ P},
        ∑ s ∈ (Finset.univ : Finset κ).powerset,
          (3 * (p : ℝ) ^ (-(Real.log (R : ℝ))⁻¹)) ^ s.card *
            ‖primeAffineFamilyZeroDensity forms (p : ℕ) s‖ := by
  classical
  unfold fixedFamilyPrimeSupportAssignmentChoices
    fixedFamilyPrimeSupportRpowCoefficientMass
    fixedFamilyPrimeSupportDensity
  simp_rw [norm_prod, ← Finset.prod_mul_distrib]
  rw [Finset.prod_univ_sum]

/-- Binomial expansion of the total coefficient weight over all supports. -/
theorem sum_three_pow_card_powerset
    (κ : Type*) [Fintype κ] [DecidableEq κ] :
    ∑ s ∈ (Finset.univ : Finset κ).powerset,
        (3 : ℝ) ^ s.card =
      (4 : ℝ) ^ Fintype.card κ := by
  calc
    (∑ s ∈ (Finset.univ : Finset κ).powerset,
        (3 : ℝ) ^ s.card) =
        ∑ s ∈ (Finset.univ : Finset κ).powerset,
          ∏ _q ∈ s, (3 : ℝ) := by
      simp
    _ = ∏ q ∈ (Finset.univ : Finset κ), (1 + (3 : ℝ)) := by
      exact (Finset.prod_one_add (Finset.univ : Finset κ)).symm
    _ = (4 : ℝ) ^ Fintype.card κ := by
      norm_num

/-- At a prime in the supported range, the Rpow phase base is at most
three. -/
theorem three_mul_prime_rpow_neg_inv_log_le_three
    {R p : ℕ} (hR : 2 ≤ R) (hp : p.Prime) :
    3 * (p : ℝ) ^ (-(Real.log (R : ℝ))⁻¹) ≤ 3 := by
  have hlog : 0 ≤ Real.log (R : ℝ) :=
    (Real.log_pos (by exact_mod_cast hR : (1 : ℝ) < R)).le
  have hexponent :
      -(Real.log (R : ℝ))⁻¹ ≤ 0 :=
    neg_nonpos.mpr (inv_nonneg.mpr hlog)
  have hrpow :
      (p : ℝ) ^ (-(Real.log (R : ℝ))⁻¹) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos
      (by exact_mod_cast hp.one_le) hexponent
  linarith

/-- One fixed-carry local Rpow mass is bounded by
`1 + 4 ^ m / p`. -/
theorem selectedCFZCarryVectorRpowLocalMass_le
    {k N W b : ℕ} [NeZero N]
    (hk : 2 ≤ k) (hWb : W.Coprime b)
    (e : LinearFormsExponent k)
    (carry : SelectedCFZFormIndex e → ℤ)
    (hcover :
      ∀ p : ℕ, p.Prime → ¬p ∣ W →
        exceptionalPrimeBound
            (fun q : CFZFormIndex k => cfzAffineForm q) < p)
    {R : ℕ} (hR : 2 ≤ R)
    (p : Nat.Primes) :
    (∑ s ∈
        (Finset.univ : Finset (SelectedCFZFormIndex e)).powerset,
      (3 * ((p : ℕ) : ℝ) ^ (-(Real.log (R : ℝ))⁻¹)) ^ s.card *
        ‖primeAffineFamilyZeroDensity
          (cfzCarryAdjustedFamilyAtVector
            N W b (fun q : SelectedCFZFormIndex e => q.1) carry)
          (p : ℕ) s‖) ≤
      1 +
        (selectedCFZCanonicalRankinEulerCoefficient e : ℝ) /
          ((p : ℕ) : ℝ) := by
  letI : NeZero (p : ℕ) := ⟨p.prop.ne_zero⟩
  let B : ℝ :=
    3 * ((p : ℕ) : ℝ) ^ (-(Real.log (R : ℝ))⁻¹)
  have hB0 : 0 ≤ B := by
    unfold B
    positivity
  have hB3 : B ≤ 3 := by
    exact three_mul_prime_rpow_neg_inv_log_le_three hR p.prop
  calc
    (∑ s ∈
        (Finset.univ : Finset (SelectedCFZFormIndex e)).powerset,
      B ^ s.card *
        ‖primeAffineFamilyZeroDensity
          (cfzCarryAdjustedFamilyAtVector
            N W b (fun q : SelectedCFZFormIndex e => q.1) carry)
          (p : ℕ) s‖) ≤
        (∑ s ∈
          (Finset.univ : Finset (SelectedCFZFormIndex e)).powerset,
          ((if s = ∅ then 1 else 0) +
            (3 : ℝ) ^ s.card / ((p : ℕ) : ℝ))) := by
      apply Finset.sum_le_sum
      intro s hs
      by_cases hsempty : s = ∅
      · subst s
        simp [primeAffineFamilyZeroDensity, p.prop]
      · have hsnonempty : s.Nonempty :=
          Finset.nonempty_iff_ne_empty.mpr hsempty
        have hpow : B ^ s.card ≤ (3 : ℝ) ^ s.card :=
          pow_le_pow_left₀ hB0 hB3 s.card
        have hdensity :=
          norm_primeAffineFamilyZeroDensity_selectedCarry_le_inv
            (N := N) hk hWb e carry hcover p s hsnonempty
        calc
          B ^ s.card *
              ‖primeAffineFamilyZeroDensity
                (cfzCarryAdjustedFamilyAtVector
                  N W b
                  (fun q : SelectedCFZFormIndex e => q.1) carry)
                (p : ℕ) s‖ ≤
              (3 : ℝ) ^ s.card * ((1 : ℝ) / ((p : ℕ) : ℝ)) :=
            mul_le_mul hpow hdensity (norm_nonneg _)
              (pow_nonneg (by norm_num) s.card)
          _ =
              (if s = ∅ then 1 else 0) +
                (3 : ℝ) ^ s.card / ((p : ℕ) : ℝ) := by
            simp [hsempty, div_eq_mul_inv]
    _ =
        1 +
          (4 : ℝ) ^
              Fintype.card (SelectedCFZFormIndex e) /
            ((p : ℕ) : ℝ) := by
      rw [Finset.sum_add_distrib, ← Finset.sum_div,
        sum_three_pow_card_powerset]
      simp
    _ =
        1 +
          (selectedCFZCanonicalRankinEulerCoefficient e : ℝ) /
            ((p : ℕ) : ℝ) := by
      simp [selectedCFZCanonicalRankinEulerCoefficient]

/-- The full unrestricted Rpow support mass of one carry vector is bounded
by its finite prime Euler majorant. -/
theorem selectedCFZCarryVectorRpowRankinMass_le_eulerMajorant
    {k N W b : ℕ} [NeZero N]
    (hk : 2 ≤ k) (hWb : W.Coprime b)
    (e : LinearFormsExponent k)
    (carry : SelectedCFZFormIndex e → ℤ)
    (hcover :
      ∀ p : ℕ, p.Prime → ¬p ∣ W →
        exceptionalPrimeBound
            (fun q : CFZFormIndex k => cfzAffineForm q) < p)
    {R : ℕ} (hR : 2 ≤ R) :
    ∑ support ∈ fixedFamilyPrimeSupportAssignmentChoices
        (SelectedCFZFormIndex e) (primesLEAsPrimes R),
      fixedFamilyPrimeSupportRpowCoefficientMass R support *
        ‖fixedFamilyPrimeSupportDensity
          (cfzCarryAdjustedFamilyAtVector
            N W b (fun q : SelectedCFZFormIndex e => q.1) carry)
          support‖ ≤
      selectedCFZCanonicalRankinRpowEulerMajorant e R := by
  rw [
    sum_fixedFamilyPrimeSupportRpowCoefficientMass_mul_norm_density_eq_prod]
  unfold selectedCFZCanonicalRankinRpowEulerMajorant
  calc
    (∏ p : {p // p ∈ primesLEAsPrimes R},
        ∑ s ∈
          (Finset.univ : Finset (SelectedCFZFormIndex e)).powerset,
          (3 * (p : ℝ) ^ (-(Real.log (R : ℝ))⁻¹)) ^ s.card *
            ‖primeAffineFamilyZeroDensity
              (cfzCarryAdjustedFamilyAtVector
                N W b (fun q : SelectedCFZFormIndex e => q.1) carry)
              (p : ℕ) s‖) ≤
        ∏ p : {p // p ∈ primesLEAsPrimes R},
          (1 +
            (selectedCFZCanonicalRankinEulerCoefficient e : ℝ) /
              (p : ℝ)) := by
      apply Finset.prod_le_prod
      · intro p _hp
        exact Finset.sum_nonneg fun s _hs =>
          mul_nonneg (pow_nonneg (by positivity) _)
            (norm_nonneg _)
      · intro p _hp
        exact
          selectedCFZCarryVectorRpowLocalMass_le
            (N := N) hk hWb e carry hcover hR p
    _ =
        ∏ p ∈ primesLEAsPrimes R,
          (1 +
            (selectedCFZCanonicalRankinEulerCoefficient e : ℝ) /
              ((p : ℕ) : ℝ)) := by
      exact
        Finset.prod_coe_sort
          (primesLEAsPrimes R)
          (fun p : Nat.Primes =>
            1 +
              (selectedCFZCanonicalRankinEulerCoefficient e : ℝ) /
                ((p : ℕ) : ℝ))
    _ =
        ∏ p ∈ Nat.primesLE R,
          (1 +
            (selectedCFZCanonicalRankinEulerCoefficient e : ℝ) /
              (p : ℝ)) := by
      exact
        prod_primesLEAsPrimes R
          (fun p =>
            1 +
              (selectedCFZCanonicalRankinEulerCoefficient e : ℝ) /
                (p : ℝ))

/-! ## Fixed-family and carry-averaged mass bounds -/

/-- Both pieces of the fixed-family Rankin mass are controlled by their
respective finite Euler majorants. -/
theorem selectedCFZCarryVectorCoordinatewiseRankinMass_le
    {k N W b : ℕ} [NeZero N]
    (hk : 2 ≤ k) (hWb : W.Coprime b)
    (e : LinearFormsExponent k)
    (carry : SelectedCFZFormIndex e → ℤ)
    (hcover :
      ∀ p : ℕ, p.Prime → ¬p ∣ W →
        exceptionalPrimeBound
            (fun q : CFZFormIndex k => cfzAffineForm q) < p)
    {R : ℕ} (hR : 2 ≤ R) :
    fixedFamilyCoordinatewiseTruncationRankinMass R
        (cfzCarryAdjustedFamilyAtVector
          N W b (fun q : SelectedCFZFormIndex e => q.1) carry)
        (primesLEAsPrimes R) ≤
      SmoothSieveCutoff.pairedDivisorHarmonicEulerMajorant
          (SelectedCFZFormIndex e) R +
        selectedCFZCanonicalRankinRpowEulerMajorant e R := by
  unfold fixedFamilyCoordinatewiseTruncationRankinMass
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib]
  exact add_le_add
    ((selectedCFZCarryVectorTruncatedRankinMass_le_harmonicLcmMass
      (N := N) hk hWb e carry hcover hR).trans
        (SmoothSieveCutoff.pairedDivisorHarmonicLcmMass_le_eulerMajorant
          R))
    (selectedCFZCarryVectorRpowRankinMass_le_eulerMajorant
      (N := N) hk hWb e carry hcover hR)

/-- The harmonic Euler coefficient is dominated by the slightly enlarged
Rpow coefficient. -/
theorem pairedDivisorHarmonicEulerMajorant_selected_le_rankinRpow
    {k : ℕ} (e : LinearFormsExponent k) (R : ℕ) :
    SmoothSieveCutoff.pairedDivisorHarmonicEulerMajorant
        (SelectedCFZFormIndex e) R ≤
      selectedCFZCanonicalRankinRpowEulerMajorant e R := by
  let m := Fintype.card (SelectedCFZFormIndex e)
  have hcoefficient :
      2 ^ (2 * m) - 1 ≤ 4 ^ m := by
    calc
      2 ^ (2 * m) - 1 ≤ 2 ^ (2 * m) :=
        Nat.sub_le _ _
      _ = 4 ^ m := by
        rw [pow_mul]
        norm_num
  unfold SmoothSieveCutoff.pairedDivisorHarmonicEulerMajorant
    selectedCFZCanonicalRankinRpowEulerMajorant
    selectedCFZCanonicalRankinEulerCoefficient
  change
    (∏ p ∈ Nat.primesLE R,
      (1 + (((2 ^ (2 * m) - 1 : ℕ) : ℝ) / (p : ℝ)))) ≤
      ∏ p ∈ Nat.primesLE R,
        (1 + (((4 ^ m : ℕ) : ℝ) / (p : ℝ)))
  apply Finset.prod_le_prod
  · intro p _hp
    positivity
  · intro p _hp
    gcongr

/-- The carry-cell probability partition removes all dependence on the
number of possible carry vectors. -/
theorem cfzCanonicalCarryTruncationRankinMass_le_two_rpowEuler
    {k N W b : ℕ} [NeZero N]
    (hk : 2 ≤ k) (hWb : W.Coprime b)
    (e : LinearFormsExponent k)
    (hcover :
      ∀ p : ℕ, p.Prime → ¬p ∣ W →
        exceptionalPrimeBound
            (fun q : CFZFormIndex k => cfzAffineForm q) < p)
    {R : ℕ} (hR : 2 ≤ R) :
    cfzCanonicalCarryTruncationRankinMass
        (N := N) W b R
        (fun q : SelectedCFZFormIndex e => q.1) ≤
      2 * selectedCFZCanonicalRankinRpowEulerMajorant e R := by
  unfold cfzCanonicalCarryTruncationRankinMass
  have hcell :
      ∀ carry ∈
          cfzCanonicalCarryVectorChoices
            (SelectedCFZFormIndex e) k,
        |cfzCanonicalCarryCellDensity
            (N := N)
            (fun q : SelectedCFZFormIndex e => q.1) carry| *
            fixedFamilyCoordinatewiseTruncationRankinMass R
              (cfzCarryAdjustedFamilyAtVector N W b
                (fun q : SelectedCFZFormIndex e => q.1) carry)
              (primesLEAsPrimes R) ≤
          cfzCanonicalCarryCellDensity
              (N := N)
              (fun q : SelectedCFZFormIndex e => q.1) carry *
            (2 * selectedCFZCanonicalRankinRpowEulerMajorant e R) := by
    intro carry _hcarry
    have hdensity :=
      cfzCanonicalCarryCellDensity_nonneg
        (N := N) (fun q : SelectedCFZFormIndex e => q.1) carry
    rw [abs_of_nonneg hdensity]
    apply mul_le_mul_of_nonneg_left _ hdensity
    calc
      fixedFamilyCoordinatewiseTruncationRankinMass R
          (cfzCarryAdjustedFamilyAtVector N W b
            (fun q : SelectedCFZFormIndex e => q.1) carry)
          (primesLEAsPrimes R) ≤
          SmoothSieveCutoff.pairedDivisorHarmonicEulerMajorant
              (SelectedCFZFormIndex e) R +
            selectedCFZCanonicalRankinRpowEulerMajorant e R :=
        selectedCFZCarryVectorCoordinatewiseRankinMass_le
          (N := N) hk hWb e carry hcover hR
      _ ≤
          selectedCFZCanonicalRankinRpowEulerMajorant e R +
            selectedCFZCanonicalRankinRpowEulerMajorant e R :=
        add_le_add
          (pairedDivisorHarmonicEulerMajorant_selected_le_rankinRpow
            e R)
          le_rfl
      _ = 2 * selectedCFZCanonicalRankinRpowEulerMajorant e R := by
        ring
  calc
    (∑ carry ∈
        cfzCanonicalCarryVectorChoices
          (SelectedCFZFormIndex e) k,
      |cfzCanonicalCarryCellDensity
          (N := N)
          (fun q : SelectedCFZFormIndex e => q.1) carry| *
        fixedFamilyCoordinatewiseTruncationRankinMass R
          (cfzCarryAdjustedFamilyAtVector N W b
            (fun q : SelectedCFZFormIndex e => q.1) carry)
          (primesLEAsPrimes R)) ≤
        ∑ carry ∈
          cfzCanonicalCarryVectorChoices
            (SelectedCFZFormIndex e) k,
          cfzCanonicalCarryCellDensity
              (N := N)
              (fun q : SelectedCFZFormIndex e => q.1) carry *
            (2 * selectedCFZCanonicalRankinRpowEulerMajorant e R) :=
      Finset.sum_le_sum hcell
    _ =
        (∑ carry ∈
          cfzCanonicalCarryVectorChoices
            (SelectedCFZFormIndex e) k,
          cfzCanonicalCarryCellDensity
            (N := N)
            (fun q : SelectedCFZFormIndex e => q.1) carry) *
          (2 * selectedCFZCanonicalRankinRpowEulerMajorant e R) := by
      rw [Finset.sum_mul]
    _ = 2 * selectedCFZCanonicalRankinRpowEulerMajorant e R := by
      rw [sum_cfzCanonicalCarryCellDensity_eq_one]
      ring

/-! ## Primorial polylogarithmic bounds -/

/-- Total exponent after including one Selberg logarithm for each selected
form. -/
def selectedCFZCanonicalRankinPolylogExponent
    {k : ℕ} (e : LinearFormsExponent k) : ℕ :=
  Fintype.card (SelectedCFZFormIndex e) +
    3 * selectedCFZCanonicalRankinEulerCoefficient e

/-- Constant in the fully Selberg-scaled Rankin bound. -/
noncomputable def SmoothSieveCutoff.selectedCFZCanonicalRankinPolylogConstant
    {k : ℕ} (χ : SmoothSieveCutoff)
    (e : LinearFormsExponent k) : ℝ :=
  2 * χ.normalizer⁻¹ ^
    Fintype.card (SelectedCFZFormIndex e)

theorem SmoothSieveCutoff.selectedCFZCanonicalRankinPolylogConstant_nonneg
    {k : ℕ} (χ : SmoothSieveCutoff)
    (e : LinearFormsExponent k) :
    0 ≤ χ.selectedCFZCanonicalRankinPolylogConstant e := by
  unfold selectedCFZCanonicalRankinPolylogConstant
  exact mul_nonneg (by norm_num)
    (pow_nonneg (inv_nonneg.mpr χ.normalizer_pos.le) _)

theorem selectedCFZCanonicalRankinRpowEulerMajorant_le_polylog
    {k : ℕ} (e : LinearFormsExponent k)
    {R : ℕ} (hR : 2 ≤ R) :
    selectedCFZCanonicalRankinRpowEulerMajorant e R ≤
      (1 + Real.log R) ^
        (3 * selectedCFZCanonicalRankinEulerCoefficient e) := by
  unfold selectedCFZCanonicalRankinRpowEulerMajorant
  exact
    prod_primesLE_one_add_nat_div_le_one_add_log_pow
      (selectedCFZCanonicalRankinEulerCoefficient e) R hR

/-- Primorial specialization of the raw canonical Rankin-mass estimate. -/
theorem cfzCanonicalCarryTruncationRankinMass_primorial_le_polylog
    {k N w b : ℕ} [NeZero N]
    (hk : 2 ≤ k)
    (hbound :
      exceptionalPrimeBound
          (fun q : CFZFormIndex k => cfzAffineForm q) ≤ w)
    (hwb : (primorial w).Coprime b)
    (e : LinearFormsExponent k)
    {R : ℕ} (hR : 2 ≤ R) :
    cfzCanonicalCarryTruncationRankinMass
        (N := N) (primorial w) b R
        (fun q : SelectedCFZFormIndex e => q.1) ≤
      2 *
        (1 + Real.log R) ^
          (3 * selectedCFZCanonicalRankinEulerCoefficient e) := by
  have hcover :
      ∀ p : ℕ, p.Prime → ¬p ∣ primorial w →
        exceptionalPrimeBound
            (fun q : CFZFormIndex k => cfzAffineForm q) < p := by
    intro p hp hpW
    exact
      SmoothSieveCutoff.selectedCFZ_exceptionalPrime_covered_by_primorial
        hbound hp hpW
  exact
    (cfzCanonicalCarryTruncationRankinMass_le_two_rpowEuler
      (N := N) hk hwb e hcover hR).trans
      (mul_le_mul_of_nonneg_left
        (selectedCFZCanonicalRankinRpowEulerMajorant_le_polylog
          e hR)
        (by norm_num))

/-- **Scaled canonical Rankin-mass polylog bound.** -/
theorem
    SmoothSieveCutoff.selectedCFZCanonicalCarryScaledTruncationRankinMass_primorial_le_polylog
    {k N w b : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (hk : 2 ≤ k)
    (hbound :
      exceptionalPrimeBound
          (fun q : CFZFormIndex k => cfzAffineForm q) ≤ w)
    (hwb : (primorial w).Coprime b)
    (e : LinearFormsExponent k)
    {R : ℕ} (hR : 2 ≤ R) :
    χ.selectedCFZCanonicalCarryScaledTruncationRankinMass
        (N := N) (primorial w) b R e ≤
      χ.selectedCFZCanonicalRankinPolylogConstant e *
        (1 + Real.log R) ^
          selectedCFZCanonicalRankinPolylogExponent e := by
  let m := Fintype.card (SelectedCFZFormIndex e)
  let A := selectedCFZCanonicalRankinEulerCoefficient e
  have hbase :
      |normalizedSelbergScale
          χ.normalizer R (primorial w)| *
          |Real.log R ^ 2| ≤
        χ.normalizer⁻¹ * (1 + Real.log R) :=
    χ.abs_normalizedSelbergScale_mul_logSq_le hR w
  have hbaseNonneg :
      0 ≤
        |normalizedSelbergScale
            χ.normalizer R (primorial w)| *
          |Real.log R ^ 2| := by
    positivity
  have hlogNonneg : 0 ≤ 1 + Real.log R := by
    have hlog :
        0 ≤ Real.log R :=
      (Real.log_pos
        (by exact_mod_cast hR : (1 : ℝ) < R)).le
    linarith
  have hupperBaseNonneg :
      0 ≤ χ.normalizer⁻¹ * (1 + Real.log R) :=
    mul_nonneg
      (inv_nonneg.mpr χ.normalizer_pos.le) hlogNonneg
  have hraw :
      cfzCanonicalCarryTruncationRankinMass
          (N := N) (primorial w) b R
          (fun q : SelectedCFZFormIndex e => q.1) ≤
        2 * (1 + Real.log R) ^ (3 * A) := by
    simpa only [A] using
      cfzCanonicalCarryTruncationRankinMass_primorial_le_polylog
        (N := N) hk hbound hwb e hR
  have hrawNonneg :
      0 ≤
        cfzCanonicalCarryTruncationRankinMass
          (N := N) (primorial w) b R
          (fun q : SelectedCFZFormIndex e => q.1) :=
    cfzCanonicalCarryTruncationRankinMass_nonneg
      (primorial w) b R
      (fun q : SelectedCFZFormIndex e => q.1)
  unfold selectedCFZCanonicalCarryScaledTruncationRankinMass
    selectedCFZCanonicalRankinPolylogConstant
    selectedCFZCanonicalRankinPolylogExponent
  change
    |normalizedSelbergScale χ.normalizer R (primorial w)| ^ m *
        |Real.log R ^ 2| ^ m *
        cfzCanonicalCarryTruncationRankinMass
          (N := N) (primorial w) b R
          (fun q : SelectedCFZFormIndex e => q.1) ≤
      (2 * χ.normalizer⁻¹ ^ m) *
        (1 + Real.log R) ^ (m + 3 * A)
  calc
    |normalizedSelbergScale χ.normalizer R (primorial w)| ^ m *
          |Real.log R ^ 2| ^ m *
          cfzCanonicalCarryTruncationRankinMass
            (N := N) (primorial w) b R
            (fun q : SelectedCFZFormIndex e => q.1) =
        (|normalizedSelbergScale
            χ.normalizer R (primorial w)| *
          |Real.log R ^ 2|) ^ m *
          cfzCanonicalCarryTruncationRankinMass
            (N := N) (primorial w) b R
            (fun q : SelectedCFZFormIndex e => q.1) := by
      rw [mul_pow]
    _ ≤
        (χ.normalizer⁻¹ * (1 + Real.log R)) ^ m *
          (2 * (1 + Real.log R) ^ (3 * A)) := by
      exact
        mul_le_mul
          (pow_le_pow_left₀ hbaseNonneg hbase m)
          hraw hrawNonneg
          (pow_nonneg hupperBaseNonneg m)
    _ =
        (2 * χ.normalizer⁻¹ ^ m) *
          (1 + Real.log R) ^ (m + 3 * A) := by
      rw [mul_pow, pow_add]
      ring

/-- Eventual form expected by the growing-box Rankin-tail theorem. -/
theorem
    SmoothSieveCutoff.eventually_selectedCFZCanonicalCarryScaledTruncationRankinMass_primorial_le_polylog
    {k N w b : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (hk : 2 ≤ k)
    (hbound :
      exceptionalPrimeBound
          (fun q : CFZFormIndex k => cfzAffineForm q) ≤ w)
    (hwb : (primorial w).Coprime b)
    (e : LinearFormsExponent k) :
    ∀ᶠ R : ℕ in atTop,
      χ.selectedCFZCanonicalCarryScaledTruncationRankinMass
          (N := N) (primorial w) b R e ≤
        χ.selectedCFZCanonicalRankinPolylogConstant e *
          (1 + Real.log R) ^
            selectedCFZCanonicalRankinPolylogExponent e := by
  filter_upwards [eventually_ge_atTop 2] with R hR
  exact
    χ.selectedCFZCanonicalCarryScaledTruncationRankinMass_primorial_le_polylog
      (N := N) hk hbound hwb e hR

/-- The sharp complementary Fourier tail therefore tends to zero in the
primorial regime. -/
theorem
    SmoothSieveCutoff.tendsto_selectedCFZCanonicalCarryScaledTruncationTailNorm_sqrt_log_primorial
    {k N w b : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (hk : 2 ≤ k)
    (hbound :
      exceptionalPrimeBound
          (fun q : CFZFormIndex k => cfzAffineForm q) ≤ w)
    (hwb : (primorial w).Coprime b)
    (e : LinearFormsExponent k) :
    Tendsto
      (fun R : ℕ =>
        χ.selectedCFZCanonicalCarryScaledTruncationTailNorm
          (N := N) (primorial w) b R e
          (Real.sqrt (Real.log R)))
      atTop (𝓝 0) := by
  exact
    χ.tendsto_selectedCFZCanonicalCarryScaledTruncationTailNorm_sqrt_log_of_polylog
      (N := N) (primorial w) b e
      (selectedCFZCanonicalRankinPolylogExponent e)
      (χ.selectedCFZCanonicalRankinPolylogConstant e)
      (χ.selectedCFZCanonicalRankinPolylogConstant_nonneg e)
      (χ.eventually_selectedCFZCanonicalCarryScaledTruncationRankinMass_primorial_le_polylog
        (N := N) hk hbound hwb e)

/-- With the independent full-space cancellation input, the growing
interior Fourier-box norm tends to zero as well. -/
theorem
    SmoothSieveCutoff.tendsto_selectedCFZCanonicalCarryScaledTruncationBoxNorm_sqrt_log_primorial_of_integral_zero
    {k N w b : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (hk : 2 ≤ k)
    (hbound :
      exceptionalPrimeBound
          (fun q : CFZFormIndex k => cfzAffineForm q) ≤ w)
    (hwb : (primorial w).Coprime b)
    (e : LinearFormsExponent k)
    (hzero :
      ∀ R : ℕ,
        (∫ tu :
            (SelectedCFZFormIndex e → ℝ) ×
              (SelectedCFZFormIndex e → ℝ),
          cfzCanonicalCarryTruncationDiscrepancy
            (N := N) χ (primorial w) b R
            (fun q : SelectedCFZFormIndex e => q.1)
            tu.1 tu.2
          ∂(MeasureTheory.volume.prod MeasureTheory.volume)) = 0) :
    Tendsto
      (fun R : ℕ =>
        χ.selectedCFZCanonicalCarryScaledTruncationBoxNorm
          (N := N) (primorial w) b R e
          (Real.sqrt (Real.log R)))
      atTop (𝓝 0) := by
  exact
    χ.tendsto_selectedCFZCanonicalCarryScaledTruncationBoxNorm_sqrt_log_of_integral_zero
      (N := N) (primorial w) b e
      (selectedCFZCanonicalRankinPolylogExponent e)
      (χ.selectedCFZCanonicalRankinPolylogConstant e)
      (χ.selectedCFZCanonicalRankinPolylogConstant_nonneg e)
      (χ.eventually_selectedCFZCanonicalCarryScaledTruncationRankinMass_primorial_le_polylog
        (N := N) hk hbound hwb e)
      hzero

end Wikipedia.SzemeredisTheorem
