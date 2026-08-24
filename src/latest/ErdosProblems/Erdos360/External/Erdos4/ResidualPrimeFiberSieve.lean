/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos360.External.Erdos4.Base
import ErdosProblems.Erdos851.BetaSieveFundamental
import ErdosProblems.Erdos851.ConcreteBetaCutoff

/-!
# The prime-variable sieve for the residual fibres

For a fixed cofactor `m`, primes dividing `m` never divide `m * p - 1`.
This file removes exactly those vacuous primes from the initial primorial,
builds the corresponding multiplicative density `1 / φ(d)`, and packages
the residual prime fibre as a `BoundingSieve`.  This is the exact finite
arithmetic interface needed before applying the Rosser--Iwaniec beta sieve
and Bombieri--Vinogradov to the prime variable.
-/

namespace Erdos4

noncomputable section

open scoped BigOperators

noncomputable local instance residualPrimeFiberSieveDecidable
    (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-- The small sieving primes which impose a genuine condition on
`m * p - 1`. -/
def residualSievePrimes (y m : ℕ) : Finset ℕ :=
  (Nat.primesLE y).filter fun r ↦ ¬r ∣ m

/-- Product of the genuine small-prime obstructions in the fibre at `m`. -/
def residualSieveProduct (y m : ℕ) : ℕ :=
  ∏ r ∈ residualSievePrimes y m, r

theorem residualSieveProduct_pos (y m : ℕ) :
    0 < residualSieveProduct y m := by
  unfold residualSieveProduct
  exact Finset.prod_pos fun r hr ↦
    (Nat.mem_primesLE.mp (Finset.mem_filter.mp hr).1).2.pos

theorem residualSieveProduct_squarefree (y m : ℕ) :
    Squarefree (residualSieveProduct y m) := by
  unfold residualSieveProduct
  refine Finset.squarefree_prod_of_pairwise_isCoprime ?_ ?_
  · intro p hp r hr hpr
    change IsRelPrime p r
    rw [← Nat.coprime_iff_isRelPrime]
    exact (Nat.coprime_primes
      (Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).2
      (Nat.mem_primesLE.mp (Finset.mem_filter.mp hr).1).2).mpr hpr
  · intro p hp
    exact (Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).2.squarefree

theorem residualSieveProduct_dvd_primorial (y m : ℕ) :
    residualSieveProduct y m ∣ primorial y := by
  rw [residualSieveProduct, primorial_eq_prod_primesLE]
  exact Finset.prod_dvd_prod_of_subset _ _ id (Finset.filter_subset _ _)

theorem residualSieveProduct_coprime_cofactor (y m : ℕ) :
    (residualSieveProduct y m).Coprime m := by
  unfold residualSieveProduct
  apply Nat.Coprime.prod_left
  intro r hr
  have hrData := Finset.mem_filter.mp hr
  exact (Nat.Prime.coprime_iff_not_dvd
    (Nat.mem_primesLE.mp hrData.1).2).mpr hrData.2

theorem primeFactors_residualSieveProduct (y m : ℕ) :
    (residualSieveProduct y m).primeFactors = residualSievePrimes y m := by
  unfold residualSieveProduct
  exact Nat.primeFactors_prod fun r hr ↦
    (Nat.mem_primesLE.mp (Finset.mem_filter.mp hr).1).2

theorem prime_mem_residualSievePrimes_of_dvd_product
    {y m r : ℕ} (hr : r.Prime) (hdiv : r ∣ residualSieveProduct y m) :
    r ∈ residualSievePrimes y m := by
  rw [← primeFactors_residualSieveProduct]
  exact Nat.mem_primeFactors.mpr
    ⟨hr, hdiv, (residualSieveProduct_pos y m).ne'⟩

/-- Removing primes dividing `m` does not change the coprimality condition
on the affine value `m * p - 1`. -/
theorem coprime_affine_primorial_iff_reduced
    {y m p : ℕ} (hm : 0 < m) (hp : 0 < p) :
    Nat.Coprime (m * p - 1) (primorial y) ↔
      Nat.Coprime (m * p - 1) (residualSieveProduct y m) := by
  constructor
  · intro h
    exact h.of_dvd_right (residualSieveProduct_dvd_primorial y m)
  · intro h
    apply Nat.coprime_of_dvd
    intro r hrPrime hrAffine hrPrimorial
    have hry : r ≤ y := hrPrime.dvd_primorial_iff.mp hrPrimorial
    have hrNotM : ¬r ∣ m := by
      intro hrm
      have hrmp : r ∣ m * p := dvd_mul_of_dvd_left hrm p
      have hone : r ∣ m * p - (m * p - 1) := Nat.dvd_sub hrmp hrAffine
      have hsub : m * p - (m * p - 1) = 1 := by
        have : 0 < m * p := Nat.mul_pos hm hp
        omega
      rw [hsub] at hone
      exact hrPrime.not_dvd_one hone
    have hrMem : r ∈ residualSievePrimes y m := by
      rw [residualSievePrimes, Finset.mem_filter, Nat.mem_primesLE]
      exact ⟨⟨hry, hrPrime⟩, hrNotM⟩
    have hrProd : r ∣ residualSieveProduct y m := by
      exact Finset.dvd_prod_of_mem id hrMem
    have hcop : Nat.Coprime (m * p - 1) r :=
      h.of_dvd_right hrProd
    exact (hrPrime.coprime_iff_not_dvd.mp hcop.symm) hrAffine

/-- The local density for one reduced prime progression. -/
noncomputable def residualPrimeSieveNu (_m : ℕ) : ArithmeticFunction ℝ :=
  ArithmeticFunction.prodPrimeFactors fun r ↦
    (Nat.totient r : ℝ)⁻¹

/-- The prime-local form of the residual-fibre density.  The cofactor only
removes primes from the sieve support; at every remaining prime the density
is `1 / (p - 1)`. -/
noncomputable def residualPrimeDensity (p : ℕ) : ℝ :=
  (Nat.totient p : ℝ)⁻¹

theorem residualPrimeDensity_eq_inv_pred {r : ℕ} (hr : r.Prime) :
    residualPrimeDensity r = ((r - 1 : ℕ) : ℝ)⁻¹ := by
  rw [residualPrimeDensity, Nat.totient_prime hr]

theorem residualPrimeDensity_pos {r : ℕ} (hr : r.Prime) :
    0 < residualPrimeDensity r := by
  rw [residualPrimeDensity_eq_inv_pred hr]
  apply inv_pos.mpr
  exact_mod_cast Nat.sub_pos_of_lt hr.one_lt

theorem residualPrimeDensity_lt_one {r : ℕ} (hr : r.Prime)
    (hr2 : 2 < r) : residualPrimeDensity r < 1 := by
  rw [residualPrimeDensity_eq_inv_pred hr]
  apply inv_lt_one_of_one_lt₀
  exact_mod_cast (show 1 < r - 1 by omega)

/-- The inverse `1/(p-1)` local factor is one ordinary Mertens factor
times the convergent second-order correction already used by the finite
beta-sieve library. -/
theorem residualPrimeDensity_inverse_factor_eq
    {r : ℕ} (hr : r.Prime) (hr2 : 2 < r) :
    (1 - residualPrimeDensity r)⁻¹ =
      (1 - Erdos851.oneShiftDensity r)⁻¹ *
        Erdos851.secondOrderCorrection r := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr.pos
  have hrR1 : (1 : ℝ) < r := by exact_mod_cast hr.one_lt
  have hrR2 : (2 : ℝ) < r := by exact_mod_cast hr2
  rw [residualPrimeDensity_eq_inv_pred hr,
    Erdos851.secondOrderCorrection_eq hr2]
  unfold Erdos851.oneShiftDensity
  norm_num [Nat.cast_sub hr.one_le]
  field_simp [hrR.ne', (sub_pos.mpr hrR1).ne',
    (sub_pos.mpr hrR2).ne']
  rw [show (r : ℝ) - 1 - 1 = (r : ℝ) - 2 by ring,
    div_self (sub_pos.mpr hrR2).ne']

/-- The full residual local product is a genuine dimension-one product:
the excess over the ordinary one-shift Mertens product is uniformly bounded
by the telescoping second-order product. -/
theorem residualPrimeDensity_inverseLocalEulerProduct_le
    {z y : ℕ} (hz : 2 ≤ z) :
    Erdos851.inverseLocalEulerProduct residualPrimeDensity z y ≤
      2 * Erdos851.inverseLocalEulerProduct
        Erdos851.oneShiftDensity z y := by
  rw [show (2 : ℝ) *
      Erdos851.inverseLocalEulerProduct Erdos851.oneShiftDensity z y =
      Erdos851.inverseLocalEulerProduct Erdos851.oneShiftDensity z y * 2 by
    ring]
  calc
    Erdos851.inverseLocalEulerProduct residualPrimeDensity z y =
        Erdos851.inverseLocalEulerProduct Erdos851.oneShiftDensity z y *
          ∏ r ∈ Erdos851.sievePrimes z y,
            Erdos851.secondOrderCorrection r := by
      simp only [Erdos851.inverseLocalEulerProduct]
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro r hrMem
      have hrData := Erdos851.mem_sievePrimes.mp hrMem
      exact residualPrimeDensity_inverse_factor_eq hrData.2.2 (by omega)
    _ ≤ Erdos851.inverseLocalEulerProduct Erdos851.oneShiftDensity z y *
          2 := by
      apply mul_le_mul_of_nonneg_left
        (Erdos851.secondOrderCorrection_product_le_two hz)
      unfold Erdos851.inverseLocalEulerProduct
      apply Finset.prod_nonneg
      intro r hrMem
      exact inv_nonneg.mpr
        (Erdos851.oneShift_localFactor_pos
          (Erdos851.mem_sievePrimes.mp hrMem).2.2).le

/-- A uniform dimension-one logarithmic ratio estimate for the residual
prime density. -/
theorem exists_residualPrimeDensity_dimension_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ z y : ℕ, 2 ≤ z → z ≤ y →
      Erdos851.inverseLocalEulerProduct residualPrimeDensity z y ≤
        C * (Real.log (y : ℝ) / Real.log (z : ℝ)) := by
  obtain ⟨C, hC, hdimension⟩ := Erdos851.exists_oneShift_dimension_bound
  refine ⟨2 * C, by positivity, ?_⟩
  intro z y hz hzy
  calc
    Erdos851.inverseLocalEulerProduct residualPrimeDensity z y ≤
        2 * Erdos851.inverseLocalEulerProduct
          Erdos851.oneShiftDensity z y :=
      residualPrimeDensity_inverseLocalEulerProduct_le hz
    _ ≤ 2 * (C * (Real.log (y : ℝ) / Real.log (z : ℝ))) := by
      gcongr
      exact hdimension z y hz hzy
    _ = (2 * C) * (Real.log (y : ℝ) / Real.log (z : ℝ)) := by ring

theorem residualPrimeSieveNu_mult (m : ℕ) :
    (residualPrimeSieveNu m).IsMultiplicative :=
  ArithmeticFunction.IsMultiplicative.prodPrimeFactors _

theorem residualPrimeSieveNu_eq_inv_totient
    {m d : ℕ} (hd : Squarefree d) :
    residualPrimeSieveNu m d = (Nat.totient d : ℝ)⁻¹ := by
  rw [residualPrimeSieveNu,
    ArithmeticFunction.prodPrimeFactors_apply hd.ne_zero,
    Finset.prod_inv_distrib,
    BoundedGaps.Maynard.totient_eq_prod_primeFactors_of_squarefree hd]
  norm_cast

theorem residualPrimeSieveNu_prime {m r : ℕ} (hr : r.Prime) :
    residualPrimeSieveNu m r = (Nat.totient r : ℝ)⁻¹ := by
  exact residualPrimeSieveNu_eq_inv_totient hr.squarefree

theorem residualPrimeSieveNu_prime_eq_density {m r : ℕ} (hr : r.Prime) :
    residualPrimeSieveNu m r = residualPrimeDensity r := by
  rw [residualPrimeSieveNu_prime hr]
  rfl

theorem residualPrimeSieveNu_prime_pos {m r : ℕ} (hr : r.Prime) :
    0 < residualPrimeSieveNu m r := by
  rw [residualPrimeSieveNu_prime hr]
  apply inv_pos.mpr
  exact_mod_cast Nat.totient_pos.mpr hr.pos

theorem residualPrimeSieveNu_prime_lt_one_of_even_of_dvd
    {y m r : ℕ} (hm : Even m) (hr : r.Prime)
    (hrDiv : r ∣ residualSieveProduct y m) :
    residualPrimeSieveNu m r < 1 := by
  have hrMem := prime_mem_residualSievePrimes_of_dvd_product hr hrDiv
  have hrNotM : ¬r ∣ m := (Finset.mem_filter.mp hrMem).2
  have hrNeTwo : r ≠ 2 := by
    intro hre
    subst r
    exact hrNotM hm.two_dvd
  have hrThree : 3 ≤ r := by
    have := hr.two_le
    omega
  rw [residualPrimeSieveNu_prime hr, Nat.totient_prime hr]
  apply inv_lt_one_of_one_lt₀
  exact_mod_cast (show 1 < r - 1 by omega)

/-- The unsifted prime candidates in the residual fibre at `m`. -/
def residualPrimeCandidates (U z m : ℕ) : Finset ℕ :=
  (Nat.primesLE U).filter fun p ↦ z < p ∧ m * p ≤ U

theorem mem_residualPrimeCandidates {U z m p : ℕ} :
    p ∈ residualPrimeCandidates U z m ↔
      p ≤ U ∧ p.Prime ∧ z < p ∧ m * p ≤ U := by
  rw [residualPrimeCandidates, Finset.mem_filter, Nat.mem_primesLE]
  tauto

/-- The product inequality in the definition is the interval endpoint
`p ≤ U / m` once the cofactor is positive. -/
theorem residualPrimeCandidates_eq_interval
    {U z m : ℕ} (hm : 0 < m) :
    residualPrimeCandidates U z m =
      (Finset.Ioc z (U / m)).filter Nat.Prime := by
  ext p
  rw [mem_residualPrimeCandidates, Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨_hpU, hpPrime, hzp, hmpU⟩
    refine ⟨⟨hzp, ?_⟩, hpPrime⟩
    rw [Nat.le_div_iff_mul_le hm, Nat.mul_comm]
    exact hmpU
  · rintro ⟨⟨hzp, hpDiv⟩, hpPrime⟩
    have hmpU : m * p ≤ U := by
      rw [Nat.le_div_iff_mul_le hm, Nat.mul_comm] at hpDiv
      exact hpDiv
    have hpU : p ≤ U := by
      exact (Nat.le_mul_of_pos_left p hm).trans hmpU
    exact ⟨hpU, hpPrime, hzp, hmpU⟩

/-- A divisor of the reduced sieve product is coprime to `m`. -/
theorem cofactor_coprime_of_dvd_residualSieveProduct
    {y m d : ℕ} (hd : d ∣ residualSieveProduct y m) :
    m.Coprime d := by
  exact (residualSieveProduct_coprime_cofactor y m).symm.of_dvd_right hd

/-- Canonical reduced residue solving `m * a = 1 (mod d)`. -/
noncomputable def residualAffinePrimeResidue
    (m d : ℕ) (hcop : m.Coprime d) : ℕ :=
  ((((ZMod.unitOfCoprime m hcop)⁻¹ : (ZMod d)ˣ) : ZMod d)).val

theorem residualAffinePrimeResidue_lt
    {m d : ℕ} (hd : 0 < d) (hcop : m.Coprime d) :
    residualAffinePrimeResidue m d hcop < d := by
  letI : NeZero d := ⟨hd.ne'⟩
  unfold residualAffinePrimeResidue
  exact ZMod.val_lt _

theorem residualAffinePrimeResidue_spec
    {m d : ℕ} (hd : 0 < d) (hcop : m.Coprime d) :
    (m : ZMod d) * (residualAffinePrimeResidue m d hcop : ZMod d) = 1 := by
  letI : NeZero d := ⟨hd.ne'⟩
  let u : (ZMod d)ˣ := ZMod.unitOfCoprime m hcop
  have ha : (residualAffinePrimeResidue m d hcop : ZMod d) =
      (↑(u⁻¹) : ZMod d) := by
    unfold residualAffinePrimeResidue
    exact ZMod.natCast_zmod_val _
  rw [show (m : ZMod d) = (u : ZMod d) by
    exact (ZMod.coe_unitOfCoprime m hcop).symm, ha]
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one]

theorem residualAffinePrimeResidue_coprime
    {m d : ℕ} (hcop : m.Coprime d) :
    (residualAffinePrimeResidue m d hcop).Coprime d := by
  unfold residualAffinePrimeResidue
  exact ZMod.val_coe_unit_coprime ((ZMod.unitOfCoprime m hcop)⁻¹)

theorem residualAffinePrimeResidue_mem_coprimeResidues
    {m d : ℕ} (hd : 0 < d) (hcop : m.Coprime d) :
    residualAffinePrimeResidue m d hcop ∈
      BoundedGaps.Maynard.coprimeResidues d := by
  rw [BoundedGaps.Maynard.coprimeResidues, Finset.mem_filter,
    Finset.mem_range]
  exact ⟨residualAffinePrimeResidue_lt hd hcop,
    residualAffinePrimeResidue_coprime hcop⟩

/-- Divisibility of the affine value is one reduced prime-progression
class modulo a divisor of the residual sieve product. -/
theorem dvd_affine_iff_modEq_residualAffinePrimeResidue
    {y m d p : ℕ} (hm : 0 < m) (hp : 0 < p)
    (hd : d ∣ residualSieveProduct y m) :
    d ∣ m * p - 1 ↔
      p ≡ residualAffinePrimeResidue m d
        (cofactor_coprime_of_dvd_residualSieveProduct hd) [MOD d] := by
  let hcop := cofactor_coprime_of_dvd_residualSieveProduct hd
  let u : (ZMod d)ˣ := ZMod.unitOfCoprime m hcop
  let a := residualAffinePrimeResidue m d hcop
  have hdpos : 0 < d :=
    Nat.pos_of_dvd_of_pos hd (residualSieveProduct_pos y m)
  have hspec : (m : ZMod d) * (a : ZMod d) = 1 :=
    residualAffinePrimeResidue_spec hdpos hcop
  have hmp : 1 ≤ m * p := (Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero hm.ne' hp.ne'))
  constructor
  · intro hdiv
    have hmod : 1 ≡ m * p [MOD d] :=
      (Nat.modEq_iff_dvd' hmp).mpr hdiv
    have hcast : (m : ZMod d) * (p : ZMod d) = 1 := by
      have := (ZMod.natCast_eq_natCast_iff 1 (m * p) d).mpr hmod
      simpa only [Nat.cast_one, Nat.cast_mul] using this.symm
    have hmul : (u : ZMod d) * (p : ZMod d) =
        (u : ZMod d) * (a : ZMod d) := by
      rw [show (u : ZMod d) = (m : ZMod d) by
        exact ZMod.coe_unitOfCoprime m hcop]
      rw [hcast, hspec]
    have hpa : (p : ZMod d) = (a : ZMod d) := u.mulLeft.injective hmul
    exact (ZMod.natCast_eq_natCast_iff p a d).mp hpa
  · intro hmod
    have hpa : (p : ZMod d) = (a : ZMod d) :=
      (ZMod.natCast_eq_natCast_iff p a d).mpr hmod
    have hcast : ((m * p : ℕ) : ZMod d) = 1 := by
      push_cast
      rw [hpa, hspec]
    have hmodOne : 1 ≡ m * p [MOD d] :=
      (ZMod.natCast_eq_natCast_iff 1 (m * p) d).mp (by
        simpa only [Nat.cast_one] using hcast.symm)
    exact (Nat.modEq_iff_dvd' hmp).mp hmodOne

/-- Candidates for which the squarefree sieve divisor divides `m*p-1`. -/
def residualPrimeDivisibleCandidates
    (U z m d : ℕ) : Finset ℕ :=
  (residualPrimeCandidates U z m).filter fun p ↦ d ∣ m * p - 1

/-- The affine divisibility count is an ordinary reduced prime progression
count on `(z, U / m]`. -/
theorem card_residualPrimeDivisibleCandidates_eq_progression
    {U y z m d : ℕ} (hm : 0 < m)
    (hd : d ∣ residualSieveProduct y m) :
    (residualPrimeDivisibleCandidates U z m d).card =
      BoundedGaps.Maynard.primeVariableProgressionCount
        (z + 1) (U / m + 1) d
        (residualAffinePrimeResidue m d
          (cofactor_coprime_of_dvd_residualSieveProduct hd)) := by
  classical
  apply congrArg Finset.card
  rw [residualPrimeDivisibleCandidates,
    residualPrimeCandidates_eq_interval hm]
  ext p
  simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Ico]
  constructor
  · rintro ⟨⟨⟨hzp, hpU⟩, hpPrime⟩, hdiv⟩
    refine ⟨⟨by omega, by omega⟩, hpPrime, ?_⟩
    exact (dvd_affine_iff_modEq_residualAffinePrimeResidue
      hm hpPrime.pos hd).mp hdiv
  · rintro ⟨⟨hpz, hpU⟩, hpPrime, hmod⟩
    refine ⟨⟨⟨by omega, by omega⟩, hpPrime⟩, ?_⟩
    exact (dvd_affine_iff_modEq_residualAffinePrimeResidue
      hm hpPrime.pos hd).mpr hmod

/-- The unsifted mass is the total prime count on the same interval. -/
theorem card_residualPrimeCandidates_eq_totalProgression
    {U z m : ℕ} (hm : 0 < m) :
    (residualPrimeCandidates U z m).card =
      BoundedGaps.Maynard.primeVariableProgressionCount
        (z + 1) (U / m + 1) 1 0 := by
  classical
  apply congrArg Finset.card
  rw [residualPrimeCandidates_eq_interval hm]
  ext p
  simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Ico]
  constructor
  · rintro ⟨⟨hzp, hpU⟩, hpPrime⟩
    exact ⟨⟨by omega, by omega⟩, hpPrime, Nat.modEq_one⟩
  · rintro ⟨⟨hpz, hpU⟩, hpPrime, _hmod⟩
    exact ⟨⟨by omega, by omega⟩, hpPrime⟩

theorem primeCountUpTo_one_zero (x : ℕ) :
    BoundedGaps.Maynard.primeCountUpTo x 1 0 =
      BoundedGaps.Maynard.primeCountTotal x := by
  unfold BoundedGaps.Maynard.primeCountUpTo
    BoundedGaps.Maynard.primeCountTotal Nat.primeCounting
    Nat.primeCounting'
  rw [Nat.count_eq_card_filter_range]
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_range, Nat.mod_one,
    Nat.zero_mod, and_true]

theorem cast_card_residualPrimeCandidates
    {U z m : ℕ} (hm : 0 < m) (hzU : z ≤ U / m) :
    ((residualPrimeCandidates U z m).card : ℝ) =
      (BoundedGaps.Maynard.primeCountTotal (U / m) : ℝ) -
        BoundedGaps.Maynard.primeCountTotal z := by
  rw [card_residualPrimeCandidates_eq_totalProgression hm,
    BoundedGaps.Maynard.cast_primeVariableProgressionCount]
  · rw [primeCountUpTo_one_zero, primeCountUpTo_one_zero]
    simp only [Nat.add_sub_cancel]
  · omega
  · omega

/-- A fibre-cardinality weight on the image of `p ↦ m*p-1`; this avoids
having to assume injectivity when defining the abstract sieve. -/
noncomputable def residualPrimeBoundingSieve
    (U y z m : ℕ) (hm : 0 < m) (hmEven : Even m) : BoundingSieve := by
  classical
  let P := residualPrimeCandidates U z m
  let f := fun p : ℕ ↦ m * p - 1
  exact
    { support := P.image f
      prodPrimes := residualSieveProduct y m
      prodPrimes_squarefree := residualSieveProduct_squarefree y m
      weights := fun a ↦ ((P.filter fun p ↦ f p = a).card : ℝ)
      weights_nonneg := fun _ ↦ by positivity
      totalMass := P.card
      nu := residualPrimeSieveNu m
      nu_mult := residualPrimeSieveNu_mult m
      nu_pos_of_prime := by
        intro r hr _hrDiv
        exact residualPrimeSieveNu_prime_pos hr
      nu_lt_one_of_prime := by
        intro r hr hrDiv
        exact residualPrimeSieveNu_prime_lt_one_of_even_of_dvd
          hmEven hr hrDiv }

@[simp] theorem residualPrimeBoundingSieve_totalMass
    {U y z m : ℕ} {hm : 0 < m} {hmEven : Even m} :
    (residualPrimeBoundingSieve U y z m hm hmEven).totalMass =
      (residualPrimeCandidates U z m).card := rfl

@[simp] theorem residualPrimeBoundingSieve_nu_apply
    {U y z m d : ℕ} {hm : 0 < m} {hmEven : Even m} :
    (residualPrimeBoundingSieve U y z m hm hmEven).nu d =
      residualPrimeSieveNu m d := rfl

/-- The abstract multiple sum is the literal affine divisibility count. -/
theorem residualPrimeBoundingSieve_multSum
    {U y z m d : ℕ} {hm : 0 < m} {hmEven : Even m} :
    (residualPrimeBoundingSieve U y z m hm hmEven).multSum d =
      ((residualPrimeDivisibleCandidates U z m d).card : ℝ) := by
  classical
  let P := residualPrimeCandidates U z m
  let f := fun p : ℕ ↦ m * p - 1
  rw [BoundingSieve.multSum]
  change (∑ a ∈ P.image f,
      if d ∣ a then ((P.filter fun p ↦ f p = a).card : ℝ) else 0) = _
  simp_rw [← Finset.sum_filter]
  have hcount :
      (∑ a ∈ (P.image f).filter fun a ↦ d ∣ a,
          (P.filter fun p ↦ f p = a).card) =
        (P.filter fun p ↦ d ∣ f p).card := by
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    congr 1
    ext p
    simp only [Finset.mem_filter, Finset.mem_image]
    aesop
  rw [← Nat.cast_sum, hcount]
  rfl

/-- The abstract sieve remainder is bounded by the two endpoint prime
progression discrepancies.  This is the exact Bombieri--Vinogradov-facing
interface for the residual fibre. -/
theorem residualPrimeBoundingSieve_rem_abs_le
    {U y z m d : ℕ} {hm : 0 < m} {hmEven : Even m}
    (hzU : z ≤ U / m) (hd : d ∣ residualSieveProduct y m) :
    |(residualPrimeBoundingSieve U y z m hm hmEven).rem d| ≤
      BoundedGaps.Maynard.progressionDiscrepancy (U / m) d
          (residualAffinePrimeResidue m d
            (cofactor_coprime_of_dvd_residualSieveProduct hd)) +
        BoundedGaps.Maynard.progressionDiscrepancy z d
          (residualAffinePrimeResidue m d
            (cofactor_coprime_of_dvd_residualSieveProduct hd)) := by
  have hdSq : Squarefree d :=
    Squarefree.squarefree_of_dvd hd
      (residualSieveProduct_squarefree y m)
  have hcount :=
    BoundedGaps.Maynard.primeVariableProgressionCount_intervalDiscrepancy_le_global_sum
      (A := z + 1) (B := U / m + 1) (q := d)
      (r := residualAffinePrimeResidue m d
        (cofactor_coprime_of_dvd_residualSieveProduct hd))
      (by omega) (by omega)
  rw [BoundingSieve.rem, residualPrimeBoundingSieve_multSum,
    card_residualPrimeDivisibleCandidates_eq_progression hm hd,
    residualPrimeBoundingSieve_nu_apply,
    residualPrimeSieveNu_eq_inv_totient hdSq,
    residualPrimeBoundingSieve_totalMass,
    cast_card_residualPrimeCandidates hm hzU]
  simpa [div_eq_mul_inv, mul_comm] using hcount

/-- A pointwise form of the remainder estimate using the maximum over
reduced residues, ready for summation over the sieve divisors. -/
theorem residualPrimeBoundingSieve_rem_abs_le_max
    {U y z m d : ℕ} {hm : 0 < m} {hmEven : Even m}
    (hzU : z ≤ U / m) (hd : d ∣ residualSieveProduct y m) :
    |(residualPrimeBoundingSieve U y z m hm hmEven).rem d| ≤
      BoundedGaps.Maynard.maxProgressionDiscrepancy (U / m) d +
        BoundedGaps.Maynard.maxProgressionDiscrepancy z d := by
  have hdpos : 0 < d :=
    Nat.pos_of_dvd_of_pos hd (residualSieveProduct_pos y m)
  let hcop := cofactor_coprime_of_dvd_residualSieveProduct hd
  have hres : residualAffinePrimeResidue m d hcop ∈
      BoundedGaps.Maynard.coprimeResidues d :=
    residualAffinePrimeResidue_mem_coprimeResidues hdpos hcop
  exact (residualPrimeBoundingSieve_rem_abs_le hzU hd).trans
    (add_le_add
      (BoundedGaps.Maynard.progressionDiscrepancy_le_max hdpos hres)
      (BoundedGaps.Maynard.progressionDiscrepancy_le_max hdpos hres))

/-- Bombieri--Vinogradov, at two endpoints, bounds the complete beta-sieve
level remainder for one residual fibre. -/
theorem residualPrimeBoundingSieve_levelRemainder_le_primeLevelWitness
    {theta A C : ℝ} {X₀ U y z m D : ℕ}
    {hm : 0 < m} {hmEven : Even m}
    (hw : BoundedGaps.Maynard.PrimeLevelWitness theta A C X₀)
    (hzU : z ≤ U / m) (hupper : X₀ ≤ U / m) (hlower : X₀ ≤ z)
    (hDupper : D ≤ BoundedGaps.Maynard.modulusCutoff theta (U / m))
    (hDlower : D ≤ BoundedGaps.Maynard.modulusCutoff theta z) :
    Erdos851.BetaSieveFundamental.levelRemainder
        (residualPrimeBoundingSieve U y z m hm hmEven) D ≤
      C * ((U / m : ℕ) : ℝ) /
          Real.rpow (Real.log ((U / m : ℕ) : ℝ)) A +
        C * (z : ℝ) / Real.rpow (Real.log (z : ℝ)) A := by
  let S :=
    (Nat.divisors (residualSieveProduct y m)).filter fun d ↦ d ≤ D
  have hSupper : S ⊆ Finset.Icc 1
      (BoundedGaps.Maynard.modulusCutoff theta (U / m)) := by
    intro d hd
    have hdData := Finset.mem_filter.mp hd
    exact Finset.mem_Icc.mpr
      ⟨Nat.pos_of_mem_divisors hdData.1,
        hdData.2.trans hDupper⟩
  have hSlower : S ⊆ Finset.Icc 1
      (BoundedGaps.Maynard.modulusCutoff theta z) := by
    intro d hd
    have hdData := Finset.mem_filter.mp hd
    exact Finset.mem_Icc.mpr
      ⟨Nat.pos_of_mem_divisors hdData.1,
        hdData.2.trans hDlower⟩
  have hsumUpper :=
    hw.sum_maxProgressionDiscrepancy_subset hupper S hSupper
  have hsumLower :=
    hw.sum_maxProgressionDiscrepancy_subset hlower S hSlower
  unfold Erdos851.BetaSieveFundamental.levelRemainder
  change (∑ d ∈ S,
      |(residualPrimeBoundingSieve U y z m hm hmEven).rem d|) ≤ _
  calc
    (∑ d ∈ S,
        |(residualPrimeBoundingSieve U y z m hm hmEven).rem d|) ≤
        ∑ d ∈ S,
          (BoundedGaps.Maynard.maxProgressionDiscrepancy (U / m) d +
            BoundedGaps.Maynard.maxProgressionDiscrepancy z d) := by
      apply Finset.sum_le_sum
      intro d hd
      exact residualPrimeBoundingSieve_rem_abs_le_max hzU
        (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1)
    _ = (∑ d ∈ S,
          BoundedGaps.Maynard.maxProgressionDiscrepancy (U / m) d) +
        ∑ d ∈ S,
          BoundedGaps.Maynard.maxProgressionDiscrepancy z d := by
      rw [Finset.sum_add_distrib]
    _ ≤ C * ((U / m : ℕ) : ℝ) /
          Real.rpow (Real.log ((U / m : ℕ) : ℝ)) A +
        C * (z : ℝ) / Real.rpow (Real.log (z : ℝ)) A :=
      add_le_add hsumUpper hsumLower

/-- The abstract sifted sum is exactly the residual prime fibre. -/
theorem residualPrimeBoundingSieve_siftedSum
    {U y z m : ℕ} {hm : 0 < m} {hmEven : Even m} :
    (residualPrimeBoundingSieve U y z m hm hmEven).siftedSum =
      ((residualPrimeFiber U y z m).card : ℝ) := by
  classical
  let P := residualPrimeCandidates U z m
  let f := fun p : ℕ ↦ m * p - 1
  rw [BoundingSieve.siftedSum]
  change (∑ a ∈ P.image f,
      if Nat.Coprime (residualSieveProduct y m) a then
        ((P.filter fun p ↦ f p = a).card : ℝ) else 0) = _
  simp_rw [← Finset.sum_filter]
  have hcount :
      (∑ a ∈ (P.image f).filter fun a ↦
          Nat.Coprime (residualSieveProduct y m) a,
          (P.filter fun p ↦ f p = a).card) =
        (P.filter fun p ↦
          Nat.Coprime (residualSieveProduct y m) (f p)).card := by
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    congr 1
    ext p
    simp only [Finset.mem_filter, Finset.mem_image]
    aesop
  rw [← Nat.cast_sum, hcount]
  congr 1
  apply congrArg Finset.card
  ext p
  rw [Finset.mem_filter, mem_residualPrimeCandidates,
    mem_residualPrimeFiber]
  constructor
  · rintro ⟨hpData, hcop⟩
    refine ⟨hpData.1, hpData.2.1, hpData.2.2.1, hpData.2.2.2, ?_⟩
    exact (coprime_affine_primorial_iff_reduced hm
      hpData.2.1.pos).mpr hcop.symm
  · rintro ⟨hpU, hpPrime, hzp, hmpU, hcop⟩
    refine ⟨⟨hpU, hpPrime, hzp, hmpU⟩, ?_⟩
    exact ((coprime_affine_primorial_iff_reduced hm hpPrime.pos).mp hcop).symm

end

end Erdos4
