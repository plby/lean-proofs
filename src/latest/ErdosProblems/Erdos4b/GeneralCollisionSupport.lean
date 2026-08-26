/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.PinnedGeneralCollision

/-!
# Rough support of the cross-family auxiliary variables

The exact collision expansions in `GeneralCollision` and
`PinnedGeneralCollision` introduce one divisor for every ordered
companion/first coordinate pair.  This file records the first analytic
property of those variables: unless the entire matrix is trivial, one of
its entries has a prime divisor beyond the pre-sieve cutoff, and affine
compatibility forces that prime to divide the corresponding exceptional
integer.

This is the finite support statement behind the exceptional-prime products
in Maynard's Lemmas 6 and 7.  It is independent of all asymptotic estimates.
-/

namespace Erdos4b

open scoped BigOperators

noncomputable section

noncomputable local instance erdos4GeneralCollisionSupportPropDecidable
    (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- The signed affine difference attached to the ordered pair
`(companion coordinate, first coordinate)`. -/
def crossAffineDifference {H : Finset ℕ} (m q : ℕ) (ba : H × H) : ℤ :=
  (m * (ba.1.1 * q) : ℕ) - (m * (ba.2.1 * q) + 1 : ℕ)

/-- For a positive multiplier and a prime auxiliary variable, none of the
affine exceptional integers vanishes.  The point is simply that a multiple
of `m*q`, whose absolute value is at least two, cannot equal one. -/
theorem crossAffineDifference_ne_zero
    {H : Finset ℕ} {m q : ℕ} (hm : 0 < m) (hq : q.Prime)
    (ba : H × H) : crossAffineDifference m q ba ≠ 0 := by
  intro hzero
  have hmqTwo : 2 ≤ m * q := by
    have hqTwo : 2 ≤ q := hq.two_le
    nlinarith
  have hdiv : (m * q : ℤ) ∣ (1 : ℤ) := by
    refine ⟨(ba.1.1 : ℤ) - ba.2.1, ?_⟩
    have hzero' :
        (m : ℤ) * ((ba.1.1 : ℤ) * q) -
            ((m : ℤ) * ((ba.2.1 : ℤ) * q) + 1) = 0 := by
      exact hzero
    nlinarith
  have hdivNat : m * q ∣ 1 := Int.natCast_dvd_natCast.mp hdiv
  have hmqOne : m * q = 1 := Nat.dvd_one.mp hdivNat
  omega

/-- Product of all affine exceptional integers, with signs discarded. -/
noncomputable def crossExceptionalModulus
    (H : Finset ℕ) (m q : ℕ) : ℕ :=
  ∏ ba : H × H, (crossAffineDifference m q ba).natAbs

/-- A uniform elementary envelope for each affine difference.  The sum of
the shifts avoids a nonempty hypothesis on `H`. -/
def crossAffineEnvelope (H : Finset ℕ) (m q : ℕ) : ℕ :=
  m * q * (∑ h ∈ H, h) + 1

theorem crossAffineDifference_natAbs_le_envelope
    {H : Finset ℕ} (m q : ℕ) (ba : H × H) :
    (crossAffineDifference m q ba).natAbs ≤
      crossAffineEnvelope H m q := by
  have hfirst : ba.2.1 ≤ ∑ h ∈ H, h :=
    Finset.single_le_sum (fun h _ ↦ Nat.zero_le h) ba.2.2
  have hcompanion : ba.1.1 ≤ ∑ h ∈ H, h :=
    Finset.single_le_sum (fun h _ ↦ Nat.zero_le h) ba.1.2
  have hleft : m * (ba.1.1 * q) ≤ crossAffineEnvelope H m q := by
    unfold crossAffineEnvelope
    calc
      m * (ba.1.1 * q) = (m * q) * ba.1.1 := by ring
      _ ≤ (m * q) * (∑ h ∈ H, h) :=
        Nat.mul_le_mul_left _ hcompanion
      _ ≤ (m * q) * (∑ h ∈ H, h) + 1 := Nat.le_add_right _ _
  have hright :
      m * (ba.2.1 * q) + 1 ≤ crossAffineEnvelope H m q := by
    unfold crossAffineEnvelope
    calc
      m * (ba.2.1 * q) + 1 = (m * q) * ba.2.1 + 1 := by ring
      _ ≤ (m * q) * (∑ h ∈ H, h) + 1 :=
        Nat.add_le_add_right (Nat.mul_le_mul_left _ hfirst) 1
  exact Int.natAbs_coe_sub_coe_le_of_le hleft hright

/-- Polynomial-size envelope for the product of all exceptional affine
integers.  The exponent is exactly the number of ordered coordinate pairs. -/
theorem crossExceptionalModulus_le_envelope_pow
    (H : Finset ℕ) (m q : ℕ) :
    crossExceptionalModulus H m q ≤
      crossAffineEnvelope H m q ^ Fintype.card (H × H) := by
  unfold crossExceptionalModulus
  calc
    (∏ ba : H × H, (crossAffineDifference m q ba).natAbs) ≤
        ∏ _ba : H × H, crossAffineEnvelope H m q := by
      apply Finset.prod_le_prod
      · intro ba hba
        exact Nat.zero_le _
      · intro ba hba
        exact crossAffineDifference_natAbs_le_envelope m q ba
    _ = crossAffineEnvelope H m q ^ Fintype.card (H × H) := by simp

/-- The exceptional modulus is positive in the range used by the large-gap
weight. -/
theorem crossExceptionalModulus_pos
    {H : Finset ℕ} {m q : ℕ} (hm : 0 < m) (hq : q.Prime) :
    0 < crossExceptionalModulus H m q := by
  unfold crossExceptionalModulus
  apply Finset.prod_pos
  intro ba hba
  exact Int.natAbs_pos.mpr (crossAffineDifference_ne_zero hm hq ba)

/-- Reciprocal-log mass of the prime factors of `P` lying strictly beyond
`w`.  This is the form in which exceptional affine primes enter Maynard's
Euler-product comparison. -/
noncomputable def roughPrimeLogDivisorMass (P w : ℕ) : ℝ :=
  ∑ p ∈ P.primeFactors.filter (fun p ↦ w < p),
    Real.log p / (p : ℝ)

/-- Elementary large-prime divisor bound.  No squarefreeness hypothesis is
needed: the radical of `P` divides `P`, so the sum of the logarithms of its
distinct prime divisors is at most `log P`. -/
theorem roughPrimeLogDivisorMass_le_log_div
    {P w : ℕ} (hP : 0 < P) (hw : 0 < w) :
    roughPrimeLogDivisorMass P w ≤ Real.log P / w := by
  classical
  let high := P.primeFactors.filter (fun p ↦ w < p)
  have hpoint : ∀ p ∈ high,
      Real.log p / (p : ℝ) ≤ Real.log p / w := by
    intro p hp
    have hpData := Finset.mem_filter.mp hp
    exact div_le_div_of_nonneg_left (Real.log_natCast_nonneg p)
      (by exact_mod_cast hw) (by exact_mod_cast hpData.2.le)
  have hsubset : high ⊆ P.primeFactors := Finset.filter_subset _ _
  have hprodPos : 0 < ∏ p ∈ P.primeFactors, p := by
    exact Finset.prod_pos fun p hp ↦ (Nat.prime_of_mem_primeFactors hp).pos
  have hprodLe : (∏ p ∈ P.primeFactors, p) ≤ P :=
    Nat.le_of_dvd hP (Nat.prod_primeFactors_dvd P)
  have hcastProd :
      (∏ p ∈ P.primeFactors, (p : ℝ)) =
        ((∏ p ∈ P.primeFactors, p : ℕ) : ℝ) := by
    simp
  have hlogsumLe :
      (∑ p ∈ P.primeFactors, Real.log p) ≤ Real.log P := by
    calc
      (∑ p ∈ P.primeFactors, Real.log p) =
          Real.log (∏ p ∈ P.primeFactors, (p : ℝ)) := by
        exact (Real.log_prod (fun p hp ↦ by
          exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero)).symm
      _ = Real.log ((∏ p ∈ P.primeFactors, p : ℕ) : ℝ) := by
        rw [hcastProd]
      _ ≤ Real.log P := Real.log_le_log
        (by exact_mod_cast hprodPos) (by exact_mod_cast hprodLe)
  unfold roughPrimeLogDivisorMass
  change (∑ p ∈ high, Real.log p / (p : ℝ)) ≤ _
  calc
    (∑ p ∈ high, Real.log p / (p : ℝ)) ≤
        ∑ p ∈ high, Real.log p / w := Finset.sum_le_sum hpoint
    _ ≤ ∑ p ∈ P.primeFactors, Real.log p / w := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro p hpP hpNot
      positivity
    _ = (∑ p ∈ P.primeFactors, Real.log p) / w := by
      rw [Finset.sum_div]
    _ ≤ Real.log P / w := by
      exact div_le_div_of_nonneg_right hlogsumLe (by exact_mod_cast hw.le)

theorem roughPrimeLogDivisorMass_mono_of_dvd
    {A B w : ℕ} (hAB : A ∣ B) (hB : B ≠ 0) :
    roughPrimeLogDivisorMass A w ≤ roughPrimeLogDivisorMass B w := by
  classical
  unfold roughPrimeLogDivisorMass
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    have hpData := Finset.mem_filter.mp hp
    apply Finset.mem_filter.mpr
    exact ⟨Nat.primeFactors_mono hAB hB hpData.1, hpData.2⟩
  · intro p hpB hpNot
    positivity

/-- The auxiliary matrix all of whose entries are one. -/
noncomputable def oneCrossAuxiliaryDivisors
    {H : Finset ℕ} {d e d' e' : H → ℕ}
    (hDpos : ∀ h : H, 0 < Nat.lcm (d h) (d' h))
    (hEpos : ∀ h : H, 0 < Nat.lcm (e h) (e' h)) :
    CrossAuxiliaryDivisors H d e d' e' := fun ba ↦
  ⟨1, Nat.mem_divisors.mpr ⟨one_dvd _,
    (Nat.gcd_pos_of_pos_left _ (hDpos ba.2)).ne'⟩⟩

@[simp] theorem oneCrossAuxiliaryDivisors_apply
    {H : Finset ℕ} {d e d' e' : H → ℕ}
    (hDpos : ∀ h : H, 0 < Nat.lcm (d h) (d' h))
    (hEpos : ∀ h : H, 0 < Nat.lcm (e h) (e' h))
    (ba : H × H) :
    (oneCrossAuxiliaryDivisors hDpos hEpos ba).1 = 1 := by
  rfl

/-- Extensional characterization of the trivial auxiliary matrix. -/
theorem crossAuxiliaryDivisors_eq_one_iff
    {H : Finset ℕ} {d e d' e' : H → ℕ}
    (hDpos : ∀ h : H, 0 < Nat.lcm (d h) (d' h))
    (hEpos : ∀ h : H, 0 < Nat.lcm (e h) (e' h))
    (a : CrossAuxiliaryDivisors H d e d' e') :
    a = oneCrossAuxiliaryDivisors hDpos hEpos ↔
      ∀ ba : H × H, (a ba).1 = 1 := by
  constructor
  · rintro rfl ba
    rfl
  · intro ha
    funext ba
    exact Subtype.ext (ha ba)

/-- The trivial matrix has unit totient weight. -/
@[simp] theorem crossAuxiliaryTotientWeight_one
    {H : Finset ℕ} {d e d' e' : H → ℕ}
    (hDpos : ∀ h : H, 0 < Nat.lcm (d h) (d' h))
    (hEpos : ∀ h : H, 0 < Nat.lcm (e h) (e' h)) :
    crossAuxiliaryTotientWeight
      (oneCrossAuxiliaryDivisors hDpos hEpos) = 1 := by
  simp [crossAuxiliaryTotientWeight]

/-- The trivial matrix also has unit pinned `g(p)=p-2` weight. -/
@[simp] theorem crossAuxiliaryS2GWeight_one
    {H : Finset ℕ} {d e d' e' : H → ℕ}
    (hDpos : ∀ h : H, 0 < Nat.lcm (d h) (d' h))
    (hEpos : ∀ h : H, 0 < Nat.lcm (e h) (e' h)) :
    crossAuxiliaryS2GWeight
      (oneCrossAuxiliaryDivisors hDpos hEpos) = 1 := by
  simp [crossAuxiliaryS2GWeight, BoundedGaps.Maynard.maynardS2G]

/-- A prime dividing one auxiliary entry divides the corresponding signed
affine difference whenever the auxiliary matrix is compatible. -/
theorem prime_dvd_crossAffineDifference_of_auxiliaryCompatible
    {H : Finset ℕ} {d e d' e' : H → ℕ} {m q p : ℕ}
    {a : CrossAuxiliaryDivisors H d e d' e'}
    (hcompat : CrossAuxiliaryAffineCompatible m q a)
    (ba : H × H) (hp : p ∣ (a ba).1) :
    (p : ℤ) ∣ crossAffineDifference m q ba := by
  exact Nat.modEq_iff_dvd.mp ((hcompat ba).of_dvd hp)

/-- A prime dividing one compatible auxiliary entry belongs to the single
finite exceptional modulus. -/
theorem prime_dvd_crossExceptionalModulus_of_auxiliaryCompatible
    {H : Finset ℕ} {d e d' e' : H → ℕ} {m q p : ℕ}
    {a : CrossAuxiliaryDivisors H d e d' e'}
    (hcompat : CrossAuxiliaryAffineCompatible m q a)
    (ba : H × H) (hp : p ∣ (a ba).1) :
    p ∣ crossExceptionalModulus H m q := by
  have hpdiff : p ∣ (crossAffineDifference m q ba).natAbs :=
    Int.natCast_dvd.mp
      (prime_dvd_crossAffineDifference_of_auxiliaryCompatible
        hcompat ba hp)
  exact hpdiff.trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ ba))

/-- The full cross-gcd product is squarefree once the first within-family
lcm product is squarefree. -/
theorem squarefree_crossCoordinateGcdProduct
    {H : Finset ℕ} {d e d' e' : H → ℕ}
    (hDsq : ∀ a : H, Squarefree (Nat.lcm (d a) (d' a)))
    (hDD : ∀ {a b : H}, a ≠ b →
      (Nat.lcm (d a) (d' a)).Coprime (Nat.lcm (d b) (d' b)))
    (hEE : ∀ {a b : H}, a ≠ b →
      (Nat.lcm (e a) (e' a)).Coprime (Nat.lcm (e b) (e' b))) :
    Squarefree (crossCoordinateGcdProduct H d e d' e') := by
  have hFirstSq : Squarefree (firstLcmProduct H d d') :=
    squarefree_firstLcmProduct_of_pairwise hDsq hDD
  rw [← gcd_firstLcmProduct_companionLcmProduct_eq_cross hDD hEE]
  exact hFirstSq.squarefree_of_dvd (Nat.gcd_dvd_left _ _)

theorem firstLcmProduct_dvd_divisorTupleProducts
    {H : Finset ℕ} (d d' : H → ℕ) :
    firstLcmProduct H d d' ∣
      BoundedGaps.Maynard.divisorTupleProduct H d *
        BoundedGaps.Maynard.divisorTupleProduct H d' := by
  unfold firstLcmProduct BoundedGaps.Maynard.divisorTupleProduct
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_dvd_prod_of_dvd _ _ fun h _ ↦
    Nat.lcm_dvd_mul (d h) (d' h)

/-- The cross factor is smaller than the square of the first-family
divisor radius. -/
theorem crossCoordinateGcdProduct_lt_radius_sq
    {H : Finset ℕ} {RD W : ℕ} {d e d' e' : H → ℕ}
    (hd : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD W d)
    (hd' : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD W d')
    (hDD : ∀ {a b : H}, a ≠ b →
      (Nat.lcm (d a) (d' a)).Coprime (Nat.lcm (d b) (d' b)))
    (hEE : ∀ {a b : H}, a ≠ b →
      (Nat.lcm (e a) (e' a)).Coprime (Nat.lcm (e b) (e' b))) :
    crossCoordinateGcdProduct H d e d' e' < RD ^ 2 := by
  have hcrossDvdFirst : crossCoordinateGcdProduct H d e d' e' ∣
      firstLcmProduct H d d' := by
    rw [← gcd_firstLcmProduct_companionLcmProduct_eq_cross hDD hEE]
    exact Nat.gcd_dvd_left _ _
  have hprodPos : 0 <
      BoundedGaps.Maynard.divisorTupleProduct H d *
        BoundedGaps.Maynard.divisorTupleProduct H d' := by
    exact mul_pos
      (Nat.pos_of_ne_zero hd.2.2.ne_zero)
      (Nat.pos_of_ne_zero hd'.2.2.ne_zero)
  have hcrossLe : crossCoordinateGcdProduct H d e d' e' ≤
      BoundedGaps.Maynard.divisorTupleProduct H d *
        BoundedGaps.Maynard.divisorTupleProduct H d' :=
    Nat.le_of_dvd hprodPos
      (hcrossDvdFirst.trans (firstLcmProduct_dvd_divisorTupleProducts d d'))
  have hprodLt :
      BoundedGaps.Maynard.divisorTupleProduct H d *
          BoundedGaps.Maynard.divisorTupleProduct H d' < RD * RD := by
    nlinarith [hd.1, hd'.1]
  rw [pow_two]
  exact hcrossLe.trans_lt hprodLt

theorem crossCoordinateGcdProduct_pos
    {H : Finset ℕ} {d e d' e' : H → ℕ}
    (hDpos : ∀ a : H, 0 < Nat.lcm (d a) (d' a)) :
    0 < crossCoordinateGcdProduct H d e d' e' := by
  unfold crossCoordinateGcdProduct
  apply Finset.prod_pos
  intro b hb
  apply Finset.prod_pos
  intro a ha
  exact Nat.gcd_pos_of_pos_left _ (hDpos a)

/-- The three elementary hypotheses required by the existing rough-modulus
Euler estimates: positivity, squarefreeness, and a radius-square bound. -/
theorem crossCoordinateGcdProduct_roughModulusData
    {H : Finset ℕ} {RD W : ℕ} {d e d' e' : H → ℕ}
    (hd : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD W d)
    (hd' : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD W d')
    (hDD : ∀ {a b : H}, a ≠ b →
      (Nat.lcm (d a) (d' a)).Coprime (Nat.lcm (d b) (d' b)))
    (hEE : ∀ {a b : H}, a ≠ b →
      (Nat.lcm (e a) (e' a)).Coprime (Nat.lcm (e b) (e' b))) :
    0 < crossCoordinateGcdProduct H d e d' e' ∧
      Squarefree (crossCoordinateGcdProduct H d e d' e') ∧
      crossCoordinateGcdProduct H d e d' e' < RD ^ 2 := by
  have hDpos : ∀ a : H, 0 < Nat.lcm (d a) (d' a) := fun a ↦
    Nat.lcm_pos (Nat.pos_of_ne_zero (hd.coordinate_squarefree a).ne_zero)
      (Nat.pos_of_ne_zero (hd'.coordinate_squarefree a).ne_zero)
  have hDsq : ∀ a : H, Squarefree (Nat.lcm (d a) (d' a)) := fun a ↦
    BoundedGaps.Maynard.squarefree_lcm
      (hd.coordinate_squarefree a) (hd'.coordinate_squarefree a)
  exact ⟨crossCoordinateGcdProduct_pos hDpos,
    squarefree_crossCoordinateGcdProduct hDsq hDD hEE,
    crossCoordinateGcdProduct_lt_radius_sq hd hd' hDD hEE⟩

/-- Direct insertion of the cross-gcd data into the existing uniform
rough-modulus prime-log estimate. -/
theorem exists_uniform_crossCoordinateGcdProduct_primeLogDivisorMass_le :
    ∃ C : ℝ, ∀ {H : Finset ℕ} {RD W : ℕ} {d e d' e' : H → ℕ},
      BoundedGaps.Maynard.IsMaynardDivisorTuple H RD W d →
      BoundedGaps.Maynard.IsMaynardDivisorTuple H RD W d' →
      (∀ {a b : H}, a ≠ b →
        (Nat.lcm (d a) (d' a)).Coprime (Nat.lcm (d b) (d' b))) →
      (∀ {a b : H}, a ≠ b →
        (Nat.lcm (e a) (e' a)).Coprime (Nat.lcm (e b) (e' b))) →
      2 ≤ Real.log ((RD ^ 2 : ℕ) : ℝ) →
      BoundedGaps.Maynard.primeLogDivisorMass
          (crossCoordinateGcdProduct H d e d' e') ≤
        Real.log (Real.log ((RD ^ 2 : ℕ) : ℝ)) + C + 2 := by
  obtain ⟨C, hC⟩ :=
    BoundedGaps.Maynard.exists_uniform_primeLogDivisorMass_le_log_log_add
  refine ⟨C, ?_⟩
  intro H RD W d e d' e' hd hd' hDD hEE hlog
  obtain ⟨hP, hPsq, hPR⟩ :=
    crossCoordinateGcdProduct_roughModulusData hd hd' hDD hEE
  exact hC hP hPsq hPR hlog

/-- If the entire coordinate system is compatible, its squarefree
cross-collision factor divides the exceptional affine modulus. -/
theorem crossCoordinateGcdProduct_dvd_crossExceptionalModulus
    {H : Finset ℕ} {d e d' e' : H → ℕ} {m q : ℕ}
    (hm : 0 < m) (hq : q.Prime)
    (hDpos : ∀ h : H, 0 < Nat.lcm (d h) (d' h))
    (hEpos : ∀ h : H, 0 < Nat.lcm (e h) (e' h))
    (hmE : ∀ h : H, m.Coprime (Nat.lcm (e h) (e' h)))
    (hDsq : ∀ a : H, Squarefree (Nat.lcm (d a) (d' a)))
    (hDD : ∀ {a b : H}, a ≠ b →
      (Nat.lcm (d a) (d' a)).Coprime (Nat.lcm (d b) (d' b)))
    (hEE : ∀ {a b : H}, a ≠ b →
      (Nat.lcm (e a) (e' a)).Coprime (Nat.lcm (e b) (e' b)))
    (hcompat : LargeGapCoordinateCrtCompatible H m q d e d' e') :
    crossCoordinateGcdProduct H d e d' e' ∣
      crossExceptionalModulus H m q := by
  let amax : CrossAuxiliaryDivisors H d e d' e' :=
    maximalCrossAuxiliaryDivisors hDpos hEpos
  have haux : CrossAuxiliaryAffineCompatible m q amax :=
    crossAuxiliaryAffineCompatible_of_coordinateCompatible
      hDpos hEpos hmE hDD hEE hcompat amax
  have hCrossSq : Squarefree (crossCoordinateGcdProduct H d e d' e') :=
    squarefree_crossCoordinateGcdProduct hDsq hDD hEE
  rw [← Nat.prod_primeFactors_of_squarefree hCrossSq]
  rw [Nat.prod_primeFactors_dvd_iff
    (crossExceptionalModulus_pos hm hq).ne']
  intro p hpFactors
  have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hpFactors
  have hpCross : p ∣ crossCoordinateGcdProduct H d e d' e' :=
    Nat.dvd_of_mem_primeFactors hpFactors
  unfold crossCoordinateGcdProduct at hpCross
  obtain ⟨b, hb, hpB⟩ :=
    (hpPrime.prime.dvd_finsetProd_iff
      (fun b : H ↦ ∏ a : H,
        Nat.gcd (Nat.lcm (d a) (d' a))
          (Nat.lcm (e b) (e' b)))).mp hpCross
  obtain ⟨c, hc, hpGcd⟩ :=
    (hpPrime.prime.dvd_finsetProd_iff
      (fun c : H ↦ Nat.gcd (Nat.lcm (d c) (d' c))
        (Nat.lcm (e b) (e' b)))).mp hpB
  have hpEntry : p ∣ (amax (b, c)).1 := by
    simpa [amax, maximalCrossAuxiliaryDivisors] using hpGcd
  have hpMod := prime_dvd_crossExceptionalModulus_of_auxiliaryCompatible
    haux (b, c) hpEntry
  exact Nat.mem_primeFactors.mpr
    ⟨hpPrime, hpMod, (crossExceptionalModulus_pos hm hq).ne'⟩

/-- Standard-support version used termwise in the normalization kernel. -/
theorem crossCoordinateGcdProduct_dvd_crossExceptionalModulus_standard
    {H : Finset ℕ} {RD RE W m q : ℕ} {d e d' e' : H → ℕ}
    (hm : 0 < m) (hq : q.Prime) (hRDq : RD ≤ q) (hREq : RE ≤ q)
    (hcover : BoundedGaps.Maynard.CoversShiftDifferencePrimes H W)
    (hd : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD W d)
    (hd' : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD W d')
    (he : BoundedGaps.Maynard.IsMaynardDivisorTuple H RE (W * m) e)
    (he' : BoundedGaps.Maynard.IsMaynardDivisorTuple H RE (W * m) e')
    (hcompat : LargeGapCoordinateCrtCompatible H m q d e d' e') :
    crossCoordinateGcdProduct H d e d' e' ∣
      crossExceptionalModulus H m q := by
  have hcoverE : BoundedGaps.Maynard.CoversShiftDifferencePrimes H (W * m) := by
    intro a b hab p hp hpd
    exact dvd_mul_of_dvd_left (hcover hab p hp hpd) m
  have hmE : m.Coprime (BoundedGaps.Maynard.divisorTupleProduct H e) :=
    Nat.Coprime.of_dvd_left (dvd_mul_left m W) he.2.1.symm
  have hmE' : m.Coprime (BoundedGaps.Maynard.divisorTupleProduct H e') :=
    Nat.Coprime.of_dvd_left (dvd_mul_left m W) he'.2.1.symm
  have hqD : q.Coprime (BoundedGaps.Maynard.divisorTupleProduct H d) :=
    Nat.Coprime.of_dvd_left (dvd_mul_left q W)
      (prime_mul_modulus_coprime_tupleProduct hd hq hRDq)
  have hqD' : q.Coprime (BoundedGaps.Maynard.divisorTupleProduct H d') :=
    Nat.Coprime.of_dvd_left (dvd_mul_left q W)
      (prime_mul_modulus_coprime_tupleProduct hd' hq hRDq)
  have hqE : q.Coprime (BoundedGaps.Maynard.divisorTupleProduct H e) :=
    Nat.Coprime.of_dvd_left (dvd_mul_left q (W * m))
      (prime_mul_modulus_coprime_tupleProduct he hq hREq)
  have hqE' : q.Coprime (BoundedGaps.Maynard.divisorTupleProduct H e') :=
    Nat.Coprime.of_dvd_left (dvd_mul_left q (W * m))
      (prime_mul_modulus_coprime_tupleProduct he' hq hREq)
  obtain ⟨hDD, hEE⟩ := withinFamilyLcm_pairwise_of_coordinateCompatible
    hm hq.pos hd hd' he he' hcover hcoverE hmE hmE'
      hqD hqD' hqE hqE' hcompat
  have hDpos : ∀ h : H, 0 < Nat.lcm (d h) (d' h) := fun h ↦
    Nat.lcm_pos (Nat.pos_of_ne_zero (hd.coordinate_squarefree h).ne_zero)
      (Nat.pos_of_ne_zero (hd'.coordinate_squarefree h).ne_zero)
  have hEpos : ∀ h : H, 0 < Nat.lcm (e h) (e' h) := fun h ↦
    Nat.lcm_pos (Nat.pos_of_ne_zero (he.coordinate_squarefree h).ne_zero)
      (Nat.pos_of_ne_zero (he'.coordinate_squarefree h).ne_zero)
  have hmELcm : ∀ h : H, m.Coprime (Nat.lcm (e h) (e' h)) := by
    intro h
    have hme : m.Coprime (e h) := Nat.Coprime.of_dvd_right
      (BoundedGaps.Maynard.divisorTupleCoordinate_dvd_product e h) hmE
    have hme' : m.Coprime (e' h) := Nat.Coprime.of_dvd_right
      (BoundedGaps.Maynard.divisorTupleCoordinate_dvd_product e' h) hmE'
    exact Nat.Coprime.of_dvd_right (Nat.lcm_dvd_mul (e h) (e' h))
      (hme.mul_right hme')
  have hDsq : ∀ a : H, Squarefree (Nat.lcm (d a) (d' a)) := fun a ↦
    BoundedGaps.Maynard.squarefree_lcm
      (hd.coordinate_squarefree a) (hd'.coordinate_squarefree a)
  exact crossCoordinateGcdProduct_dvd_crossExceptionalModulus
    hm hq hDpos hEpos hmELcm hDsq hDD hEE hcompat

/-- Every prime divisor of a first-family cross gcd lies beyond the
primorial cutoff. -/
theorem cutoff_lt_prime_of_dvd_crossAuxiliary
    {H : Finset ℕ} {RD w p : ℕ} {d e d' e' : H → ℕ}
    (hd : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD (primorial w) d)
    (hd' : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD (primorial w) d')
    (a : CrossAuxiliaryDivisors H d e d' e') (ba : H × H)
    (hpPrime : p.Prime) (hp : p ∣ (a ba).1) :
    w < p := by
  have haGcd : (a ba).1 ∣
      Nat.gcd (Nat.lcm (d ba.2) (d' ba.2))
        (Nat.lcm (e ba.1) (e' ba.1)) :=
    (Nat.mem_divisors.mp (a ba).2).1
  have hpLcm : p ∣ Nat.lcm (d ba.2) (d' ba.2) :=
    hp.trans (haGcd.trans (Nat.gcd_dvd_left _ _))
  rcases hpPrime.dvd_lcm.mp hpLcm with hpd | hpd'
  · by_contra hpNot
    have hpW : p ∣ primorial w :=
      hpPrime.dvd_primorial_iff.mpr (not_lt.mp hpNot)
    have hpcop : p.Coprime (primorial w) :=
      Nat.Coprime.of_dvd_left hpd (hd.coordinate_coprime_W ba.2)
    exact (hpPrime.coprime_iff_not_dvd.mp hpcop) hpW
  · by_contra hpNot
    have hpW : p ∣ primorial w :=
      hpPrime.dvd_primorial_iff.mpr (not_lt.mp hpNot)
    have hpcop : p.Coprime (primorial w) :=
      Nat.Coprime.of_dvd_left hpd' (hd'.coordinate_coprime_W ba.2)
    exact (hpPrime.coprime_iff_not_dvd.mp hpcop) hpW

/-- Every prime factor of the full cross-gcd product lies beyond the
primorial cutoff of the first Maynard family. -/
theorem cutoff_lt_prime_of_mem_crossCoordinateGcdProduct_primeFactors
    {H : Finset ℕ} {RD w p : ℕ} {d e d' e' : H → ℕ}
    (hd : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD (primorial w) d)
    (hd' : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD (primorial w) d')
    (hpFactors : p ∈ (crossCoordinateGcdProduct H d e d' e').primeFactors) :
    w < p := by
  have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hpFactors
  have hpCross : p ∣ crossCoordinateGcdProduct H d e d' e' :=
    Nat.dvd_of_mem_primeFactors hpFactors
  unfold crossCoordinateGcdProduct at hpCross
  obtain ⟨b, hb, hpB⟩ :=
    (hpPrime.prime.dvd_finsetProd_iff
      (fun b : H ↦ ∏ a : H,
        Nat.gcd (Nat.lcm (d a) (d' a))
          (Nat.lcm (e b) (e' b)))).mp hpCross
  obtain ⟨c, hc, hpGcd⟩ :=
    (hpPrime.prime.dvd_finsetProd_iff
      (fun c : H ↦ Nat.gcd (Nat.lcm (d c) (d' c))
        (Nat.lcm (e b) (e' b)))).mp hpB
  have hpLcm : p ∣ Nat.lcm (d c) (d' c) :=
    hpGcd.trans (Nat.gcd_dvd_left _ _)
  rcases hpPrime.dvd_lcm.mp hpLcm with hpd | hpd'
  · by_contra hpNot
    have hpW : p ∣ primorial w :=
      hpPrime.dvd_primorial_iff.mpr (not_lt.mp hpNot)
    have hpcop : p.Coprime (primorial w) :=
      Nat.Coprime.of_dvd_left hpd (hd.coordinate_coprime_W c)
    exact (hpPrime.coprime_iff_not_dvd.mp hpcop) hpW
  · by_contra hpNot
    have hpW : p ∣ primorial w :=
      hpPrime.dvd_primorial_iff.mpr (not_lt.mp hpNot)
    have hpcop : p.Coprime (primorial w) :=
      Nat.Coprime.of_dvd_left hpd' (hd'.coordinate_coprime_W c)
    exact (hpPrime.coprime_iff_not_dvd.mp hpcop) hpW

/-- On standard first-family supports the rough mass is the full
prime-log divisor mass. -/
theorem roughPrimeLogDivisorMass_crossCoordinateGcdProduct_eq
    {H : Finset ℕ} {RD w : ℕ} {d e d' e' : H → ℕ}
    (hd : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD (primorial w) d)
    (hd' : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD (primorial w) d') :
    roughPrimeLogDivisorMass (crossCoordinateGcdProduct H d e d' e') w =
      BoundedGaps.Maynard.primeLogDivisorMass
        (crossCoordinateGcdProduct H d e d' e') := by
  unfold roughPrimeLogDivisorMass
    BoundedGaps.Maynard.primeLogDivisorMass
  rw [Finset.filter_eq_self.mpr]
  intro p hp
  exact cutoff_lt_prime_of_mem_crossCoordinateGcdProduct_primeFactors
    hd hd' hp

/-- A nontrivial compatible auxiliary matrix is supported on an exceptional
prime beyond the pre-sieve cutoff.  The conclusion exposes both the matrix
entry and the signed affine integer that the prime divides. -/
theorem exists_rough_prime_dvd_crossAffineDifference_of_ne_one
    {H : Finset ℕ} {RD RE w m q : ℕ} {d e d' e' : H → ℕ}
    (hd : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD (primorial w) d)
    (hd' : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD (primorial w) d')
    (he : BoundedGaps.Maynard.IsMaynardDivisorTuple H RE (primorial w * m) e)
    (he' : BoundedGaps.Maynard.IsMaynardDivisorTuple H RE (primorial w * m) e')
    (a : CrossAuxiliaryDivisors H d e d' e')
    (hcompat : CrossAuxiliaryAffineCompatible m q a)
    (ha : a ≠ oneCrossAuxiliaryDivisors
      (fun h ↦ Nat.lcm_pos
        (Nat.pos_of_ne_zero (hd.coordinate_squarefree h).ne_zero)
        (Nat.pos_of_ne_zero (hd'.coordinate_squarefree h).ne_zero))
      (fun h ↦ Nat.lcm_pos
        (Nat.pos_of_ne_zero (he.coordinate_squarefree h).ne_zero)
        (Nat.pos_of_ne_zero (he'.coordinate_squarefree h).ne_zero))) :
    ∃ ba : H × H, ∃ p : ℕ,
      p.Prime ∧ w < p ∧ p ∣ (a ba).1 ∧
        (p : ℤ) ∣ crossAffineDifference m q ba := by
  let hDpos : ∀ h : H, 0 < Nat.lcm (d h) (d' h) := fun h ↦
    Nat.lcm_pos
      (Nat.pos_of_ne_zero (hd.coordinate_squarefree h).ne_zero)
      (Nat.pos_of_ne_zero (hd'.coordinate_squarefree h).ne_zero)
  let hEpos : ∀ h : H, 0 < Nat.lcm (e h) (e' h) := fun h ↦
    Nat.lcm_pos
      (Nat.pos_of_ne_zero (he.coordinate_squarefree h).ne_zero)
      (Nat.pos_of_ne_zero (he'.coordinate_squarefree h).ne_zero)
  have ha' : a ≠ oneCrossAuxiliaryDivisors hDpos hEpos := by
    simpa [hDpos, hEpos] using ha
  have hentry : ∃ ba : H × H, (a ba).1 ≠ 1 := by
    by_contra hall
    push_neg at hall
    exact ha' ((crossAuxiliaryDivisors_eq_one_iff hDpos hEpos a).mpr hall)
  obtain ⟨ba, hba⟩ := hentry
  obtain ⟨p, hpPrime, hpEntry⟩ := Nat.exists_prime_and_dvd hba
  exact ⟨ba, p, hpPrime,
    cutoff_lt_prime_of_dvd_crossAuxiliary hd hd' a ba hpPrime hpEntry,
    hpEntry,
    prime_dvd_crossAffineDifference_of_auxiliaryCompatible
      hcompat ba hpEntry⟩

/-- Finite-support form of the preceding witness: the rough collision prime
is a prime factor of `crossExceptionalModulus`. -/
theorem exists_rough_prime_mem_crossExceptionalModulus_of_ne_one
    {H : Finset ℕ} {RD RE w m q : ℕ} {d e d' e' : H → ℕ}
    (hm : 0 < m) (hq : q.Prime)
    (hd : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD (primorial w) d)
    (hd' : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD (primorial w) d')
    (he : BoundedGaps.Maynard.IsMaynardDivisorTuple H RE (primorial w * m) e)
    (he' : BoundedGaps.Maynard.IsMaynardDivisorTuple H RE (primorial w * m) e')
    (a : CrossAuxiliaryDivisors H d e d' e')
    (hcompat : CrossAuxiliaryAffineCompatible m q a)
    (ha : a ≠ oneCrossAuxiliaryDivisors
      (fun h ↦ Nat.lcm_pos
        (Nat.pos_of_ne_zero (hd.coordinate_squarefree h).ne_zero)
        (Nat.pos_of_ne_zero (hd'.coordinate_squarefree h).ne_zero))
      (fun h ↦ Nat.lcm_pos
        (Nat.pos_of_ne_zero (he.coordinate_squarefree h).ne_zero)
        (Nat.pos_of_ne_zero (he'.coordinate_squarefree h).ne_zero))) :
    ∃ ba : H × H, ∃ p : ℕ,
      p.Prime ∧ w < p ∧ p ∣ (a ba).1 ∧
        p ∈ (crossExceptionalModulus H m q).primeFactors := by
  obtain ⟨ba, p, hpPrime, hwp, hpEntry, hpDiff⟩ :=
    exists_rough_prime_dvd_crossAffineDifference_of_ne_one
      hd hd' he he' a hcompat ha
  have hpMod : p ∣ crossExceptionalModulus H m q :=
    prime_dvd_crossExceptionalModulus_of_auxiliaryCompatible
      hcompat ba hpEntry
  have hMod : crossExceptionalModulus H m q ≠ 0 :=
    (crossExceptionalModulus_pos hm hq).ne'
  exact ⟨ba, p, hpPrime, hwp, hpEntry,
    Nat.mem_primeFactors.mpr ⟨hpPrime, hpMod, hMod⟩⟩

/-- Uniform reciprocal-log envelope for all affine collision primes. -/
theorem roughPrimeLogDivisorMass_crossExceptionalModulus_le
    {H : Finset ℕ} {m q w : ℕ}
    (hm : 0 < m) (hq : q.Prime) (hw : 0 < w) :
    roughPrimeLogDivisorMass (crossExceptionalModulus H m q) w ≤
      Real.log (crossExceptionalModulus H m q) / w :=
  roughPrimeLogDivisorMass_le_log_div
    (crossExceptionalModulus_pos hm hq) hw

/-- Fully explicit exceptional-prime estimate.  In applications `H` is
fixed, the envelope is polynomial in the ambient endpoint, and `w → ∞`. -/
theorem roughPrimeLogDivisorMass_crossExceptionalModulus_le_envelope
    {H : Finset ℕ} {m q w : ℕ}
    (hm : 0 < m) (hq : q.Prime) (hw : 0 < w) :
    roughPrimeLogDivisorMass (crossExceptionalModulus H m q) w ≤
      (Fintype.card (H × H) : ℝ) *
        Real.log (crossAffineEnvelope H m q) / w := by
  have hModPos := crossExceptionalModulus_pos (H := H) hm hq
  have hEnvelopePos : 0 < crossAffineEnvelope H m q := by
    unfold crossAffineEnvelope
    omega
  have hModLe := crossExceptionalModulus_le_envelope_pow H m q
  have hlogLe :
      Real.log (crossExceptionalModulus H m q) ≤
        Real.log (crossAffineEnvelope H m q ^ Fintype.card (H × H)) := by
    apply Real.log_le_log
    · exact_mod_cast hModPos
    · exact_mod_cast hModLe
  calc
    roughPrimeLogDivisorMass (crossExceptionalModulus H m q) w ≤
        Real.log (crossExceptionalModulus H m q) / w :=
      roughPrimeLogDivisorMass_crossExceptionalModulus_le hm hq hw
    _ ≤ Real.log (crossAffineEnvelope H m q ^ Fintype.card (H × H)) / w := by
      exact div_le_div_of_nonneg_right hlogLe (by exact_mod_cast hw.le)
    _ = (Fintype.card (H × H) : ℝ) *
        Real.log (crossAffineEnvelope H m q) / w := by
      push_cast
      rw [Real.log_pow]

/-- The actual cross-gcd factor of a compatible standard summand has the
same explicit reciprocal-log envelope. -/
theorem roughPrimeLogDivisorMass_crossCoordinateGcdProduct_le_envelope_standard
    {H : Finset ℕ} {RD RE W m q w : ℕ} {d e d' e' : H → ℕ}
    (hm : 0 < m) (hq : q.Prime) (hw : 0 < w)
    (hRDq : RD ≤ q) (hREq : RE ≤ q)
    (hcover : BoundedGaps.Maynard.CoversShiftDifferencePrimes H W)
    (hd : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD W d)
    (hd' : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD W d')
    (he : BoundedGaps.Maynard.IsMaynardDivisorTuple H RE (W * m) e)
    (he' : BoundedGaps.Maynard.IsMaynardDivisorTuple H RE (W * m) e')
    (hcompat : LargeGapCoordinateCrtCompatible H m q d e d' e') :
    roughPrimeLogDivisorMass (crossCoordinateGcdProduct H d e d' e') w ≤
      (Fintype.card (H × H) : ℝ) *
        Real.log (crossAffineEnvelope H m q) / w := by
  have hdiv := crossCoordinateGcdProduct_dvd_crossExceptionalModulus_standard
    hm hq hRDq hREq hcover hd hd' he he' hcompat
  calc
    roughPrimeLogDivisorMass (crossCoordinateGcdProduct H d e d' e') w ≤
        roughPrimeLogDivisorMass (crossExceptionalModulus H m q) w :=
      roughPrimeLogDivisorMass_mono_of_dvd hdiv
        (crossExceptionalModulus_pos hm hq).ne'
    _ ≤ _ := roughPrimeLogDivisorMass_crossExceptionalModulus_le_envelope
      hm hq hw

/-- Full prime-log mass bound in the concrete primorial pre-sieve. -/
theorem primeLogDivisorMass_crossCoordinateGcdProduct_le_envelope_standard
    {H : Finset ℕ} {RD RE w m q : ℕ} {d e d' e' : H → ℕ}
    (hm : 0 < m) (hq : q.Prime) (hw : 0 < w)
    (hRDq : RD ≤ q) (hREq : RE ≤ q)
    (hcover : BoundedGaps.Maynard.CoversShiftDifferencePrimes H (primorial w))
    (hd : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD (primorial w) d)
    (hd' : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD (primorial w) d')
    (he : BoundedGaps.Maynard.IsMaynardDivisorTuple H RE (primorial w * m) e)
    (he' : BoundedGaps.Maynard.IsMaynardDivisorTuple H RE (primorial w * m) e')
    (hcompat : LargeGapCoordinateCrtCompatible H m q d e d' e') :
    BoundedGaps.Maynard.primeLogDivisorMass
        (crossCoordinateGcdProduct H d e d' e') ≤
      (Fintype.card (H × H) : ℝ) *
        Real.log (crossAffineEnvelope H m q) / w := by
  rw [← roughPrimeLogDivisorMass_crossCoordinateGcdProduct_eq hd hd']
  exact roughPrimeLogDivisorMass_crossCoordinateGcdProduct_le_envelope_standard
    hm hq hw hRDq hREq hcover hd hd' he he' hcompat

end

end Erdos4b
