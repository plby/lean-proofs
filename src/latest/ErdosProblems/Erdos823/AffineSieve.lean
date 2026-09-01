import BoundedGaps.Proof.MainTheorem
import ErdosProblems.Erdos823.AffinePrimes

/-!
# The Maynard sieve for the forms `c i * n - 1`

This file develops the finite, algebraic part of the unequal-slope version
of Maynard's sieve needed by Pollack.  The index type is the 105-element
Engelsma tuple, but its numerical entries play no role: they provide exactly
the finite coordinate set for which the checked Maynard coefficient is
available.
-/

namespace Erdos823

open Filter Finset
open scoped BigOperators

noncomputable section

namespace AffineSieve

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- Every prime divisor of every leading coefficient has entered the
pre-sieving modulus.  Prime powers are deliberately not required. -/
def CoefficientPrimesCovered (c : BoundedGaps.engelsmaTuple → ℕ) (W : ℕ) : Prop :=
  ∀ i p, p.Prime → p ∣ c i → p ∣ W

/-- Every prime divisor of a nonzero determinant of two forms has entered
the pre-sieving modulus.  For `c_i n - 1` the determinant is `c_i-c_j`. -/
def CoefficientDifferencesCovered (c : BoundedGaps.engelsmaTuple → ℕ) (W : ℕ) : Prop :=
  ∀ i j : BoundedGaps.engelsmaTuple, i ≠ j →
    ∀ p, p.Prime → p ∣ Nat.dist (c i) (c j) → p ∣ W

/-- Divisor-tuple condition for the affine forms.  Congruence is preferable
to truncated subtraction here and is equivalent to divisibility of
`c i * n - 1` whenever `n` and `c i` are positive. -/
def divisorTupleCondition (c : BoundedGaps.engelsmaTuple → ℕ) (n : ℕ)
    (d : BoundedGaps.engelsmaTuple → ℕ) : Prop :=
  ∀ i, c i * n ≡ 1 [MOD d i]

def divisorTuplePairCondition (c : BoundedGaps.engelsmaTuple → ℕ) (n : ℕ)
    (d e : BoundedGaps.engelsmaTuple → ℕ) : Prop :=
  divisorTupleCondition c n d ∧ divisorTupleCondition c n e

/-- The square Selberg weight formed from affine divisor conditions. -/
def squareDivisorWeight (c : BoundedGaps.engelsmaTuple → ℕ)
    (D : Finset (BoundedGaps.engelsmaTuple → ℕ))
    (coeff : (BoundedGaps.engelsmaTuple → ℕ) → ℝ) (n : ℕ) : ℝ :=
  (∑ d ∈ D.filter (divisorTupleCondition c n), coeff d) ^ 2

/-- Restriction to the universally admissible class `n ≡ 0 (mod W)`.
On this class every form is `-1` modulo every prime dividing `W`. -/
def preSievedWeight (c : BoundedGaps.engelsmaTuple → ℕ)
    (D : Finset (BoundedGaps.engelsmaTuple → ℕ)) (coeff : (BoundedGaps.engelsmaTuple → ℕ) → ℝ)
    (W n : ℕ) : ℝ :=
  if n ≡ 0 [MOD W] then squareDivisorWeight c D coeff n else 0

def primeCount (c : BoundedGaps.engelsmaTuple → ℕ) (n : ℕ) : ℕ :=
  (Finset.univ.filter fun i : BoundedGaps.engelsmaTuple ↦ (c i * n - 1).Prime).card

def primeWeightedSum (c : BoundedGaps.engelsmaTuple → ℕ) (N : ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑ n ∈ Finset.Ico N (2 * N), (primeCount c n : ℝ) * w n

def excess (c : BoundedGaps.engelsmaTuple → ℕ) (N : ℕ) (w : ℕ → ℝ) : ℝ :=
  primeWeightedSum c N w - BoundedGaps.Maynard.sieveWeightSum N w

theorem coefficient_coprime_of_covered
    {c : BoundedGaps.engelsmaTuple → ℕ} {W m : ℕ}
    (hcover : CoefficientPrimesCovered c W) (hmW : Nat.Coprime m W)
    (i : BoundedGaps.engelsmaTuple) : Nat.Coprime (c i) m := by
  by_contra hnot
  obtain ⟨p, hp, hpc, hpm⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnot
  have hpW : p ∣ W := hcover i p hp hpc
  have hcop : Nat.Coprime p W := hmW.coprime_dvd_left hpm
  exact (hp.coprime_iff_not_dvd.mp hcop) hpW

/-- An explicit inverse residue.  Euler's theorem is enough and avoids any
choice of a modular inverse. -/
def coordinateResidue (a m : ℕ) : ℕ :=
  a ^ (Nat.totient m - 1)

theorem mul_coordinateResidue_modEq_one
    {a m : ℕ} (hm : 0 < m) (hcop : Nat.Coprime a m) :
    a * coordinateResidue a m ≡ 1 [MOD m] := by
  have hphi : 0 < Nat.totient m := Nat.totient_pos.mpr hm
  have hexp : Nat.totient m - 1 + 1 = Nat.totient m := by omega
  calc
    a * coordinateResidue a m = a ^ Nat.totient m := by
      rw [coordinateResidue, ← pow_succ']
      rw [hexp]
    _ ≡ 1 [MOD m] := Nat.ModEq.pow_totient hcop

theorem modEq_coordinateResidue_iff
    {a m n : ℕ} (hm : 0 < m) (hcop : Nat.Coprime a m) :
    n ≡ coordinateResidue a m [MOD m] ↔ a * n ≡ 1 [MOD m] := by
  have hinv := mul_coordinateResidue_modEq_one hm hcop
  constructor
  · intro hn
    exact (hn.mul_left a).trans hinv
  · intro hn
    exact Nat.ModEq.cancel_left_of_coprime (m := m) (c := a)
      (by rw [Nat.gcd_comm]; exact hcop) (hn.trans hinv.symm)

def pairCoordinateResidue (c : BoundedGaps.engelsmaTuple → ℕ)
    (d e : BoundedGaps.engelsmaTuple → ℕ) (i : BoundedGaps.engelsmaTuple) : ℕ :=
  coordinateResidue (c i)
    (BoundedGaps.Maynard.divisorTupleLcm BoundedGaps.engelsmaTuple d e i)

theorem coefficient_coprime_pairCoordinate
    {c : BoundedGaps.engelsmaTuple → ℕ} {R W : ℕ} {d e : BoundedGaps.engelsmaTuple → ℕ}
    (hcover : CoefficientPrimesCovered c W)
    (hd : BoundedGaps.Maynard.IsMaynardDivisorTuple BoundedGaps.engelsmaTuple R W d)
    (he : BoundedGaps.Maynard.IsMaynardDivisorTuple BoundedGaps.engelsmaTuple R W e)
    (i : BoundedGaps.engelsmaTuple) :
    Nat.Coprime (c i) (BoundedGaps.Maynard.divisorTupleLcm BoundedGaps.engelsmaTuple d e i) := by
  apply coefficient_coprime_of_covered hcover
  have hWd : Nat.Coprime W (d i) := (hd.coordinate_coprime_W i).symm
  have hWe : Nat.Coprime W (e i) := (he.coordinate_coprime_W i).symm
  have hWprod : Nat.Coprime W (d i * e i) := hWd.mul_right hWe
  exact (Nat.Coprime.of_dvd_right (Nat.lcm_dvd_mul (d i) (e i)) hWprod).symm

theorem divisorTuplePairCondition_iff_modEq_residue
    {c : BoundedGaps.engelsmaTuple → ℕ} {R W : ℕ} {d e : BoundedGaps.engelsmaTuple → ℕ}
    (hcover : CoefficientPrimesCovered c W)
    (hd : BoundedGaps.Maynard.IsMaynardDivisorTuple BoundedGaps.engelsmaTuple R W d)
    (he : BoundedGaps.Maynard.IsMaynardDivisorTuple BoundedGaps.engelsmaTuple R W e)
    (n : ℕ) :
    divisorTuplePairCondition c n d e ↔
      ∀ i : BoundedGaps.engelsmaTuple, n ≡ pairCoordinateResidue c d e i
        [MOD BoundedGaps.Maynard.divisorTupleLcm BoundedGaps.engelsmaTuple d e i] := by
  constructor
  · rintro ⟨hdvd, hevd⟩ i
    apply (modEq_coordinateResidue_iff
      (BoundedGaps.Maynard.divisorTupleLcm_pos_of_isMaynard hd he i)
      (coefficient_coprime_pairCoordinate hcover hd he i)).mpr
    exact Nat.mod_lcm (hdvd i) (hevd i)
  · intro hres
    refine ⟨?_, ?_⟩ <;> intro i
    · have hfull := (modEq_coordinateResidue_iff
          (BoundedGaps.Maynard.divisorTupleLcm_pos_of_isMaynard hd he i)
          (coefficient_coprime_pairCoordinate hcover hd he i)).mp (hres i)
      exact hfull.of_dvd (Nat.dvd_lcm_left (d i) (e i))
    · have hfull := (modEq_coordinateResidue_iff
          (BoundedGaps.Maynard.divisorTupleLcm_pos_of_isMaynard hd he i)
          (coefficient_coprime_pairCoordinate hcover hd he i)).mp (hres i)
      exact hfull.of_dvd (Nat.dvd_lcm_right (d i) (e i))

theorem divisorTuplePairCondition_iff_modEq_residue_list
    {c : BoundedGaps.engelsmaTuple → ℕ} {R W : ℕ} {d e : BoundedGaps.engelsmaTuple → ℕ}
    (hcover : CoefficientPrimesCovered c W)
    (hd : BoundedGaps.Maynard.IsMaynardDivisorTuple BoundedGaps.engelsmaTuple R W d)
    (he : BoundedGaps.Maynard.IsMaynardDivisorTuple BoundedGaps.engelsmaTuple R W e)
    (n : ℕ) :
    divisorTuplePairCondition c n d e ↔
      ∀ i ∈ BoundedGaps.engelsmaTuple.attach.toList,
        n ≡ pairCoordinateResidue c d e i
          [MOD BoundedGaps.Maynard.divisorTupleLcm BoundedGaps.engelsmaTuple d e i] := by
  simpa using divisorTuplePairCondition_iff_modEq_residue hcover hd he n

noncomputable def pairCrtResidue
    (c : BoundedGaps.engelsmaTuple → ℕ) (R W : ℕ) (d e : BoundedGaps.engelsmaTuple → ℕ)
    (hd : BoundedGaps.Maynard.IsMaynardDivisorTuple BoundedGaps.engelsmaTuple R W d)
    (he : BoundedGaps.Maynard.IsMaynardDivisorTuple BoundedGaps.engelsmaTuple R W e)
    (hcross : BoundedGaps.Maynard.IsCrossCoordinateCoprime BoundedGaps.engelsmaTuple d e) : ℕ :=
  Nat.chineseRemainderOfList
    (BoundedGaps.Maynard.preSievedResidue 0 (pairCoordinateResidue c d e))
    (BoundedGaps.Maynard.preSievedModulus W
      (BoundedGaps.Maynard.divisorTupleLcm BoundedGaps.engelsmaTuple d e))
    (BoundedGaps.Maynard.preSievedModulusList BoundedGaps.engelsmaTuple.attach.toList)
    (BoundedGaps.Maynard.preSievedModulusList_pairwise W
      (BoundedGaps.Maynard.divisorTupleLcm BoundedGaps.engelsmaTuple d e)
      BoundedGaps.engelsmaTuple.attach.toList
      (BoundedGaps.Maynard.isMaynardDivisorTuple_pair_lcm_compatible
        hd he hcross))

theorem modEq_pairCrtResidue_iff
    {c : BoundedGaps.engelsmaTuple → ℕ} {R W : ℕ} {d e : BoundedGaps.engelsmaTuple → ℕ}
    (hcover : CoefficientPrimesCovered c W)
    (hd : BoundedGaps.Maynard.IsMaynardDivisorTuple BoundedGaps.engelsmaTuple R W d)
    (he : BoundedGaps.Maynard.IsMaynardDivisorTuple BoundedGaps.engelsmaTuple R W e)
    (hcross : BoundedGaps.Maynard.IsCrossCoordinateCoprime BoundedGaps.engelsmaTuple d e)
    (n : ℕ) :
    n ≡ pairCrtResidue c R W d e hd he hcross
        [MOD BoundedGaps.Maynard.divisorPairModulus BoundedGaps.engelsmaTuple W d e] ↔
      n ≡ 0 [MOD W] ∧ divisorTuplePairCondition c n d e := by
  rw [← BoundedGaps.Maynard.preSievedDivisorPairModulus_eq]
  unfold pairCrtResidue
  rw [BoundedGaps.Maynard.modEq_preSieved_crt_iff
    (pairCoordinateResidue c d e)
    (BoundedGaps.Maynard.divisorTupleLcm BoundedGaps.engelsmaTuple d e)
    BoundedGaps.engelsmaTuple.attach.toList W 0 n
    (BoundedGaps.Maynard.isMaynardDivisorTuple_pair_lcm_compatible
      hd he hcross)]
  rw [← divisorTuplePairCondition_iff_modEq_residue_list hcover hd he n]

theorem dvd_dist_of_modEq {p a b : ℕ} (h : a ≡ b [MOD p]) :
    p ∣ Nat.dist a b := by
  by_cases hab : a ≤ b
  · rw [Nat.dist_eq_sub_of_le hab]
    apply Int.natCast_dvd_natCast.mp
    rw [Int.natCast_sub hab]
    exact h.dvd
  · have hba : b ≤ a := le_of_not_ge hab
    rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hba]
    apply Int.natCast_dvd_natCast.mp
    rw [Int.natCast_sub hba]
    exact h.symm.dvd

theorem isCrossCoordinateCoprime_of_pairCondition
    {c : BoundedGaps.engelsmaTuple → ℕ} {R W : ℕ} {d e : BoundedGaps.engelsmaTuple → ℕ}
    (hd : BoundedGaps.Maynard.IsMaynardDivisorTuple BoundedGaps.engelsmaTuple R W d)
    (he : BoundedGaps.Maynard.IsMaynardDivisorTuple BoundedGaps.engelsmaTuple R W e)
    (hcoverage : CoefficientDifferencesCovered c W) {n : ℕ}
    (hpair : divisorTuplePairCondition c n d e) :
    BoundedGaps.Maynard.IsCrossCoordinateCoprime BoundedGaps.engelsmaTuple d e := by
  intro a b hab
  constructor
  · by_contra hnot
    obtain ⟨p, hp, hpa, hpb⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnot
    have ha : c a * n ≡ 1 [MOD p] := (hpair.1 a).of_dvd hpa
    have hb : c b * n ≡ 1 [MOD p] := (hpair.2 b).of_dvd hpb
    have hcoeff : c b ≡ c a [MOD p] := by
      have ha' := ha.mul_left (c b)
      have hb' := hb.mul_left (c a)
      simpa [mul_assoc, mul_comm, mul_left_comm] using
        ha'.symm.trans (by
          simpa [mul_assoc, mul_comm, mul_left_comm] using hb')
    have hpdist : p ∣ Nat.dist (c a) (c b) :=
      dvd_dist_of_modEq hcoeff.symm
    have hpW : p ∣ W := hcoverage a b hab p hp hpdist
    have hpcop : Nat.Coprime p W :=
      (hd.coordinate_coprime_W a).coprime_dvd_left hpa
    exact (hp.coprime_iff_not_dvd.mp hpcop) hpW
  · by_contra hnot
    obtain ⟨p, hp, hpa, hpb⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnot
    have ha : c a * n ≡ 1 [MOD p] := (hpair.2 a).of_dvd hpa
    have hb : c b * n ≡ 1 [MOD p] := (hpair.1 b).of_dvd hpb
    have hcoeff : c b ≡ c a [MOD p] := by
      have ha' := ha.mul_left (c b)
      have hb' := hb.mul_left (c a)
      simpa [mul_assoc, mul_comm, mul_left_comm] using
        ha'.symm.trans (by
          simpa [mul_assoc, mul_comm, mul_left_comm] using hb')
    have hpdist : p ∣ Nat.dist (c a) (c b) :=
      dvd_dist_of_modEq hcoeff.symm
    have hpW : p ∣ W := hcoverage a b hab p hp hpdist
    have hpcop : Nat.Coprime p W :=
      (he.coordinate_coprime_W a).coprime_dvd_left hpa
    exact (hp.coprime_iff_not_dvd.mp hpcop) hpW

theorem squareDivisorWeight_eq_double_sum
    (c : BoundedGaps.engelsmaTuple → ℕ) (D : Finset (BoundedGaps.engelsmaTuple → ℕ))
    (coeff : (BoundedGaps.engelsmaTuple → ℕ) → ℝ) (n : ℕ) :
    squareDivisorWeight c D coeff n =
      ∑ d ∈ D.filter (divisorTupleCondition c n),
        ∑ e ∈ D.filter (divisorTupleCondition c n), coeff d * coeff e := by
  classical
  unfold squareDivisorWeight
  simp only [pow_two, Finset.mul_sum, mul_comm]

theorem preSievedWeight_eq_pair_indicator
    (c : BoundedGaps.engelsmaTuple → ℕ) (D : Finset (BoundedGaps.engelsmaTuple → ℕ))
    (coeff : (BoundedGaps.engelsmaTuple → ℕ) → ℝ) (W n : ℕ) :
    preSievedWeight c D coeff W n =
      ∑ d ∈ D, ∑ e ∈ D,
        if n ≡ 0 [MOD W] ∧ divisorTuplePairCondition c n d e then
          coeff d * coeff e else 0 := by
  classical
  by_cases hres : n ≡ 0 [MOD W]
  · simp only [preSievedWeight, if_pos hres]
    rw [squareDivisorWeight_eq_double_sum]
    simp_rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hdc : divisorTupleCondition c n d
    · simp [divisorTuplePairCondition, hres, hdc]
    · simp [divisorTuplePairCondition, hres, hdc]
  · simp [preSievedWeight, hres]

theorem sieveWeightSum_eq_pair_indicator
    (c : BoundedGaps.engelsmaTuple → ℕ) (D : Finset (BoundedGaps.engelsmaTuple → ℕ))
    (coeff : (BoundedGaps.engelsmaTuple → ℕ) → ℝ) (W N : ℕ) :
    BoundedGaps.Maynard.sieveWeightSum N (preSievedWeight c D coeff W) =
      ∑ d ∈ D, ∑ e ∈ D, ∑ n ∈ Finset.Ico N (2 * N),
        if n ≡ 0 [MOD W] ∧ divisorTuplePairCondition c n d e then
          coeff d * coeff e else 0 := by
  classical
  unfold BoundedGaps.Maynard.sieveWeightSum
  calc
    (∑ n ∈ Finset.Ico N (2 * N), preSievedWeight c D coeff W n) =
        ∑ n ∈ Finset.Ico N (2 * N),
          ∑ d ∈ D, ∑ e ∈ D,
            if n ≡ 0 [MOD W] ∧ divisorTuplePairCondition c n d e then
              coeff d * coeff e else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      exact preSievedWeight_eq_pair_indicator c D coeff W n
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.sum_comm]

def compatiblePairSieveSum
    (c : BoundedGaps.engelsmaTuple → ℕ) (D : Finset (BoundedGaps.engelsmaTuple → ℕ))
    (W N : ℕ) (coeff : (BoundedGaps.engelsmaTuple → ℕ) → ℝ) : ℝ :=
  ∑ d ∈ D,
    ∑ e ∈ D.filter
      (fun e ↦ BoundedGaps.Maynard.IsCrossCoordinateCoprime BoundedGaps.engelsmaTuple d e),
      ∑ n ∈ Finset.Ico N (2 * N),
        if n ≡ 0 [MOD W] ∧ divisorTuplePairCondition c n d e then
          coeff d * coeff e else 0

def compatiblePairCardSum
    (c : BoundedGaps.engelsmaTuple → ℕ) (D : Finset (BoundedGaps.engelsmaTuple → ℕ))
    (W N : ℕ) (coeff : (BoundedGaps.engelsmaTuple → ℕ) → ℝ) : ℝ :=
  ∑ d ∈ D,
    ∑ e ∈ D.filter
      (fun e ↦ BoundedGaps.Maynard.IsCrossCoordinateCoprime BoundedGaps.engelsmaTuple d e),
      (((Finset.Ico N (2 * N)).filter fun n ↦
        n ≡ 0 [MOD W] ∧ divisorTuplePairCondition c n d e).card : ℝ) *
          (coeff d * coeff e)

def pairCountError
    (c : BoundedGaps.engelsmaTuple → ℕ) (W N : ℕ) (d e : BoundedGaps.engelsmaTuple → ℕ) : ℝ :=
  (((Finset.Ico N (2 * N)).filter fun n ↦
      n ≡ 0 [MOD W] ∧ divisorTuplePairCondition c n d e).card : ℝ) -
    (N : ℝ) / BoundedGaps.Maynard.divisorPairModulus BoundedGaps.engelsmaTuple W d e

def compatiblePairErrorSum
    (c : BoundedGaps.engelsmaTuple → ℕ) (D : Finset (BoundedGaps.engelsmaTuple → ℕ))
    (W N : ℕ) (coeff : (BoundedGaps.engelsmaTuple → ℕ) → ℝ) : ℝ :=
  ∑ d ∈ D,
    ∑ e ∈ D.filter
      (fun e ↦ BoundedGaps.Maynard.IsCrossCoordinateCoprime BoundedGaps.engelsmaTuple d e),
      pairCountError c W N d e * (coeff d * coeff e)

theorem sieveWeightSum_eq_compatiblePairSieveSum
    {c : BoundedGaps.engelsmaTuple → ℕ} {D : Finset (BoundedGaps.engelsmaTuple → ℕ)}
    {coeff : (BoundedGaps.engelsmaTuple → ℕ) → ℝ} {W N R : ℕ}
    (hD : ∀ d ∈ D,
      BoundedGaps.Maynard.IsMaynardDivisorTuple BoundedGaps.engelsmaTuple R W d)
    (hcoverage : CoefficientDifferencesCovered c W) :
    BoundedGaps.Maynard.sieveWeightSum N (preSievedWeight c D coeff W) =
      compatiblePairSieveSum c D W N coeff := by
  classical
  unfold compatiblePairSieveSum
  rw [sieveWeightSum_eq_pair_indicator]
  apply Finset.sum_congr rfl
  intro d hd_mem
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e he_mem
  by_cases hcross :
      BoundedGaps.Maynard.IsCrossCoordinateCoprime BoundedGaps.engelsmaTuple d e
  · simp [hcross]
  · have hd := hD d hd_mem
    have he := hD e he_mem
    have hinner :
        (∑ n ∈ Finset.Ico N (2 * N),
          if n ≡ 0 [MOD W] ∧ divisorTuplePairCondition c n d e then
            coeff d * coeff e else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      have hfalse : ¬(n ≡ 0 [MOD W] ∧
          divisorTuplePairCondition c n d e) := by
        intro hcond
        exact hcross (isCrossCoordinateCoprime_of_pairCondition
          hd he hcoverage hcond.2)
      simp [hfalse]
    simp [hcross, hinner]

theorem compatiblePairSieveSum_eq_cardSum
    {c : BoundedGaps.engelsmaTuple → ℕ} {D : Finset (BoundedGaps.engelsmaTuple → ℕ)}
    {coeff : (BoundedGaps.engelsmaTuple → ℕ) → ℝ} {W N : ℕ} :
    compatiblePairSieveSum c D W N coeff =
      compatiblePairCardSum c D W N coeff := by
  classical
  unfold compatiblePairSieveSum compatiblePairCardSum
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro e he
  rw [← Finset.sum_filter]
  rw [Finset.sum_const]
  simp [nsmul_eq_mul]

theorem pairCountError_abs_le_one
    {c : BoundedGaps.engelsmaTuple → ℕ} {R W N : ℕ} {d e : BoundedGaps.engelsmaTuple → ℕ}
    (hcover : CoefficientPrimesCovered c W) (hW : 0 < W)
    (hd : BoundedGaps.Maynard.IsMaynardDivisorTuple BoundedGaps.engelsmaTuple R W d)
    (he : BoundedGaps.Maynard.IsMaynardDivisorTuple BoundedGaps.engelsmaTuple R W e)
    (hcross : BoundedGaps.Maynard.IsCrossCoordinateCoprime BoundedGaps.engelsmaTuple d e) :
    |pairCountError c W N d e| ≤ 1 := by
  let q := BoundedGaps.Maynard.divisorPairModulus BoundedGaps.engelsmaTuple W d e
  let r := pairCrtResidue c R W d e hd he hcross
  have hq : 0 < q :=
    BoundedGaps.Maynard.divisorPairModulus_pos hW hd he
  have hfilter :
      (Finset.Ico N (2 * N)).filter (fun n ↦
        n ≡ 0 [MOD W] ∧ divisorTuplePairCondition c n d e) =
      (Finset.Ico N (2 * N)).filter (fun n ↦ n ≡ r [MOD q]) := by
    ext n
    simp only [Finset.mem_filter]
    exact and_congr_right fun _ ↦
      (modEq_pairCrtResidue_iff hcover hd he hcross n).symm
  unfold pairCountError
  rw [hfilter]
  have herr := BoundedGaps.Maynard.intervalModEqCardError_abs_le_one
    N (2 * N) q r (by omega) hq
  rw [BoundedGaps.Maynard.intervalModEqCardError] at herr
  have hlength : ((2 * N : ℕ) : ℝ) - (N : ℝ) = N := by
    push_cast
    ring
  rw [hlength] at herr
  change
    |↑((Finset.Ico N (2 * N)).filter (fun n ↦ n ≡ r [MOD q])).card -
        (N : ℝ) / q| ≤ 1
  exact herr

theorem compatiblePairCardSum_eq_main_add_error
    {c : BoundedGaps.engelsmaTuple → ℕ} {D : Finset (BoundedGaps.engelsmaTuple → ℕ)}
    {coeff : (BoundedGaps.engelsmaTuple → ℕ) → ℝ} {W N : ℕ} :
    compatiblePairCardSum c D W N coeff =
      BoundedGaps.Maynard.compatibleDivisorPairMainSum
        BoundedGaps.engelsmaTuple D W N coeff + compatiblePairErrorSum c D W N coeff := by
  classical
  unfold compatiblePairCardSum
    BoundedGaps.Maynard.compatibleDivisorPairMainSum compatiblePairErrorSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e he
  unfold pairCountError
  ring

theorem abs_compatiblePairErrorSum_le_coefficientMass
    {c : BoundedGaps.engelsmaTuple → ℕ} {D : Finset (BoundedGaps.engelsmaTuple → ℕ)}
    {coeff : (BoundedGaps.engelsmaTuple → ℕ) → ℝ} {W N R : ℕ}
    (hcover : CoefficientPrimesCovered c W) (hW : 0 < W)
    (hD : ∀ d ∈ D,
      BoundedGaps.Maynard.IsMaynardDivisorTuple BoundedGaps.engelsmaTuple R W d) :
    |compatiblePairErrorSum c D W N coeff| ≤
      BoundedGaps.Maynard.compatibleDivisorPairCoefficientMass
        BoundedGaps.engelsmaTuple D coeff := by
  classical
  unfold compatiblePairErrorSum
    BoundedGaps.Maynard.compatibleDivisorPairCoefficientMass
  calc
    |∑ d ∈ D, ∑ e ∈ D.filter
        (fun e ↦ BoundedGaps.Maynard.IsCrossCoordinateCoprime BoundedGaps.engelsmaTuple d e),
        pairCountError c W N d e * (coeff d * coeff e)| ≤
        ∑ d ∈ D, |∑ e ∈ D.filter
          (fun e ↦ BoundedGaps.Maynard.IsCrossCoordinateCoprime BoundedGaps.engelsmaTuple d e),
          pairCountError c W N d e * (coeff d * coeff e)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ D, ∑ e ∈ D.filter
        (fun e ↦ BoundedGaps.Maynard.IsCrossCoordinateCoprime BoundedGaps.engelsmaTuple d e),
        |pairCountError c W N d e * (coeff d * coeff e)| := by
      apply Finset.sum_le_sum
      intro d hd
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ D, ∑ e ∈ D.filter
        (fun e ↦ BoundedGaps.Maynard.IsCrossCoordinateCoprime BoundedGaps.engelsmaTuple d e),
        |coeff d * coeff e| := by
      apply Finset.sum_le_sum
      intro d hd_mem
      apply Finset.sum_le_sum
      intro e he_mem
      obtain ⟨heD, hcross⟩ := Finset.mem_filter.mp he_mem
      rw [abs_mul]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (pairCountError_abs_le_one hcover hW (hD d hd_mem) (hD e heD) hcross)
        (abs_nonneg (coeff d * coeff e))

theorem sieveWeightSum_eq_main_add_error
    {c : BoundedGaps.engelsmaTuple → ℕ} {D : Finset (BoundedGaps.engelsmaTuple → ℕ)}
    {coeff : (BoundedGaps.engelsmaTuple → ℕ) → ℝ} {W N R : ℕ}
    (hD : ∀ d ∈ D,
      BoundedGaps.Maynard.IsMaynardDivisorTuple BoundedGaps.engelsmaTuple R W d)
    (hcoverage : CoefficientDifferencesCovered c W) :
    BoundedGaps.Maynard.sieveWeightSum N (preSievedWeight c D coeff W) =
      BoundedGaps.Maynard.compatibleDivisorPairMainSum BoundedGaps.engelsmaTuple D W N coeff +
        compatiblePairErrorSum c D W N coeff := by
  rw [sieveWeightSum_eq_compatiblePairSieveSum hD hcoverage]
  rw [compatiblePairSieveSum_eq_cardSum]
  exact compatiblePairCardSum_eq_main_add_error

theorem squareDivisorWeight_nonneg
    (c : BoundedGaps.engelsmaTuple → ℕ) (D : Finset (BoundedGaps.engelsmaTuple → ℕ))
    (coeff : (BoundedGaps.engelsmaTuple → ℕ) → ℝ) (n : ℕ) :
    0 ≤ squareDivisorWeight c D coeff n := by
  exact sq_nonneg _

theorem preSievedWeight_nonneg
    (c : BoundedGaps.engelsmaTuple → ℕ) (D : Finset (BoundedGaps.engelsmaTuple → ℕ))
    (coeff : (BoundedGaps.engelsmaTuple → ℕ) → ℝ) (W n : ℕ) :
    0 ≤ preSievedWeight c D coeff W n := by
  unfold preSievedWeight
  split_ifs
  · exact squareDivisorWeight_nonneg c D coeff n
  · exact le_rfl

theorem excess_eq_sum (c : BoundedGaps.engelsmaTuple → ℕ) (N : ℕ) (w : ℕ → ℝ) :
    excess c N w =
      ∑ n ∈ Finset.Ico N (2 * N), ((primeCount c n : ℝ) - 1) * w n := by
  simp only [excess, primeWeightedSum, BoundedGaps.Maynard.sieveWeightSum,
    sub_mul, Finset.sum_sub_distrib, one_mul]

theorem exists_two_primes_of_excess_pos
    {c : BoundedGaps.engelsmaTuple → ℕ} {N : ℕ} {w : ℕ → ℝ}
    (hw : ∀ n ∈ Finset.Ico N (2 * N), 0 ≤ w n)
    (hpos : 0 < excess c N w) :
    ∃ n ∈ Finset.Ico N (2 * N), 2 ≤ primeCount c n := by
  by_contra hnone
  have hterm : ∀ n ∈ Finset.Ico N (2 * N),
      ((primeCount c n : ℝ) - 1) * w n ≤ 0 := by
    intro n hn
    have hcount : primeCount c n ≤ 1 := by
      have hnot : ¬ 2 ≤ primeCount c n := by
        intro htwo
        exact hnone ⟨n, hn, htwo⟩
      omega
    have hcountR : (primeCount c n : ℝ) ≤ 1 := by exact_mod_cast hcount
    exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hcountR) (hw n hn)
  have hsum := Finset.sum_nonpos hterm
  rw [← excess_eq_sum] at hsum
  exact (not_lt_of_ge hsum) hpos

theorem exists_distinct_prime_coordinates_of_two_le
    {c : BoundedGaps.engelsmaTuple → ℕ} {n : ℕ} (h : 2 ≤ primeCount c n) :
    ∃ i j : BoundedGaps.engelsmaTuple, i ≠ j ∧ (c i * n - 1).Prime ∧ (c j * n - 1).Prime := by
  classical
  let P := Finset.univ.filter fun i : BoundedGaps.engelsmaTuple ↦ (c i * n - 1).Prime
  have hcard : 2 ≤ P.card := h
  obtain ⟨i, hiP⟩ := Finset.card_pos.mp (lt_of_lt_of_le (by omega) hcard)
  have hremove : 0 < (P.erase i).card := by
    rw [Finset.card_erase_of_mem hiP]
    omega
  obtain ⟨j, hjP⟩ := Finset.card_pos.mp hremove
  have hjP' : j ∈ P := (Finset.mem_erase.mp hjP).2
  refine ⟨i, j, ?_, ?_, ?_⟩
  · exact fun hij ↦ (Finset.mem_erase.mp hjP).1 hij.symm
  · exact (Finset.mem_filter.mp hiP).2
  · exact (Finset.mem_filter.mp hjP').2

/-- Positive affine sieve excess at arbitrarily large scales gives the exact
prime-pair conclusion used by Pollack. -/
theorem affinePrimePair_of_eventually_positive
    {c : BoundedGaps.engelsmaTuple → ℕ}
    (hpos : ∃ N₀ : ℕ, ∀ N ≥ N₀, ∃ w : ℕ → ℝ,
      (∀ n ∈ Finset.Ico N (2 * N), 0 ≤ w n) ∧ 0 < excess c N w) :
    ∀ B : ℕ, ∃ n : ℕ, ∃ i j : BoundedGaps.engelsmaTuple,
      B < n ∧ i ≠ j ∧
      (c i * n - 1).Prime ∧ (c j * n - 1).Prime := by
  obtain ⟨N₀, hN₀⟩ := hpos
  intro B
  let N := max N₀ (B + 1)
  obtain ⟨w, hw, hexcess⟩ := hN₀ N (le_max_left _ _)
  obtain ⟨n, hn, htwo⟩ := exists_two_primes_of_excess_pos hw hexcess
  obtain ⟨i, j, hij, hpi, hpj⟩ :=
    exists_distinct_prime_coordinates_of_two_le htwo
  refine ⟨n, i, j, ?_, hij, hpi, hpj⟩
  have hNn := (Finset.mem_Ico.mp hn).1
  have hBN : B + 1 ≤ N := le_max_right _ _
  omega

/-! ## The concrete Engelsma weight: coverage and the first moment -/

def coefficientCoverageBound (c : BoundedGaps.engelsmaTuple → ℕ) : ℕ :=
  (∑ i : BoundedGaps.engelsmaTuple, c i) +
    ∑ i : BoundedGaps.engelsmaTuple,
      ∑ j : BoundedGaps.engelsmaTuple, Nat.dist (c i) (c j)

theorem coefficient_le_coverageBound
    (c : BoundedGaps.engelsmaTuple → ℕ) (i : BoundedGaps.engelsmaTuple) :
    c i ≤ coefficientCoverageBound c := by
  unfold coefficientCoverageBound
  exact (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)).trans
    (Nat.le_add_right _ _)

theorem coefficient_dist_le_coverageBound
    (c : BoundedGaps.engelsmaTuple → ℕ) (i j : BoundedGaps.engelsmaTuple) :
    Nat.dist (c i) (c j) ≤ coefficientCoverageBound c := by
  unfold coefficientCoverageBound
  apply le_add_of_le_right
  have hinner : Nat.dist (c i) (c j) ≤
      ∑ k ∈ (Finset.univ : Finset BoundedGaps.engelsmaTuple), Nat.dist (c i) (c k) := by
    exact Finset.single_le_sum
      (s := (Finset.univ : Finset BoundedGaps.engelsmaTuple))
      (f := fun k : BoundedGaps.engelsmaTuple ↦ Nat.dist (c i) (c k))
      (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ j)
  have houter : (∑ k ∈ (Finset.univ : Finset BoundedGaps.engelsmaTuple),
      Nat.dist (c i) (c k)) ≤
      ∑ a ∈ (Finset.univ : Finset BoundedGaps.engelsmaTuple),
        ∑ k ∈ (Finset.univ : Finset BoundedGaps.engelsmaTuple), Nat.dist (c a) (c k) := by
    exact Finset.single_le_sum
      (s := (Finset.univ : Finset BoundedGaps.engelsmaTuple))
      (f := fun a : BoundedGaps.engelsmaTuple ↦
        ∑ k ∈ (Finset.univ : Finset BoundedGaps.engelsmaTuple), Nat.dist (c a) (c k))
      (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
  calc
    Nat.dist (c i) (c j) ≤
        ∑ k ∈ (Finset.univ : Finset BoundedGaps.engelsmaTuple), Nat.dist (c i) (c k) := hinner
    _ ≤ ∑ a ∈ (Finset.univ : Finset BoundedGaps.engelsmaTuple),
        ∑ k ∈ (Finset.univ : Finset BoundedGaps.engelsmaTuple), Nat.dist (c a) (c k) := houter
    _ = ∑ a : BoundedGaps.engelsmaTuple,
        ∑ k : BoundedGaps.engelsmaTuple, Nat.dist (c a) (c k) := by
      rfl

theorem coefficient_coverages_of_cutoff
    {c : BoundedGaps.engelsmaTuple → ℕ} (hc : ∀ i, 0 < c i) (hinj : Function.Injective c)
    {D : ℕ} (hD : coefficientCoverageBound c ≤ D) :
    CoefficientPrimesCovered c (primorial D) ∧
      CoefficientDifferencesCovered c (primorial D) := by
  constructor
  · intro i p hp hpc
    apply hp.dvd_primorial_iff.mpr
    exact (Nat.le_of_dvd (hc i) hpc).trans
      ((coefficient_le_coverageBound c i).trans hD)
  · intro i j hij p hp hpdist
    apply hp.dvd_primorial_iff.mpr
    have hdist : 0 < Nat.dist (c i) (c j) :=
      Nat.dist_pos_of_ne (fun h ↦ hij (hinj h))
    exact (Nat.le_of_dvd hdist hpdist).trans
      ((coefficient_dist_le_coverageBound c i j).trans hD)

theorem eventually_coefficient_coverages
    {c : BoundedGaps.engelsmaTuple → ℕ} (hc : ∀ i, 0 < c i) (hinj : Function.Injective c) :
    ∀ᶠ N : ℕ in atTop,
      CoefficientPrimesCovered c
          (BoundedGaps.Maynard.engelsmaMaynardModulus N) ∧
        CoefficientDifferencesCovered c
          (BoundedGaps.Maynard.engelsmaMaynardModulus N) := by
  obtain ⟨M, hM⟩ := BoundedGaps.Maynard.exists_tripleLogCutoff_ge
    (coefficientCoverageBound c)
  filter_upwards [eventually_ge_atTop (M + 1)] with N hN
  unfold BoundedGaps.Maynard.engelsmaMaynardModulus
  exact coefficient_coverages_of_cutoff hc hinj (hM (N - 1) (by omega))

def affineMaynardSupport (alpha : ℝ) (N : ℕ) : Finset (BoundedGaps.engelsmaTuple → ℕ) :=
  BoundedGaps.Maynard.maynardSupportFamily BoundedGaps.engelsmaTuple
    (BoundedGaps.Maynard.engelsmaMaynardRadius alpha)
    BoundedGaps.Maynard.engelsmaMaynardModulus N

def affineMaynardCoefficient (alpha : ℝ) (N : ℕ) :
    (BoundedGaps.engelsmaTuple → ℕ) → ℝ :=
  BoundedGaps.Maynard.maynardCoefficientFamily BoundedGaps.engelsmaTuple
    (BoundedGaps.Maynard.engelsmaMaynardRadius alpha)
    BoundedGaps.Maynard.engelsmaMaynardModulus
    BoundedGaps.Maynard.engelsmaSmallKCandidate N

def affineMaynardWeight (c : BoundedGaps.engelsmaTuple → ℕ) (alpha : ℝ) (N : ℕ) : ℕ → ℝ :=
  preSievedWeight c (affineMaynardSupport alpha N)
    (affineMaynardCoefficient alpha N)
    (BoundedGaps.Maynard.engelsmaMaynardModulus N)

def affineMaynardS1Error (c : BoundedGaps.engelsmaTuple → ℕ) (alpha : ℝ) (N : ℕ) : ℝ :=
  compatiblePairErrorSum c (affineMaynardSupport alpha N)
    (BoundedGaps.Maynard.engelsmaMaynardModulus N) N
    (affineMaynardCoefficient alpha N)

theorem eventually_affineMaynardS1_eq_main_add_error
    {c : BoundedGaps.engelsmaTuple → ℕ} (hc : ∀ i, 0 < c i) (hinj : Function.Injective c)
    (alpha : ℝ) :
    ∀ᶠ N : ℕ in atTop,
      BoundedGaps.Maynard.sieveWeightSum N (affineMaynardWeight c alpha N) =
        BoundedGaps.Maynard.engelsmaMaynardS1Main alpha N +
          affineMaynardS1Error c alpha N := by
  filter_upwards [eventually_coefficient_coverages hc hinj] with N hcover
  have hD := BoundedGaps.Maynard.engelsmaMaynardS2SupportProof alpha N
  unfold affineMaynardWeight affineMaynardS1Error
  unfold affineMaynardSupport affineMaynardCoefficient
  rw [sieveWeightSum_eq_main_add_error hD hcover.2]
  rw [BoundedGaps.Maynard.compatibleDivisorPairMainSum_eq_auxiliaryMobiusSum hD]
  unfold BoundedGaps.Maynard.engelsmaMaynardS1Main
  rfl

set_option linter.constructorNameAsVariable false in
theorem abs_affineMaynardS1Error_le_explicit_envelope
    {c : BoundedGaps.engelsmaTuple → ℕ} {alpha : ℝ} (N : ℕ)
    (hcover : CoefficientPrimesCovered c
      (BoundedGaps.Maynard.engelsmaMaynardModulus N)) :
    |affineMaynardS1Error c alpha N| ≤
      ((BoundedGaps.Maynard.engelsmaMaynardRadius alpha N : ℝ) *
        (1 + Real.log (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)) ^
          Fintype.card BoundedGaps.engelsmaTuple) ^ 2 *
      ((BoundedGaps.Maynard.engelsmaMaynardRadius alpha N : ℝ) *
        BoundedGaps.Maynard.smallKCandidateBound *
        (1 + Real.log (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)) ^
          (2 * Fintype.card BoundedGaps.engelsmaTuple)) ^ 2 := by
  classical
  let lambda := affineMaynardCoefficient alpha N
  let L : ℝ :=
    (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N : ℝ) *
      BoundedGaps.Maynard.smallKCandidateBound *
      (1 + Real.log (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)) ^
        (2 * Fintype.card BoundedGaps.engelsmaTuple)
  have hD : ∀ d ∈ BoundedGaps.Maynard.maynardDivisorTupleSupport
      BoundedGaps.engelsmaTuple
      (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
      (BoundedGaps.Maynard.engelsmaMaynardModulus N),
      BoundedGaps.Maynard.IsMaynardDivisorTuple BoundedGaps.engelsmaTuple
        (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
        (BoundedGaps.Maynard.engelsmaMaynardModulus N) d := by
    intro d hd
    rw [BoundedGaps.Maynard.mem_maynardDivisorTupleSupport_iff] at hd
    unfold BoundedGaps.Maynard.IsMaynardDivisorTuple
    exact ⟨hd.2.1, hd.2.2.1, hd.2.2.2⟩
  have hL : 0 ≤ L := by
    dsimp [L]
    have hbase : 0 ≤ 1 +
        Real.log (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N) := by
      by_cases hzero : BoundedGaps.Maynard.engelsmaMaynardRadius alpha N = 0
      · simp [hzero]
      · have hone : (1 : ℝ) ≤
            BoundedGaps.Maynard.engelsmaMaynardRadius alpha N := by
          exact_mod_cast Nat.one_le_iff_ne_zero.mpr hzero
        linarith [Real.log_nonneg hone]
    exact mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _)
        BoundedGaps.Maynard.smallKCandidateBound_nonneg)
      (pow_nonneg hbase _)
  have hcoeff : ∀ d ∈ BoundedGaps.Maynard.maynardDivisorTupleSupport
      BoundedGaps.engelsmaTuple
      (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
      (BoundedGaps.Maynard.engelsmaMaynardModulus N),
      |lambda d| ≤ L := by
    intro d hd
    change |BoundedGaps.Maynard.maynardCoefficient
      BoundedGaps.engelsmaTuple
      (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
      (BoundedGaps.Maynard.engelsmaMaynardModulus N)
      BoundedGaps.Maynard.engelsmaSmallKCandidate d| ≤
        (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N : ℝ) *
          BoundedGaps.Maynard.smallKCandidateBound *
          (1 + Real.log
            (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)) ^
            (2 * Fintype.card BoundedGaps.engelsmaTuple)
    have hcandidate : ∀ x : BoundedGaps.engelsmaTuple → ℝ,
        |BoundedGaps.Maynard.engelsmaSmallKCandidate x| ≤
          BoundedGaps.Maynard.smallKCandidateBound := by
      intro x
      unfold BoundedGaps.Maynard.engelsmaSmallKCandidate
      simpa only [Real.norm_eq_abs] using
        BoundedGaps.Maynard.smallKCandidate_norm_le
          (fun i ↦ x (BoundedGaps.Maynard.engelsmaIndexEquiv.symm i))
    apply BoundedGaps.Maynard.abs_maynardCoefficient_le_log_envelope
      BoundedGaps.engelsmaTuple
      (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
      (BoundedGaps.Maynard.engelsmaMaynardModulus N)
      BoundedGaps.Maynard.engelsmaSmallKCandidate d
      BoundedGaps.Maynard.smallKCandidateBound
      BoundedGaps.Maynard.smallKCandidateBound_nonneg
    · exact hcandidate
    · rw [BoundedGaps.Maynard.mem_maynardDivisorTupleSupport_iff] at hd ⊢
      refine ⟨?_, hd.2.1, hd.2.2⟩
      rw [BoundedGaps.Maynard.mem_maynardDivisorTupleBox_iff] at hd ⊢
      intro i
      exact ⟨(hd.1 i).1, (hd.1 i).2⟩
  have herr := abs_compatiblePairErrorSum_le_coefficientMass
    (c := c)
    (D := BoundedGaps.Maynard.maynardDivisorTupleSupport
      BoundedGaps.engelsmaTuple
      (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
      (BoundedGaps.Maynard.engelsmaMaynardModulus N))
    (coeff := lambda)
    (R := BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
    hcover (primorial_pos _) hD (N := N)
  have hmass :=
    BoundedGaps.Maynard.compatibleDivisorPairCoefficientMass_le_card_sq_mul
      (D := BoundedGaps.Maynard.maynardDivisorTupleSupport
        BoundedGaps.engelsmaTuple
        (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
        (BoundedGaps.Maynard.engelsmaMaynardModulus N))
      (lambda := lambda) hL hcoeff
  have hcard := BoundedGaps.Maynard.maynardDivisorTupleSupport_card_le_log
    BoundedGaps.engelsmaTuple
    (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
    (BoundedGaps.Maynard.engelsmaMaynardModulus N)
  have hcardpow := pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 2
  unfold affineMaynardS1Error affineMaynardSupport affineMaynardCoefficient
  exact herr.trans (hmass.trans
    (mul_le_mul_of_nonneg_right hcardpow (sq_nonneg L)))

theorem tendsto_affineMaynardS1Error_div_scale
    {c : BoundedGaps.engelsmaTuple → ℕ} (hc : ∀ i, 0 < c i) (hinj : Function.Injective c)
    {alpha : ℝ} (halpha : 0 < alpha) (halphaQuarter : alpha < 1 / 4) :
    Tendsto (fun N : ℕ ↦ affineMaynardS1Error c alpha N /
      BoundedGaps.Maynard.engelsmaMaynardScale alpha N) atTop (nhds 0) := by
  have henv := BoundedGaps.Maynard.tendsto_engelsmaMaynardS1ExplicitEnvelope
    halpha halphaQuarter
  have hscale := BoundedGaps.Maynard.eventually_engelsmaMaynardScale_pos halpha
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ abs_nonneg _) ?_ henv
  filter_upwards [eventually_coefficient_coverages hc hinj, hscale] with
      N hcover hscaleN
  rw [abs_div, abs_of_pos hscaleN]
  have herror := abs_affineMaynardS1Error_le_explicit_envelope
    (c := c) (alpha := alpha) N hcover.1
  exact div_le_div_of_nonneg_right
    herror hscaleN.le

theorem tendsto_affineMaynardS1_div_scale
    {c : BoundedGaps.engelsmaTuple → ℕ} (hc : ∀ i, 0 < c i) (hinj : Function.Injective c)
    {alpha : ℝ} (halpha : 0 < alpha) (halphaQuarter : alpha < 1 / 4) :
    Tendsto (fun N : ℕ ↦
      BoundedGaps.Maynard.sieveWeightSum N (affineMaynardWeight c alpha N) /
        BoundedGaps.Maynard.engelsmaMaynardScale alpha N)
      atTop (nhds (BoundedGaps.Maynard.maynardI 105
        BoundedGaps.Maynard.smallKCandidate)) := by
  have hmain := BoundedGaps.Maynard.tendsto_engelsmaMaynardS1Main halpha
  have herr := tendsto_affineMaynardS1Error_div_scale hc hinj halpha halphaQuarter
  have hsum := hmain.add herr
  have hsum' : Tendsto
      (fun N : ℕ ↦
        BoundedGaps.Maynard.engelsmaMaynardS1Main alpha N /
            BoundedGaps.Maynard.engelsmaMaynardScale alpha N +
          affineMaynardS1Error c alpha N /
            BoundedGaps.Maynard.engelsmaMaynardScale alpha N)
      atTop (nhds (BoundedGaps.Maynard.maynardI 105
        BoundedGaps.Maynard.smallKCandidate)) := by
    simpa only [add_zero] using hsum
  apply hsum'.congr'
  filter_upwards [eventually_affineMaynardS1_eq_main_add_error hc hinj alpha] with
      N hN
  rw [hN]
  ring

/-! ## Affine prime progressions -/

theorem totient_mul_eq_mul_totient_of_prime_divisors
    {a q : ℕ} (ha : 0 < a)
    (hdiv : ∀ p, p.Prime → p ∣ a → p ∣ q) :
    Nat.totient (a * q) = a * Nat.totient q := by
  let P : ℕ → Prop := fun b ↦ 0 < b →
    (∀ p, p.Prime → p ∣ b → p ∣ q) →
      Nat.totient (b * q) = b * Nat.totient q
  have hP : ∀ b, P b := by
    apply induction_on_primes
    · intro hzero
      omega
    · intro _
      simp
    · intro p b hp hb hpb hprimes
      have hbpos : 0 < b := pos_of_mul_pos_right hpb (Nat.zero_le p)
      have hpq : p ∣ q := hprimes p hp (dvd_mul_right p b)
      have hbdiv : ∀ r, r.Prime → r ∣ b → r ∣ q := by
        intro r hr hrb
        exact hprimes r hr (dvd_mul_of_dvd_right hrb p)
      rw [mul_assoc, Nat.totient_mul_of_prime_of_dvd hp
        (dvd_mul_of_dvd_right hpq b)]
      rw [hb hbpos hbdiv]
      ring
  exact hP a ha hdiv

theorem totient_coefficient_mul_divisorPairModulus
    {c : BoundedGaps.engelsmaTuple → ℕ} {W : ℕ}
    (hcover : CoefficientPrimesCovered c W) (i : BoundedGaps.engelsmaTuple)
    (d e : BoundedGaps.engelsmaTuple → ℕ) (hc : 0 < c i) :
    Nat.totient (c i *
      BoundedGaps.Maynard.divisorPairModulus BoundedGaps.engelsmaTuple W d e) =
      c i * Nat.totient
        (BoundedGaps.Maynard.divisorPairModulus BoundedGaps.engelsmaTuple W d e) := by
  apply totient_mul_eq_mul_totient_of_prime_divisors hc
  intro p hp hpc
  have hpW := hcover i p hp hpc
  exact dvd_mul_of_dvd_left hpW _

def affinePrimeProgressionCount (a N q r : ℕ) : ℕ :=
  ((Finset.Ico N (2 * N)).filter fun n ↦
    n ≡ r [MOD q] ∧ (a * n - 1).Prime).card

def affinePrimeIntervalCount (a N : ℕ) : ℝ :=
  (BoundedGaps.Maynard.primeCountTotal (a * (2 * N) - 2) : ℝ) -
    (BoundedGaps.Maynard.primeCountTotal (a * N - 2) : ℝ)

def affinePrimeProgressionMainTerm (a N q : ℕ) : ℝ :=
  affinePrimeIntervalCount a N / (Nat.totient (a * q) : ℝ)

def affinePrimeProgressionError (a N q r : ℕ) : ℝ :=
  (affinePrimeProgressionCount a N q r : ℝ) -
    affinePrimeProgressionMainTerm a N q

theorem affinePrimeProgressionCount_decomposition (a N q r : ℕ) :
    (affinePrimeProgressionCount a N q r : ℝ) =
      affinePrimeProgressionMainTerm a N q +
        affinePrimeProgressionError a N q r := by
  unfold affinePrimeProgressionError
  ring

theorem affinePrimeProgressionMainTerm_eq
    {c : BoundedGaps.engelsmaTuple → ℕ} {W N : ℕ}
    (hcover : CoefficientPrimesCovered c W) (i : BoundedGaps.engelsmaTuple)
    (d e : BoundedGaps.engelsmaTuple → ℕ) (hc : 0 < c i) :
    affinePrimeProgressionMainTerm (c i) N
        (BoundedGaps.Maynard.divisorPairModulus
          BoundedGaps.engelsmaTuple W d e) =
      (affinePrimeIntervalCount (c i) N / c i) /
        (Nat.totient (BoundedGaps.Maynard.divisorPairModulus
          BoundedGaps.engelsmaTuple W d e) : ℝ) := by
  unfold affinePrimeProgressionMainTerm
  rw [totient_coefficient_mul_divisorPairModulus hcover i d e hc]
  rw [Nat.cast_mul]
  exact (div_div _ _ _).symm

end AffineSieve

end

end Erdos823
