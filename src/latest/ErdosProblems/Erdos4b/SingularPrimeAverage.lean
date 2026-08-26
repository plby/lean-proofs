/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralSingularPenalty
import BoundedGaps.Maynard.Distribution
import BoundedGaps.Maynard.MaynardSquarefreeRoughTail

/-!
# Prime averages of the affine singular-factor losses

This file identifies every off-diagonal affine collision with one reduced
prime-progression class.  It is the arithmetic bridge needed to average the
Bonferroni loss from `GeneralSingularPenalty` over the auxiliary prime.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

noncomputable local instance singularPrimeAverageDecidable
    (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-- The reduced residue occupied by an affine collision.  The coefficient is
packaged as a unit so the definition also works before installing the field
instance supplied by primality. -/
noncomputable def crossAffinePrimeResidue
    {H : Finset ℕ} (m p : ℕ) (ba : H × H)
    (hc : IsUnit ((m : ZMod p) *
      ((ba.1.1 : ZMod p) - ba.2.1))) : ℕ :=
  (((hc.unit)⁻¹ : (ZMod p)ˣ) : ZMod p).val

theorem crossAffinePrimeResidue_coprime
    {H : Finset ℕ} {m p : ℕ} {ba : H × H}
    (hc : IsUnit ((m : ZMod p) *
      ((ba.1.1 : ZMod p) - ba.2.1))) :
    (crossAffinePrimeResidue m p ba hc).Coprime p := by
  unfold crossAffinePrimeResidue
  exact ZMod.val_coe_unit_coprime _

theorem crossAffinePrimeResidue_lt
    {H : Finset ℕ} {m p : ℕ} {ba : H × H} (hp0 : 0 < p)
    (hc : IsUnit ((m : ZMod p) *
      ((ba.1.1 : ZMod p) - ba.2.1))) :
    crossAffinePrimeResidue m p ba hc < p := by
  letI : NeZero p := ⟨hp0.ne'⟩
  unfold crossAffinePrimeResidue
  exact ZMod.val_lt _

theorem crossAffinePrimeResidue_mem_coprimeResidues
    {H : Finset ℕ} {m p : ℕ} {ba : H × H} (hp0 : 0 < p)
    (hc : IsUnit ((m : ZMod p) *
      ((ba.1.1 : ZMod p) - ba.2.1))) :
    crossAffinePrimeResidue m p ba hc ∈
      BoundedGaps.Maynard.coprimeResidues p := by
  rw [BoundedGaps.Maynard.coprimeResidues, Finset.mem_filter,
    Finset.mem_range]
  exact ⟨crossAffinePrimeResidue_lt hp0 hc,
    crossAffinePrimeResidue_coprime hc⟩

/-- Divisibility of one signed affine difference is exactly one congruence
class for the auxiliary variable. -/
theorem prime_dvd_crossAffineDifference_iff_modEq
    {H : Finset ℕ} {m q p : ℕ} {ba : H × H}
    (hp : p.Prime)
    (hc : IsUnit ((m : ZMod p) *
      ((ba.1.1 : ZMod p) - ba.2.1))) :
    (p : ℤ) ∣ crossAffineDifference m q ba ↔
      q ≡ crossAffinePrimeResidue m p ba hc [MOD p] := by
  letI : Fact p.Prime := ⟨hp⟩
  let c : ZMod p := (m : ZMod p) * ((ba.1.1 : ZMod p) - ba.2.1)
  let u : (ZMod p)ˣ := hc.unit
  let a := crossAffinePrimeResidue m p ba hc
  have ha : (a : ZMod p) = ((u⁻¹ : (ZMod p)ˣ) : ZMod p) := by
    dsimp [a, u, crossAffinePrimeResidue]
    exact ZMod.natCast_zmod_val _
  have hcast : (crossAffineDifference m q ba : ZMod p) = c * q - 1 := by
    unfold crossAffineDifference
    rw [Int.cast_sub]
    push_cast
    dsimp [c]
    ring
  constructor
  · intro hdiv
    have hzero : (crossAffineDifference m q ba : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hdiv
    rw [hcast] at hzero
    have hcq : c * (q : ZMod p) = 1 := sub_eq_zero.mp hzero
    have hq : (q : ZMod p) =
        ((u⁻¹ : (ZMod p)ˣ) : ZMod p) := by
      have hunit : (u : ZMod p) * (q : ZMod p) = 1 := by
        simpa [u, c, IsUnit.unit_spec] using hcq
      exact Units.eq_inv_of_mul_eq_one_left hunit
    apply (ZMod.natCast_eq_natCast_iff q a p).mp
    rw [ha]
    exact hq
  · intro hmod
    have hq : (q : ZMod p) = (a : ZMod p) :=
      (ZMod.natCast_eq_natCast_iff q a p).2 hmod
    have hzero : (crossAffineDifference m q ba : ZMod p) = 0 := by
      rw [hcast, hq, ha]
      change (u : ZMod p) *
          ((u⁻¹ : (ZMod p)ˣ) : ZMod p) - 1 = 0
      apply sub_eq_zero.mpr
      exact u.mul_inv
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hzero

/-- Above the pre-sieve cutoff, distinct pre-sieved shifts give a nonzero
affine coefficient at every prime not dividing the residual cofactor. -/
theorem preSieved_crossAffineCoefficient_isUnit
    {K w m p : ℕ} (hp : p.Prime) (hKw : K ≤ w) (hwp : w < p)
    (hpm : ¬p ∣ m) {ba : ↥(preSievedShifts K w) ×
      ↥(preSievedShifts K w)} (hba : ba.1 ≠ ba.2) :
    IsUnit ((m : ZMod p) * ((ba.1.1 : ZMod p) - ba.2.1)) := by
  letI : Fact p.Prime := ⟨hp⟩
  rw [isUnit_iff_ne_zero]
  apply mul_ne_zero
  · intro hm
    exact hpm ((ZMod.natCast_eq_zero_iff m p).mp hm)
  · rw [sub_ne_zero]
    intro heq
    apply hba
    apply preSievedFirstResidueMap_injOn hp hKw hwp hp.not_dvd_one
      (Set.mem_univ ba.1) (Set.mem_univ ba.2)
    simpa using congrArg Neg.neg heq

theorem prime_dvd_preSieved_crossAffineDifference_iff_modEq
    {K w m q p : ℕ} (hp : p.Prime) (hKw : K ≤ w) (hwp : w < p)
    (hpm : ¬p ∣ m) {ba : ↥(preSievedShifts K w) ×
      ↥(preSievedShifts K w)} (hba : ba.1 ≠ ba.2) :
    (p : ℤ) ∣ crossAffineDifference m q ba ↔
      q ≡ crossAffinePrimeResidue m p ba
        (preSieved_crossAffineCoefficient_isUnit hp hKw hwp hpm hba)
          [MOD p] := by
  exact prime_dvd_crossAffineDifference_iff_modEq hp _

/-- Auxiliary primes in an interval causing one specified affine collision.
-/
def affineCollisionAuxiliaryPrimes
    {H : Finset ℕ} (A B m p : ℕ) (ba : H × H) : Finset ℕ :=
  (auxiliaryPrimeInterval A B).filter fun q ↦
    (p : ℤ) ∣ crossAffineDifference m q ba

theorem card_affineCollisionAuxiliaryPrimes_eq_progressionCount
    {K w A B m p : ℕ} (hp : p.Prime) (hKw : K ≤ w)
    (hwp : w < p) (hpm : ¬p ∣ m)
    {ba : ↥(preSievedShifts K w) × ↥(preSievedShifts K w)}
    (hba : ba.1 ≠ ba.2) :
    (affineCollisionAuxiliaryPrimes A B m p ba).card =
      BoundedGaps.Maynard.primeVariableProgressionCount A B p
        (crossAffinePrimeResidue m p ba
          (preSieved_crossAffineCoefficient_isUnit hp hKw hwp hpm hba)) := by
  classical
  unfold affineCollisionAuxiliaryPrimes auxiliaryPrimeInterval
    BoundedGaps.Maynard.primeVariableProgressionCount
  congr 1
  ext q
  simp only [Finset.mem_filter, Finset.mem_Ico]
  rw [prime_dvd_preSieved_crossAffineDifference_iff_modEq
    hp hKw hwp hpm hba]
  tauto

/-- One affine-collision count is bounded by its prime-progression main
term and the two endpoint discrepancies. -/
theorem cast_card_affineCollisionAuxiliaryPrimes_le
    {K w A B m p : ℕ} (hp : p.Prime) (hKw : K ≤ w)
    (hwp : w < p) (hpm : ¬p ∣ m)
    (hA : 0 < A) (hAB : A ≤ B)
    {ba : ↥(preSievedShifts K w) × ↥(preSievedShifts K w)}
    (hba : ba.1 ≠ ba.2) :
    ((affineCollisionAuxiliaryPrimes A B m p ba).card : ℝ) ≤
      (((auxiliaryPrimeInterval A B).card : ℝ) /
          (Nat.totient p : ℝ)) +
        BoundedGaps.Maynard.progressionDiscrepancy (B - 1) p
          (crossAffinePrimeResidue m p ba
            (preSieved_crossAffineCoefficient_isUnit hp hKw hwp hpm hba)) +
        BoundedGaps.Maynard.progressionDiscrepancy (A - 1) p
          (crossAffinePrimeResidue m p ba
            (preSieved_crossAffineCoefficient_isUnit hp hKw hwp hpm hba)) := by
  let r := crossAffinePrimeResidue m p ba
    (preSieved_crossAffineCoefficient_isUnit hp hKw hwp hpm hba)
  have hcount :=
    BoundedGaps.Maynard.primeVariableProgressionCount_intervalDiscrepancy_le_global_sum
      (q := p) (r := r) hA hAB
  rw [← card_affineCollisionAuxiliaryPrimes_eq_progressionCount
    hp hKw hwp hpm hba] at hcount
  rw [cast_auxiliaryPrimeInterval_card hA hAB]
  have hself := le_abs_self
    (((affineCollisionAuxiliaryPrimes A B m p ba).card : ℝ) -
      (((BoundedGaps.Maynard.primeCountTotal (B - 1) : ℕ) : ℝ) -
        ((BoundedGaps.Maynard.primeCountTotal (A - 1) : ℕ) : ℝ)) /
          (Nat.totient p : ℝ))
  dsimp [r] at hcount ⊢
  linarith

/-- Away from the fixed cofactor and the auxiliary prime itself, a local
inverse-factor loss is charged to an off-diagonal affine collision. -/
theorem largeGapLocalPenalty_le_offDiagonal_affine_sum
    {K w m q p : ℕ} (hfour : 4 * K ≤ w) (hp : p.Prime)
    (hwp : w < p) (hpm : ¬p ∣ m) (hpq : ¬p ∣ q) :
    largeGapLocalPenalty (preSievedShifts K w) m q p ≤
      ∑ ba ∈ BoundedGaps.Maynard.offDiagonalPairs
          (preSievedShifts K w),
        if (p : ℤ) ∣ crossAffineDifference m q ba then
          ((4 * K : ℕ) : ℝ) / p
        else 0 := by
  have hKw : K ≤ w := by omega
  have htwo : 2 * (preSievedShifts K w).card < p := by
    rw [card_preSievedShifts]
    omega
  by_cases hloss :
      largeGapLocalPenalty (preSievedShifts K w) m q p = 0
  · rw [hloss]
    apply Finset.sum_nonneg
    intro ba hba
    split_ifs
    · positivity
    · exact le_rfl
  · have homegaNe :
        largeGapLocalMultiplicity (preSievedShifts K w) m q p ≠
          2 * K := by
      intro homega
      apply hloss
      rw [largeGapLocalPenalty_eq_zero_iff
        (preSievedShifts K w) m q p htwo,
        card_preSievedShifts]
      exact homega
    have homegaLt :
        largeGapLocalMultiplicity (preSievedShifts K w) m q p <
          2 * K := by
      have hle := largeGapLocalMultiplicity_le_two_mul_card
        (preSievedShifts K w) m q p
      rw [card_preSievedShifts] at hle
      omega
    obtain ⟨hb, ha, hdiv⟩ :=
      exists_crossAffineDifference_of_localMultiplicity_lt
        hp hKw hwp hpq hpm homegaLt
    have hne : hb ≠ ha := by
      intro heq
      have hpAbs : p ∣
          (crossAffineDifference m q (hb, ha)).natAbs :=
        Int.natCast_dvd.mp hdiv
      have hpOne : p ∣ 1 := by
        simpa [heq, crossAffineDifference] using hpAbs
      exact hp.not_dvd_one hpOne
    have hmem : (hb, ha) ∈
        BoundedGaps.Maynard.offDiagonalPairs
          (preSievedShifts K w) := by
      rw [BoundedGaps.Maynard.offDiagonalPairs, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hne⟩
    have hterm : ((4 * K : ℕ) : ℝ) / p ≤
        ∑ ba ∈ BoundedGaps.Maynard.offDiagonalPairs
            (preSievedShifts K w),
          if (p : ℤ) ∣ crossAffineDifference m q ba then
            ((4 * K : ℕ) : ℝ) / p
          else 0 := by
      calc
        ((4 * K : ℕ) : ℝ) / p =
            if (p : ℤ) ∣ crossAffineDifference m q (hb, ha) then
              ((4 * K : ℕ) : ℝ) / p
            else 0 := by simp [hdiv]
        _ ≤ _ := Finset.single_le_sum
          (s := BoundedGaps.Maynard.offDiagonalPairs
            (preSievedShifts K w))
          (a := (hb, ha))
          (f := fun ba ↦
            if (p : ℤ) ∣ crossAffineDifference m q ba then
              ((4 * K : ℕ) : ℝ) / p
            else 0)
          (fun ba hba ↦ by split_ifs <;> positivity) hmem
    have hfourp : 4 * (preSievedShifts K w).card ≤ p := by
      rw [card_preSievedShifts]
      exact hfour.trans hwp.le
    have hpen := largeGapLocalPenalty_le_four_mul_card_div
      (H := preSievedShifts K w) (m := m) (q := q) (p := p)
      hp hfourp
    have hpen' :
        largeGapLocalPenalty (preSievedShifts K w) m q p ≤
          ((4 * K : ℕ) : ℝ) / p := by
      simpa only [card_preSievedShifts] using hpen
    exact hpen'.trans hterm

/-- Summing the pointwise charge over an auxiliary-prime interval turns the
collision indicators into exact progression counts. -/
theorem sum_largeGapLocalPenalty_auxiliaryPrimeInterval_le_affineCounts
    {K w A B m p : ℕ} (hfour : 4 * K ≤ w) (hp : p.Prime)
    (hwp : w < p) (hpm : ¬p ∣ m) (hpA : p < A) :
    (∑ q ∈ auxiliaryPrimeInterval A B,
        largeGapLocalPenalty (preSievedShifts K w) m q p) ≤
      ((4 * K : ℕ) : ℝ) / p *
        ∑ ba ∈ BoundedGaps.Maynard.offDiagonalPairs
            (preSievedShifts K w),
          ((affineCollisionAuxiliaryPrimes A B m p ba).card : ℝ) := by
  let Q := auxiliaryPrimeInterval A B
  let P := BoundedGaps.Maynard.offDiagonalPairs (preSievedShifts K w)
  have hpq : ∀ q ∈ Q, ¬p ∣ q := by
    intro q hq hpDiv
    have hqData := mem_auxiliaryPrimeInterval.mp hq
    rcases (Nat.dvd_prime hqData.2.2).mp hpDiv with hpOne | hpEq
    · exact hp.ne_one hpOne
    · omega
  calc
    (∑ q ∈ Q,
        largeGapLocalPenalty (preSievedShifts K w) m q p) ≤
        ∑ q ∈ Q, ∑ ba ∈ P,
          if (p : ℤ) ∣ crossAffineDifference m q ba then
            ((4 * K : ℕ) : ℝ) / p
          else 0 := by
      apply Finset.sum_le_sum
      intro q hq
      exact largeGapLocalPenalty_le_offDiagonal_affine_sum
        hfour hp hwp hpm (hpq q hq)
    _ = ∑ ba ∈ P, ∑ q ∈ Q,
          if (p : ℤ) ∣ crossAffineDifference m q ba then
            ((4 * K : ℕ) : ℝ) / p
          else 0 := Finset.sum_comm
    _ = ∑ ba ∈ P,
          ((4 * K : ℕ) : ℝ) / p *
            ((affineCollisionAuxiliaryPrimes A B m p ba).card : ℝ) := by
      apply Finset.sum_congr rfl
      intro ba hba
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul]
      unfold affineCollisionAuxiliaryPrimes
      change
        ((Q.filter fun q ↦
            (p : ℤ) ∣ crossAffineDifference m q ba).card : ℝ) *
              (((4 * K : ℕ) : ℝ) / p) =
          (((4 * K : ℕ) : ℝ) / p) *
            ((Q.filter fun q ↦
              (p : ℤ) ∣ crossAffineDifference m q ba).card : ℝ)
      ring
    _ = ((4 * K : ℕ) : ℝ) / p *
        ∑ ba ∈ P,
          ((affineCollisionAuxiliaryPrimes A B m p ba).card : ℝ) := by
      rw [Finset.mul_sum]

/-- The affine counts are bounded uniformly by the prime-progression main
term and maximal discrepancies. -/
theorem sum_largeGapLocalPenalty_auxiliaryPrimeInterval_le_maxDiscrepancy
    {K w A B m p : ℕ} (hfour : 4 * K ≤ w) (hp : p.Prime)
    (hwp : w < p) (hpm : ¬p ∣ m) (hpA : p < A)
    (hA : 0 < A) (hAB : A ≤ B) :
    (∑ q ∈ auxiliaryPrimeInterval A B,
        largeGapLocalPenalty (preSievedShifts K w) m q p) ≤
      ((4 * K : ℕ) : ℝ) / p *
        ((BoundedGaps.Maynard.offDiagonalPairs
          (preSievedShifts K w)).card : ℝ) *
          ((((auxiliaryPrimeInterval A B).card : ℝ) /
              (Nat.totient p : ℝ)) +
            BoundedGaps.Maynard.maxProgressionDiscrepancy (B - 1) p +
            BoundedGaps.Maynard.maxProgressionDiscrepancy (A - 1) p) := by
  let P := BoundedGaps.Maynard.offDiagonalPairs (preSievedShifts K w)
  let M : ℝ := ((auxiliaryPrimeInterval A B).card : ℝ) /
      (Nat.totient p : ℝ)
  let D : ℝ :=
    BoundedGaps.Maynard.maxProgressionDiscrepancy (B - 1) p +
      BoundedGaps.Maynard.maxProgressionDiscrepancy (A - 1) p
  have hfactor : 0 ≤ ((4 * K : ℕ) : ℝ) / p := by positivity
  have hcount : ∀ ba ∈ P,
      ((affineCollisionAuxiliaryPrimes A B m p ba).card : ℝ) ≤
        M + D := by
    intro ba hba
    have hne : ba.1 ≠ ba.2 :=
      (Finset.mem_filter.mp hba).2
    let hc := preSieved_crossAffineCoefficient_isUnit
      hp (show K ≤ w by omega) hwp hpm hne
    let r := crossAffinePrimeResidue m p ba hc
    have hraw := cast_card_affineCollisionAuxiliaryPrimes_le
      hp (show K ≤ w by omega) hwp hpm hA hAB hne
    have hrmem : r ∈ BoundedGaps.Maynard.coprimeResidues p := by
      exact crossAffinePrimeResidue_mem_coprimeResidues hp.pos hc
    have hB := BoundedGaps.Maynard.progressionDiscrepancy_le_max
      (x := B - 1) hp.pos hrmem
    have hA' := BoundedGaps.Maynard.progressionDiscrepancy_le_max
      (x := A - 1) hp.pos hrmem
    dsimp [M, D, r, hc] at hraw hB hA' ⊢
    linarith
  calc
    (∑ q ∈ auxiliaryPrimeInterval A B,
        largeGapLocalPenalty (preSievedShifts K w) m q p) ≤
        ((4 * K : ℕ) : ℝ) / p *
          ∑ ba ∈ P,
            ((affineCollisionAuxiliaryPrimes A B m p ba).card : ℝ) :=
      sum_largeGapLocalPenalty_auxiliaryPrimeInterval_le_affineCounts
        hfour hp hwp hpm hpA
    _ ≤ ((4 * K : ℕ) : ℝ) / p *
          ∑ _ba ∈ P, (M + D) := by
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum hcount) hfactor
    _ = ((4 * K : ℕ) : ℝ) / p * (P.card : ℝ) *
          (M + D) := by
      simp [nsmul_eq_mul]
      ring
    _ = _ := by
      simp only [P, M, D]
      ring

/-- Rough primes whose local factor actually varies with the auxiliary
prime.  Primes dividing the fixed cofactor are deliberately excluded: their
local factors are constant in the auxiliary prime and are factored out in
the normalization step. -/
def varyingSingularPrimeSupport (w y m : ℕ) : Finset ℕ :=
  (BoundedGaps.Maynard.roughPrimeSupport w y).filter fun p ↦ ¬p ∣ m

theorem mem_varyingSingularPrimeSupport
    {w y m p : ℕ} :
    p ∈ varyingSingularPrimeSupport w y m ↔
      w < p ∧ p ≤ y ∧ p.Prime ∧ ¬p ∣ m := by
  simp only [varyingSingularPrimeSupport,
    BoundedGaps.Maynard.roughPrimeSupport, Finset.mem_filter,
    Finset.mem_Icc]
  constructor
  · rintro ⟨⟨⟨hwp, hpy⟩, hp⟩, hpm⟩
    exact ⟨by omega, hpy, hp, hpm⟩
  · rintro ⟨hwp, hpy, hp, hpm⟩
    exact ⟨⟨⟨by omega, hpy⟩, hp⟩, hpm⟩

/-- The progression main-term weight is dominated by the reciprocal
totient-square weight already controlled by the rough Euler-product tail. -/
theorem one_div_prime_div_totient_le_primeTotientSquareWeight
    {p : ℕ} (hp : p.Prime) :
    (1 : ℝ) / p / Nat.totient p ≤
      BoundedGaps.Maynard.primeTotientSquareWeight p := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have htot : (0 : ℝ) < Nat.totient p := by
    exact_mod_cast (Nat.totient_pos.mpr hp.pos)
  have htotle : ((Nat.totient p : ℕ) : ℝ) ≤ p := by
    exact_mod_cast Nat.totient_le p
  unfold BoundedGaps.Maynard.primeTotientSquareWeight
  calc
    (1 : ℝ) / p / Nat.totient p =
        1 / ((p : ℝ) * Nat.totient p) := by ring
    _ ≤ 1 / (((Nat.totient p : ℕ) : ℝ) * Nat.totient p) := by
      apply one_div_le_one_div_of_le (mul_pos htot htot)
      exact mul_le_mul_of_nonneg_right htotle htot.le
    _ = 1 / ((Nat.totient p : ℝ) ^ 2) := by ring

/-- The total main-term weight of all varying rough singular primes is
`O(1 / w)`, uniformly in the upper cutoff and the fixed cofactor. -/
theorem sum_varyingSingularPrime_mainWeight_le
    {w y m : ℕ} (hw : 0 < w) :
    (∑ p ∈ varyingSingularPrimeSupport w y m,
        (1 : ℝ) / p / Nat.totient p) ≤ 8 / (w : ℝ) := by
  let S := varyingSingularPrimeSupport w y m
  let R := BoundedGaps.Maynard.roughPrimeSupport w y
  have hSR : S ⊆ R := by
    intro p hp
    exact (Finset.mem_filter.mp hp).1
  calc
    (∑ p ∈ S, (1 : ℝ) / p / Nat.totient p) ≤
        ∑ p ∈ S,
          BoundedGaps.Maynard.primeTotientSquareWeight p := by
      apply Finset.sum_le_sum
      intro p hp
      exact one_div_prime_div_totient_le_primeTotientSquareWeight
        (mem_varyingSingularPrimeSupport.mp hp).2.2.1
    _ ≤ ∑ p ∈ R,
          BoundedGaps.Maynard.primeTotientSquareWeight p := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hSR
      intro p hp hpS
      exact BoundedGaps.Maynard.primeTotientSquareWeight_nonneg p
    _ ≤ 8 / (w : ℝ) :=
      BoundedGaps.Maynard.roughPrimeWeightSum_le hw

/-- A prime-level witness controls the discrepancy sum even after insertion
of the extra reciprocal-prime weight. -/
theorem PrimeLevelWitness.sum_varyingSingularPrime_weightedDiscrepancy_le
    {theta exponent C : ℝ} {X₀ x w y m : ℕ}
    (hlevel : BoundedGaps.Maynard.PrimeLevelWitness
      theta exponent C X₀)
    (hw : 0 < w) (hx : X₀ ≤ x)
    (hy : y ≤ BoundedGaps.Maynard.modulusCutoff theta x) :
    (∑ p ∈ varyingSingularPrimeSupport w y m,
        BoundedGaps.Maynard.maxProgressionDiscrepancy x p / p) ≤
      (C * (x : ℝ) /
          Real.rpow (Real.log (x : ℝ)) exponent) / (w : ℝ) := by
  let S := varyingSingularPrimeSupport w y m
  have hS : S ⊆ Finset.Icc 1
      (BoundedGaps.Maynard.modulusCutoff theta x) := by
    intro p hp
    have hpData := mem_varyingSingularPrimeSupport.mp hp
    exact Finset.mem_Icc.mpr ⟨by omega, hpData.2.1.trans hy⟩
  have hBV := hlevel.sum_maxProgressionDiscrepancy_subset hx S hS
  calc
    (∑ p ∈ S,
        BoundedGaps.Maynard.maxProgressionDiscrepancy x p / p) ≤
        ∑ p ∈ S,
          BoundedGaps.Maynard.maxProgressionDiscrepancy x p / w := by
      apply Finset.sum_le_sum
      intro p hp
      have hpData := mem_varyingSingularPrimeSupport.mp hp
      apply (div_le_div_iff₀
        (by exact_mod_cast hpData.2.2.1.pos)
        (by exact_mod_cast hw)).mpr
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hpData.1.le)
        (BoundedGaps.Maynard.maxProgressionDiscrepancy_nonneg x p)
    _ = (∑ p ∈ S,
          BoundedGaps.Maynard.maxProgressionDiscrepancy x p) / w := by
      rw [Finset.sum_div]
    _ ≤ (C * (x : ℝ) /
          Real.rpow (Real.log (x : ℝ)) exponent) / (w : ℝ) := by
      exact div_le_div_of_nonneg_right hBV (by positivity)

/-- Complete averaged bound for every varying rough singular factor.  This
is the finite quantitative form of the extra `1 / p` gained by averaging an
affine collision over the auxiliary prime. -/
theorem sum_varyingSingularPrime_localPenalty_le_primeLevelWitness
    {theta exponent C : ℝ} {X₀ K w A B m y : ℕ}
    (hlevel : BoundedGaps.Maynard.PrimeLevelWitness
      theta exponent C X₀)
    (hfour : 4 * K ≤ w) (hw : 0 < w)
    (hyA : y < A) (hA : 0 < A) (hAB : A ≤ B)
    (hBthreshold : X₀ ≤ B - 1) (hAthreshold : X₀ ≤ A - 1)
    (hyBcut : y ≤ BoundedGaps.Maynard.modulusCutoff theta (B - 1))
    (hyAcut : y ≤ BoundedGaps.Maynard.modulusCutoff theta (A - 1)) :
    (∑ p ∈ varyingSingularPrimeSupport w y m,
        ∑ q ∈ auxiliaryPrimeInterval A B,
          largeGapLocalPenalty (preSievedShifts K w) m q p) ≤
      ((4 * K : ℕ) : ℝ) *
        ((BoundedGaps.Maynard.offDiagonalPairs
          (preSievedShifts K w)).card : ℝ) *
          ((((auxiliaryPrimeInterval A B).card : ℝ) *
              (8 / (w : ℝ))) +
            (C * ((B - 1 : ℕ) : ℝ) /
                Real.rpow (Real.log ((B - 1 : ℕ) : ℝ)) exponent) /
              (w : ℝ) +
            (C * ((A - 1 : ℕ) : ℝ) /
                Real.rpow (Real.log ((A - 1 : ℕ) : ℝ)) exponent) /
              (w : ℝ)) := by
  let S := varyingSingularPrimeSupport w y m
  let Q := auxiliaryPrimeInterval A B
  let P := BoundedGaps.Maynard.offDiagonalPairs
    (preSievedShifts K w)
  let a : ℝ := ((4 * K : ℕ) : ℝ)
  let N : ℝ := (P.card : ℝ)
  let QB : ℝ := (Q.card : ℝ)
  let DB : ℕ → ℝ := fun p ↦
    BoundedGaps.Maynard.maxProgressionDiscrepancy (B - 1) p
  let DA : ℕ → ℝ := fun p ↦
    BoundedGaps.Maynard.maxProgressionDiscrepancy (A - 1) p
  have hlocal : ∀ p ∈ S,
      (∑ q ∈ Q,
          largeGapLocalPenalty (preSievedShifts K w) m q p) ≤
        a / p * N * (QB / Nat.totient p + DB p + DA p) := by
    intro p hp
    have hpData := mem_varyingSingularPrimeSupport.mp hp
    exact sum_largeGapLocalPenalty_auxiliaryPrimeInterval_le_maxDiscrepancy
      hfour hpData.2.2.1 hpData.1 hpData.2.2.2
        (hpData.2.1.trans_lt hyA) hA hAB
  have hmain := sum_varyingSingularPrime_mainWeight_le
    (y := y) (m := m) hw
  have hDB := PrimeLevelWitness.sum_varyingSingularPrime_weightedDiscrepancy_le
    hlevel
    (x := B - 1) (y := y) (m := m) hw hBthreshold hyBcut
  have hDA := PrimeLevelWitness.sum_varyingSingularPrime_weightedDiscrepancy_le
    hlevel
    (x := A - 1) (y := y) (m := m) hw hAthreshold hyAcut
  have haN : 0 ≤ a * N := by positivity
  calc
    (∑ p ∈ S, ∑ q ∈ Q,
        largeGapLocalPenalty (preSievedShifts K w) m q p) ≤
        ∑ p ∈ S, a / p * N *
          (QB / Nat.totient p + DB p + DA p) := by
      exact Finset.sum_le_sum hlocal
    _ = ∑ p ∈ S, a * N *
          (QB * ((1 : ℝ) / p / Nat.totient p) +
            DB p / p + DA p / p) := by
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ = a * N *
        (QB * (∑ p ∈ S, (1 : ℝ) / p / Nat.totient p) +
          (∑ p ∈ S, DB p / p) +
          ∑ p ∈ S, DA p / p) := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ a * N *
        (QB * (8 / (w : ℝ)) +
          (C * ((B - 1 : ℕ) : ℝ) /
              Real.rpow (Real.log ((B - 1 : ℕ) : ℝ)) exponent) /
            (w : ℝ) +
          (C * ((A - 1 : ℕ) : ℝ) /
              Real.rpow (Real.log ((A - 1 : ℕ) : ℝ)) exponent) /
            (w : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ haN
      exact add_le_add
        (add_le_add (mul_le_mul_of_nonneg_left hmain (by positivity)) hDB)
        hDA
    _ = _ := by
      simp only [S, Q, P, a, N, QB, DB, DA]

/-- The inverse varying part of the truncated singular factor. -/
noncomputable def varyingSingularInverseProduct
    (K w y m q : ℕ) : ℝ :=
  ∏ p ∈ varyingSingularPrimeSupport w y m,
    (largeGapLocalAmplification (preSievedShifts K w) m q p)⁻¹

/-- Averaging the Bonferroni product over the auxiliary primes gives a
uniform lower bound.  The full loss is the explicit rough-tail main term
plus the two prime-distribution errors; no pointwise exceptional-modulus
bound is used. -/
theorem sum_varyingSingularInverseProduct_primeInterval_lower
    {theta exponent C : ℝ} {X₀ K w A B m y : ℕ}
    (hlevel : BoundedGaps.Maynard.PrimeLevelWitness
      theta exponent C X₀)
    (hfour : 4 * K ≤ w) (hw : 0 < w)
    (hyA : y < A) (hA : 0 < A) (hAB : A ≤ B)
    (hBthreshold : X₀ ≤ B - 1) (hAthreshold : X₀ ≤ A - 1)
    (hyBcut : y ≤ BoundedGaps.Maynard.modulusCutoff theta (B - 1))
    (hyAcut : y ≤ BoundedGaps.Maynard.modulusCutoff theta (A - 1)) :
    ((auxiliaryPrimeInterval A B).card : ℝ) -
        ((4 * K : ℕ) : ℝ) *
          ((BoundedGaps.Maynard.offDiagonalPairs
            (preSievedShifts K w)).card : ℝ) *
            ((((auxiliaryPrimeInterval A B).card : ℝ) *
                (8 / (w : ℝ))) +
              (C * ((B - 1 : ℕ) : ℝ) /
                  Real.rpow (Real.log ((B - 1 : ℕ) : ℝ)) exponent) /
                (w : ℝ) +
              (C * ((A - 1 : ℕ) : ℝ) /
                  Real.rpow (Real.log ((A - 1 : ℕ) : ℝ)) exponent) /
                (w : ℝ)) ≤
      ∑ q ∈ auxiliaryPrimeInterval A B,
        varyingSingularInverseProduct K w y m q := by
  let S := varyingSingularPrimeSupport w y m
  let Q := auxiliaryPrimeInterval A B
  let E : ℝ := ∑ p ∈ S, ∑ q ∈ Q,
    largeGapLocalPenalty (preSievedShifts K w) m q p
  let L : ℝ :=
    ((4 * K : ℕ) : ℝ) *
      ((BoundedGaps.Maynard.offDiagonalPairs
        (preSievedShifts K w)).card : ℝ) *
        ((((auxiliaryPrimeInterval A B).card : ℝ) *
            (8 / (w : ℝ))) +
          (C * ((B - 1 : ℕ) : ℝ) /
              Real.rpow (Real.log ((B - 1 : ℕ) : ℝ)) exponent) /
            (w : ℝ) +
          (C * ((A - 1 : ℕ) : ℝ) /
              Real.rpow (Real.log ((A - 1 : ℕ) : ℝ)) exponent) /
            (w : ℝ))
  have hE : E ≤ L := by
    dsimp only [E, L, S, Q]
    exact sum_varyingSingularPrime_localPenalty_le_primeLevelWitness
      hlevel hfour hw hyA hA hAB hBthreshold hAthreshold hyBcut hyAcut
  have hbon : ∀ q ∈ Q,
      1 - ∑ p ∈ S,
          largeGapLocalPenalty (preSievedShifts K w) m q p ≤
        varyingSingularInverseProduct K w y m q := by
    intro q hq
    have hlarge : ∀ p ∈ S,
        2 * (preSievedShifts K w).card < p := by
      intro p hp
      have hpData := mem_varyingSingularPrimeSupport.mp hp
      rw [card_preSievedShifts]
      omega
    exact one_sub_sum_largeGapLocalPenalty_le_prod_amplification_inv
      S hlarge
  calc
    ((Q.card : ℝ) - L) ≤ (Q.card : ℝ) - E :=
      sub_le_sub_left hE _
    _ = ∑ q ∈ Q, (1 - ∑ p ∈ S,
          largeGapLocalPenalty (preSievedShifts K w) m q p) := by
      simp only [E]
      rw [Finset.sum_sub_distrib]
      simp only [Finset.sum_const, nsmul_eq_mul, one_mul]
      rw [Finset.sum_comm]
      ring
    _ ≤ ∑ q ∈ Q, varyingSingularInverseProduct K w y m q := by
      exact Finset.sum_le_sum hbon
    _ = _ := by simp only [Q, L, E]

/-- Rough singular primes dividing the fixed cofactor.  Unlike the varying
support, these contribute a factor independent of the auxiliary prime. -/
def fixedSingularPrimeSupport (w y m : ℕ) : Finset ℕ :=
  (BoundedGaps.Maynard.roughPrimeSupport w y).filter fun p ↦ p ∣ m

theorem roughPrimeSupport_eq_fixed_union_varying
    (w y m : ℕ) :
    BoundedGaps.Maynard.roughPrimeSupport w y =
      fixedSingularPrimeSupport w y m ∪
        varyingSingularPrimeSupport w y m := by
  classical
  ext p
  simp only [fixedSingularPrimeSupport, varyingSingularPrimeSupport,
    Finset.mem_union, Finset.mem_filter]
  tauto

theorem fixedSingularPrimeSupport_disjoint_varying
    (w y m : ℕ) :
    Disjoint (fixedSingularPrimeSupport w y m)
      (varyingSingularPrimeSupport w y m) := by
  rw [Finset.disjoint_left]
  intro p hpFixed hpVarying
  exact (Finset.mem_filter.mp hpVarying).2
    (Finset.mem_filter.mp hpFixed).2

/-- At a rough prime dividing the fixed cofactor, the companion family has
no zero and the first family contributes exactly its `K` distinct classes.
-/
theorem largeGapLocalMultiplicity_preSievedShifts_of_dvd_m
    {K w m q p : ℕ} (hp : p.Prime) (hKw : K ≤ w)
    (hwp : w < p) (hpq : ¬p ∣ q) (hpm : p ∣ m) :
    largeGapLocalMultiplicity (preSievedShifts K w) m q p = K := by
  rw [largeGapLocalMultiplicity, largeGapLocalForbiddenResidues,
    largeGapCompanionLocalResidues_eq_empty_of_dvd hpm,
    Finset.union_empty]
  exact card_largeGapFirstLocalResidues_preSievedShifts
    hp hKw hwp hpq

/-- Closed form of the fixed inverse local amplification. -/
theorem largeGapLocalAmplification_inv_of_dvd_m
    {K w m q p : ℕ} (hp : p.Prime) (hKw : K ≤ w)
    (hwp : w < p) (hpq : ¬p ∣ q) (hpm : p ∣ m) :
    (largeGapLocalAmplification
        (preSievedShifts K w) m q p)⁻¹ =
      ((p : ℝ) - 2 * K) / ((p : ℝ) - K) := by
  rw [largeGapLocalAmplification,
    largeGapLocalMultiplicity_preSievedShifts_of_dvd_m
      hp hKw hwp hpq hpm,
    card_preSievedShifts]
  exact inv_div _ _

/-- The fixed part of the inverse singular factor. -/
noncomputable def fixedSingularInverseFactor
    (K w y m : ℕ) : ℝ :=
  ∏ p ∈ fixedSingularPrimeSupport w y m,
    ((p : ℝ) - 2 * K) / ((p : ℝ) - K)

theorem fixedSingularInverseFactor_pos
    {K w y m : ℕ} (hfour : 4 * K ≤ w) (hw : 0 < w) :
    0 < fixedSingularInverseFactor K w y m := by
  unfold fixedSingularInverseFactor
  apply Finset.prod_pos
  intro p hp
  have hpRough := (Finset.mem_filter.mp hp).1
  have hpIcc := Finset.mem_Icc.mp
    (Finset.mem_filter.mp hpRough).1
  have hwp : w < p := by omega
  have h2 : (2 * K : ℝ) < p := by exact_mod_cast (by omega : 2 * K < p)
  have h1 : (K : ℝ) < p := by exact_mod_cast (by omega : K < p)
  positivity

/-- The complete rough inverse product, before restoring the small-prime
pre-sieve portion of the singular series. -/
noncomputable def roughSingularInverseProduct
    (K w y m q : ℕ) : ℝ :=
  ∏ p ∈ BoundedGaps.Maynard.roughPrimeSupport w y,
    (largeGapLocalAmplification (preSievedShifts K w) m q p)⁻¹

theorem roughSingularInverseProduct_eq_fixed_mul_varying
    {K w A B y m q : ℕ} (hfour : 4 * K ≤ w)
    (hyA : y < A) (hq : q ∈ auxiliaryPrimeInterval A B) :
    roughSingularInverseProduct K w y m q =
      fixedSingularInverseFactor K w y m *
        varyingSingularInverseProduct K w y m q := by
  have hKw : K ≤ w := by omega
  have hqData := mem_auxiliaryPrimeInterval.mp hq
  have hqPrime := hqData.2.2
  have hpq : ∀ p ∈ fixedSingularPrimeSupport w y m, ¬p ∣ q := by
    intro p hp hpDiv
    have hpRough := (Finset.mem_filter.mp hp).1
    have hpIcc := Finset.mem_Icc.mp
      (Finset.mem_filter.mp hpRough).1
    rcases (Nat.dvd_prime hqPrime).mp hpDiv with hpOne | hpEq
    · exact (Finset.mem_filter.mp hpRough).2.ne_one hpOne
    · omega
  unfold roughSingularInverseProduct
  rw [roughPrimeSupport_eq_fixed_union_varying,
    Finset.prod_union (fixedSingularPrimeSupport_disjoint_varying w y m)]
  congr 1
  · unfold fixedSingularInverseFactor
    apply Finset.prod_congr rfl
    intro p hp
    have hpRough := (Finset.mem_filter.mp hp).1
    have hpData := Finset.mem_filter.mp hpRough
    exact largeGapLocalAmplification_inv_of_dvd_m hpData.2 hKw
      (by
        have hpIcc := Finset.mem_Icc.mp hpData.1
        omega)
      (hpq p hp) (Finset.mem_filter.mp hp).2

/-- Full averaged inverse-singular-factor lower bound, with the fixed
cofactor primes restored as an exact positive multiplicative factor. -/
theorem sum_roughSingularInverseProduct_primeInterval_lower
    {theta exponent C : ℝ} {X₀ K w A B m y : ℕ}
    (hlevel : BoundedGaps.Maynard.PrimeLevelWitness
      theta exponent C X₀)
    (hfour : 4 * K ≤ w) (hw : 0 < w)
    (hyA : y < A) (hA : 0 < A) (hAB : A ≤ B)
    (hBthreshold : X₀ ≤ B - 1) (hAthreshold : X₀ ≤ A - 1)
    (hyBcut : y ≤ BoundedGaps.Maynard.modulusCutoff theta (B - 1))
    (hyAcut : y ≤ BoundedGaps.Maynard.modulusCutoff theta (A - 1)) :
    fixedSingularInverseFactor K w y m *
      (((auxiliaryPrimeInterval A B).card : ℝ) -
        ((4 * K : ℕ) : ℝ) *
          ((BoundedGaps.Maynard.offDiagonalPairs
            (preSievedShifts K w)).card : ℝ) *
            ((((auxiliaryPrimeInterval A B).card : ℝ) *
                (8 / (w : ℝ))) +
              (C * ((B - 1 : ℕ) : ℝ) /
                  Real.rpow (Real.log ((B - 1 : ℕ) : ℝ)) exponent) /
                (w : ℝ) +
              (C * ((A - 1 : ℕ) : ℝ) /
                  Real.rpow (Real.log ((A - 1 : ℕ) : ℝ)) exponent) /
                (w : ℝ))) ≤
      ∑ q ∈ auxiliaryPrimeInterval A B,
        roughSingularInverseProduct K w y m q := by
  have hvary := sum_varyingSingularInverseProduct_primeInterval_lower
    (m := m) hlevel hfour hw hyA hA hAB hBthreshold hAthreshold
      hyBcut hyAcut
  have hfixed : 0 ≤ fixedSingularInverseFactor K w y m :=
    (fixedSingularInverseFactor_pos hfour hw).le
  calc
    fixedSingularInverseFactor K w y m *
        (((auxiliaryPrimeInterval A B).card : ℝ) -
          ((4 * K : ℕ) : ℝ) *
            ((BoundedGaps.Maynard.offDiagonalPairs
              (preSievedShifts K w)).card : ℝ) *
              ((((auxiliaryPrimeInterval A B).card : ℝ) *
                  (8 / (w : ℝ))) +
                (C * ((B - 1 : ℕ) : ℝ) /
                    Real.rpow (Real.log ((B - 1 : ℕ) : ℝ)) exponent) /
                  (w : ℝ) +
                (C * ((A - 1 : ℕ) : ℝ) /
                    Real.rpow (Real.log ((A - 1 : ℕ) : ℝ)) exponent) /
                  (w : ℝ))) ≤
        fixedSingularInverseFactor K w y m *
          (∑ q ∈ auxiliaryPrimeInterval A B,
            varyingSingularInverseProduct K w y m q) :=
      mul_le_mul_of_nonneg_left hvary hfixed
    _ = ∑ q ∈ auxiliaryPrimeInterval A B,
          fixedSingularInverseFactor K w y m *
            varyingSingularInverseProduct K w y m q := by
      rw [Finset.mul_sum]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro q hq
      exact (roughSingularInverseProduct_eq_fixed_mul_varying
        hfour hyA hq).symm

end

end Erdos4b
