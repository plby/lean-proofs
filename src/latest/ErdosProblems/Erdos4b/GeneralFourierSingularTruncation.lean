/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierPhysicalDensity
import ErdosProblems.Erdos4b.GeneralFourierSingularTailLimit

/-!
# Exact truncation of the literal affine singular product

The pre-sieve cutoff and singular-product cutoff are distinct parameters.
The auxiliary-prime factor remains in the tail when the latter cutoff is
below the auxiliary prime.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

theorem roughActualAffineSingularFactor_larger_cutoff_eq
    {K w m q Y : ℕ} (hq : q.Prime) (hKw : K ≤ w) (hwY : w ≤ Y) (hYq : Y < q)
    (hlarge : 7 * (Fintype.card (preSievedShifts K w ⊕ preSievedShifts K w) : ℝ) ≤ w)
    (p : Nat.Primes) :
    roughActualAffineSingularFactor (preSievedShifts K w) Y m q p =
      (if p.val = q then affineAuxiliaryPrimeCorrection (preSievedShifts K w) m q else 1) *
        roughDoubledFourierSingularFactor Y (indexedPreSievedFourierEdges K w m q)
          (affineFourierCompanionSwitch m) p := by
  by_cases hYp : Y < p.val
  · have hwp : w < p.val := hwY.trans_lt hYp
    have h := roughActualAffineSingularFactor_eq_correction_mul (m := m) hq hKw
      (hwY.trans_lt hYq) hlarge p
    rw [← roughDoubledFourierSingularFactor_indexed_eq] at h
    simpa only [roughActualAffineSingularFactor, roughDoubledFourierSingularFactor,
      if_pos hYp, if_pos hwp] using h
  · have hpq : p.val ≠ q := by omega
    simp only [roughActualAffineSingularFactor, roughDoubledFourierSingularFactor,
      if_neg hYp, if_neg hpq, mul_one]

theorem hasProd_roughActualAffineSingularFactor_larger_cutoff
    {K w m q Y : ℕ} (hm : 0 < m) (hq : q.Prime) (hKw : K ≤ w)
    (hwY : w ≤ Y) (hYq : Y < q)
    (hlarge : 7 * (Fintype.card (preSievedShifts K w ⊕ preSievedShifts K w) : ℝ) ≤ w) :
    HasProd (fun p : Nat.Primes ↦ roughActualAffineSingularFactor (preSievedShifts K w) Y m q p)
      (affineAuxiliaryPrimeCorrection (preSievedShifts K w) m q *
        ∏' p : Nat.Primes, roughDoubledFourierSingularFactor Y
          (indexedPreSievedFourierEdges K w m q) (affineFourierCompanionSwitch m) p) := by
  classical
  have hM := Nat.mul_pos hm (crossExceptionalModulus_pos (H := preSievedShifts K w) hm hq)
  have hcard : 7 * (Fintype.card (Fin K ⊕ Fin K) : ℝ) ≤ Y := by
    simpa only [Fintype.card_sum, Fintype.card_fin, Fintype.card_coe, card_preSievedShifts]
      using hlarge.trans (by exact_mod_cast hwY)
  have hedge (p : Nat.Primes) (hYp : Y < p.val) :
      (indexedPreSievedFourierEdges K w m q p).card ≤ Fintype.card (Fin K) := by
    simpa only [Fintype.card_fin] using
      card_indexedPreSievedFourierEdges_le p.property hKw (hwY.trans_lt hYp)
  have hgeneric (p : Nat.Primes) (_ : Y < p.val)
      (hnot : ¬p.val ∣ m * crossExceptionalModulus (preSievedShifts K w) m q) :=
    indexedPreSievedFourierEdges_generic hnot
  have hS := multipliable_roughDoubledFourierSingularFactor
    (indexedPreSievedFourierEdges K w m q) (affineFourierCompanionSwitch m)
    hM hcard hedge hgeneric
  have hc : HasProd (fun p : Nat.Primes ↦
      if p.val = q then affineAuxiliaryPrimeCorrection (preSievedShifts K w) m q else 1)
      (affineAuxiliaryPrimeCorrection (preSievedShifts K w) m q) := by
    simpa only [Subtype.ext_iff] using!
      hasProd_ite_eq (⟨q, hq⟩ : Nat.Primes)
        (affineAuxiliaryPrimeCorrection (preSievedShifts K w) m q)
  convert! hc.mul hS.hasProd using 1
  ext p
  exact roughActualAffineSingularFactor_larger_cutoff_eq hq hKw hwY hYq hlarge p

theorem fullActualAffineSingularProduct_eq_truncated_mul_tail
    {K w m q Y : ℕ} (hm : 0 < m) (hq : q.Prime) (hKw : K ≤ w)
    (hwY : w ≤ Y) (hYq : Y < q)
    (hlarge : 7 * (Fintype.card (preSievedShifts K w ⊕ preSievedShifts K w) : ℝ) ≤ w) :
    fullActualAffineSingularProduct K w m q =
      (largeGapSingularSeries (preSievedShifts K w) m q Y : ℂ) *
        ∏' p : Nat.Primes, roughActualAffineSingularFactor (preSievedShifts K w) Y m q p := by
  have hfull := hasProd_fullActualAffineSingularProduct hm hq hKw (hwY.trans_lt hYq) hlarge
  have hs := hasProd_small_actualAffineSingularFactors (preSievedShifts K w) Y m q
  have hr := (hasProd_roughActualAffineSingularFactor_larger_cutoff
    hm hq hKw hwY hYq hlarge).multipliable.hasProd
  apply hfull.unique
  convert! hs.mul hr using 1
  ext p
  by_cases hpY : p.val ≤ Y
  · simp only [if_pos hpY, roughActualAffineSingularFactor,
      if_neg (Nat.not_lt.mpr hpY), mul_one]
  · simp only [if_neg hpY, roughActualAffineSingularFactor,
      if_pos (Nat.lt_of_not_ge hpY), one_mul]

end

end Erdos4b
