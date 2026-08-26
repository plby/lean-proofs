/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierAuxiliaryPrime

/-!
# The actual rough singular product

The literal affine singular product is the Fourier singular product
times the single auxiliary-prime correction. In particular no claim
of distinct residue roots at that prime is used.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

def roughActualAffineSingularFactor (H : Finset ℕ) (w m q p : ℕ) : ℂ :=
  if w < p then (largeGapLocalFactor H m q p : ℂ) else 1

theorem roughDoubledFourierSingularFactor_indexed_eq (K w m q p : ℕ) :
    roughDoubledFourierSingularFactor w (indexedPreSievedFourierEdges K w m q)
      (affineFourierCompanionSwitch m) p =
    roughDoubledFourierSingularFactor w
      (affineFourierCollisionEdges (preSievedShifts K w) m q)
      (affineFourierCompanionSwitch m) p := by
  simp only [roughDoubledFourierSingularFactor, doubledFourierSingularFactor,
    doubledFourierExceptionalCount, indexedPreSievedFourierEdges, Finset.card_map,
    Finset.card_univ, Fintype.card_sum, Fintype.card_fin, Fintype.card_coe,
    card_preSievedShifts]

theorem roughActualAffineSingularFactor_eq_correction_mul
    {K w m q : ℕ} (hq : q.Prime) (hKw : K ≤ w) (hwq : w < q)
    (hlarge : 7 * (Fintype.card (preSievedShifts K w ⊕ preSievedShifts K w) : ℝ) ≤ w)
    (p : Nat.Primes) :
    roughActualAffineSingularFactor (preSievedShifts K w) w m q p =
      (if p.val = q then affineAuxiliaryPrimeCorrection (preSievedShifts K w) m q else 1) *
        roughDoubledFourierSingularFactor w
          (affineFourierCollisionEdges (preSievedShifts K w) m q)
          (affineFourierCompanionSwitch m) p := by
  by_cases hpq : p.val = q
  · have hpw : (w : ℝ) ≤ q := by exact_mod_cast hwq.le
    have hn : (0 : ℝ) ≤ Fintype.card (preSievedShifts K w ⊕ preSievedShifts K w) :=
      Nat.cast_nonneg _
    have hedge : (affineFourierCollisionEdges (preSievedShifts K w) m q q).card ≤
        Fintype.card (preSievedShifts K w) := by
      rw [affineFourierCollisionEdges_eq_empty_of_dvd_q _ hq (dvd_refl q)]
      simp
    have hnorm := half_le_norm_doubledFourierSingularFactor
      (affineFourierCollisionEdges (preSievedShifts K w) m q) (affineFourierCompanionSwitch m)
      (by exact_mod_cast hq.two_le) (by linarith) hedge
    have hS0 : doubledFourierSingularFactor
        (affineFourierCollisionEdges (preSievedShifts K w) m q)
        (affineFourierCompanionSwitch m) q ≠ 0 := by
      intro hz
      rw [hz, norm_zero] at hnorm
      norm_num at hnorm
    simp only [roughActualAffineSingularFactor, roughDoubledFourierSingularFactor,
      hpq, if_pos hwq, if_true]
    exact (div_mul_cancel₀ _ hS0).symm
  · have hnotdvd : ¬p.val ∣ q := by
      simpa only [Nat.prime_dvd_prime_iff_eq p.property hq] using hpq
    by_cases hwp : w < p.val
    · rw [roughActualAffineSingularFactor, roughDoubledFourierSingularFactor,
        if_pos hwp, if_pos hwp, if_neg hpq, one_mul]
      exact (doubledFourierSingularFactor_eq_actual_localFactor p.property hKw hwp hnotdvd).symm
    · simp only [roughActualAffineSingularFactor, roughDoubledFourierSingularFactor,
        if_neg hwp, if_neg hpq, one_mul]

theorem hasProd_roughActualAffineSingularFactor
    {K w m q : ℕ} (hm : 0 < m) (hq : q.Prime) (hKw : K ≤ w) (hwq : w < q)
    (hlarge : 7 * (Fintype.card (preSievedShifts K w ⊕ preSievedShifts K w) : ℝ) ≤ w) :
    HasProd (fun p : Nat.Primes ↦ roughActualAffineSingularFactor (preSievedShifts K w) w m q p)
      (affineAuxiliaryPrimeCorrection (preSievedShifts K w) m q *
        ∏' p : Nat.Primes, roughDoubledFourierSingularFactor w
          (affineFourierCollisionEdges (preSievedShifts K w) m q)
          (affineFourierCompanionSwitch m) p) := by
  classical
  have hM := Nat.mul_pos hm (crossExceptionalModulus_pos (H := preSievedShifts K w) hm hq)
  have hedge (p : Nat.Primes) (hwp : w < p.val) :
      (affineFourierCollisionEdges (preSievedShifts K w) m q p).card ≤
        Fintype.card (preSievedShifts K w) := by
    simpa only [Fintype.card_coe, card_preSievedShifts] using
      card_affineFourierCollisionEdges_preSieved_le (m := m) (q := q) p.property hKw hwp
  have hgeneric (p : Nat.Primes) (_ : w < p.val)
      (hnot : ¬p.val ∣ m * crossExceptionalModulus (preSievedShifts K w) m q) :=
    affineFourierCollisionEdges_generic (preSievedShifts K w) hnot
  have hS := multipliable_roughDoubledFourierSingularFactor
    (affineFourierCollisionEdges (preSievedShifts K w) m q)
    (affineFourierCompanionSwitch m) hM hlarge hedge hgeneric
  have hc : HasProd (fun p : Nat.Primes ↦
      if p.val = q then affineAuxiliaryPrimeCorrection (preSievedShifts K w) m q else 1)
      (affineAuxiliaryPrimeCorrection (preSievedShifts K w) m q) := by
    simpa only [Subtype.ext_iff] using!
      hasProd_ite_eq (⟨q, hq⟩ : Nat.Primes)
        (affineAuxiliaryPrimeCorrection (preSievedShifts K w) m q)
  convert! hc.mul hS.hasProd using 1
  ext p
  exact roughActualAffineSingularFactor_eq_correction_mul hq hKw hwq hlarge p

theorem tprod_roughActualAffineSingularFactor_eq_indexed
    {K w m q : ℕ} (hm : 0 < m) (hq : q.Prime) (hKw : K ≤ w) (hwq : w < q)
    (hlarge : 7 * (Fintype.card (preSievedShifts K w ⊕ preSievedShifts K w) : ℝ) ≤ w) :
    (∏' p : Nat.Primes, roughActualAffineSingularFactor (preSievedShifts K w) w m q p) =
      affineAuxiliaryPrimeCorrection (preSievedShifts K w) m q *
        ∏' p : Nat.Primes, roughDoubledFourierSingularFactor w
          (indexedPreSievedFourierEdges K w m q)
          (affineFourierCompanionSwitch m) p := by
  rw [(hasProd_roughActualAffineSingularFactor hm hq hKw hwq hlarge).tprod_eq]
  congr 1
  exact tprod_congr (fun p ↦ (roughDoubledFourierSingularFactor_indexed_eq K w m q p).symm)

end

end Erdos4b
