import ErdosProblems.Erdos394.GoodPrimeMass

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Complete finite denominator lower bound for one selected modulus
-/

open Nat Finset

namespace Erdos394

/-- A normalized shifted-bad density bound gives an unnormalized cardinality
bound. -/
theorem card_globalShiftedRootBadUnitSet_real_le
    (P : Finset ℕ) (K Y : ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (hK : 1 ≤ K) (hlarge : ∀ p ∈ P, K < p) :
    ((globalShiftedRootBadUnitSet P K Y hprime).card : ℝ) ≤
      ((((K ^ (P.card + 1) : ℕ) : ℝ) * (Y : ℝ) /
          (primeProduct P : ℝ)) * (primeUnitCount P : ℝ)) := by
  have hdensity := normalized_card_globalShiftedRootBadUnitSet_le
    P K Y hprime hK hlarge
  have hphi : (0 : ℝ) < primeUnitCount P := by
    exact_mod_cast (show 0 < primeUnitCount P by
      unfold primeUnitCount
      exact Finset.prod_pos fun p hp ↦ by
        have := (hprime p hp).two_le
        omega)
  exact (div_le_iff₀ hphi).mp hdensity

/-- Complete one-modulus lower bound: total prime mass minus the Brun-controlled
bad-class mass, multiplied by the shifted-root height `Y/2`. -/
theorem fixedQ_shiftedGoodPrimeTMass_lower
    (P S : Finset ℕ) (K Y A U R : ℕ)
    (hK : 0 < K) (hprime : ∀ p ∈ P, p.Prime)
    (hlarge : ∀ p ∈ P, K < p)
    (hPupper : ∀ p ∈ P, p ≤ A)
    (hSprime : ∀ p ∈ S, p.Prime) (hSupper : ∀ p ∈ S, p ≤ A)
    (hcopS : ∀ p ∈ S, (primeProduct P).Coprime p)
    (hheight : 2 * K ≤ Y * A)
    (hR : Even R)
    (htail :
      (∑ p ∈ S, (1 / (p : ℝ))) ^ (R + 1) /
          ((R + 1).factorial : ℝ) ≤
        localEulerProduct S (fun p ↦ 1 / (p : ℝ)))
    {L : ℝ} (htotal : L ≤ primeIntervalWeightedMass A U) :
    ((Y : ℝ) / 2) *
      (L -
        ((((K ^ (P.card + 1) : ℕ) : ℝ) * (Y : ℝ) /
            (primeProduct P : ℝ)) * (primeUnitCount P : ℝ)) *
          (((U : ℝ) ^ 2 / (primeProduct P : ℝ)) *
            localEulerProduct S (fun p ↦ 1 / (p : ℝ)) +
          (truncatedSubsets S R).card * (2 * (U : ℝ)))) ≤
      shiftedGoodPrimeTMass P K Y A U hprime := by
  have hq : 0 < primeProduct P := by
    unfold primeProduct
    exact Finset.prod_pos fun p hp ↦ (hprime p hp).pos
  let B := globalShiftedRootBadUnitSet P K Y hprime
  let Xmain : ℝ := ((U : ℝ) ^ 2 / (primeProduct P : ℝ)) *
    localEulerProduct S (fun p ↦ 1 / (p : ℝ)) +
      (truncatedSubsets S R).card * (2 * (U : ℝ))
  have hfree : ∀ ell ∈ largePrimeInterval A U,
      badPrimeSet S ell = ∅ := by
    intro ell hell
    exact badPrimeSet_primeInterval_eq_empty S hSprime hSupper
      (U := U) hell
  have hcopBlock : ∀ ell ∈ largePrimeInterval A U,
      ell.Coprime (primeProduct P) := by
    intro ell hell
    exact primeInterval_coprime_primeProduct P hprime hPupper
      (U := U) hell
  have hbad0 := primeBadUnitWeightedMass_le_card_mul_brun
    A U (primeProduct P) S B hq hSprime hcopS hfree R hR htail
  have hBcard : (B.card : ℝ) ≤
      (((K ^ (P.card + 1) : ℕ) : ℝ) * (Y : ℝ) /
          (primeProduct P : ℝ)) * (primeUnitCount P : ℝ) := by
    dsimp [B]
    exact card_globalShiftedRootBadUnitSet_real_le P K Y hprime (by omega) hlarge
  have hEuler0 : 0 ≤ localEulerProduct S (fun p ↦ 1 / (p : ℝ)) := by
    apply localEulerProduct_nonneg S (fun p ↦ 1 / (p : ℝ))
    · intro p hp; positivity
    · intro p hp
      have hp0 : (0 : ℝ) < p := by exact_mod_cast (hSprime p hp).pos
      exact (div_le_one hp0).2 (by exact_mod_cast (hSprime p hp).one_le)
  have hX0 : 0 ≤ Xmain := by dsimp [Xmain]; positivity
  have hbad : primeBadUnitWeightedMass A U (primeProduct P) B ≤
      ((((K ^ (P.card + 1) : ℕ) : ℝ) * (Y : ℝ) /
          (primeProduct P : ℝ)) * (primeUnitCount P : ℝ)) * Xmain := by
    apply hbad0.trans
    exact mul_le_mul_of_nonneg_right hBcard hX0
  have hgood : L -
      ((((K ^ (P.card + 1) : ℕ) : ℝ) * (Y : ℝ) /
          (primeProduct P : ℝ)) * (primeUnitCount P : ℝ)) * Xmain ≤
      primeGoodUnitWeightedMass A U (primeProduct P) B :=
    lower_sub_bad_le_primeGoodUnitWeightedMass A U (primeProduct P) B
      hcopBlock htotal hbad
  have htransfer := half_mul_primeGoodMass_le_shiftedGoodPrimeTMass
    P K Y A U hK hprime hheight
  dsimp [B] at hgood htransfer ⊢
  dsimp [Xmain] at hgood ⊢
  have hY0 : 0 ≤ (Y : ℝ) / 2 := by positivity
  exact (mul_le_mul_of_nonneg_left hgood hY0).trans htransfer

end Erdos394
