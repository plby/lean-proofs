import ErdosProblems.Erdos394.BadUnitPrimeSieve

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Good prime mass and its contribution to denominator lower bounds
-/

open Nat Finset

namespace Erdos394

/-- Total weighted prime mass in `(A,U]`. -/
def primeIntervalWeightedMass (A U : ℕ) : ℝ :=
  ∑ ell ∈ largePrimeInterval A U, (ell : ℝ)

/-- Weighted prime mass in unit classes outside `B`. -/
noncomputable def primeGoodUnitWeightedMass
    (A U q : ℕ) (B : Finset (ZMod q)ˣ) : ℝ :=
  ∑ ell ∈ largePrimeInterval A U,
    if hcop : ell.Coprime q then
      if ZMod.unitOfCoprime ell hcop ∉ B then (ell : ℝ) else 0
    else 0

/-- A prime larger than every selected prime is coprime to their product. -/
theorem primeInterval_coprime_primeProduct
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    {A U ell : ℕ} (hupper : ∀ p ∈ P, p ≤ A)
    (hell : ell ∈ largePrimeInterval A U) :
    ell.Coprime (primeProduct P) := by
  have hellp := (mem_largePrimeInterval_iff.mp hell).2.2
  rw [hellp.coprime_iff_not_dvd]
  intro hdiv
  rw [primeProduct] at hdiv
  obtain ⟨p, hpP, hellpdiv⟩ :=
    (_root_.Prime.dvd_finsetProd_iff hellp.prime (fun p : ℕ ↦ p)).mp hdiv
  have heq : ell = p :=
    (Nat.prime_dvd_prime_iff_eq hellp (hprime p hpP)).mp hellpdiv
  have hAell := (mem_largePrimeInterval_iff.mp hell).1
  have hpA := hupper p hpP
  omega

/-- A prime larger than every sieve prime is free of that sieve set. -/
theorem badPrimeSet_primeInterval_eq_empty
    (S : Finset ℕ) (hprime : ∀ p ∈ S, p.Prime)
    {A U ell : ℕ} (hupper : ∀ p ∈ S, p ≤ A)
    (hell : ell ∈ largePrimeInterval A U) :
    badPrimeSet S ell = ∅ := by
  ext p
  simp only [badPrimeSet, Finset.mem_filter]
  constructor
  · intro hp
    have hpprime := hprime p hp.1
    have hellprime := (mem_largePrimeInterval_iff.mp hell).2.2
    have heq : p = ell :=
      (Nat.dvd_prime hellprime).mp hp.2 |>.resolve_left hpprime.ne_one
    have hAell := (mem_largePrimeInterval_iff.mp hell).1
    have hpA := hupper p hp.1
    exfalso
    omega
  · intro hp
    simp at hp

/-- If every block prime is coprime to `q`, total mass partitions exactly into
bad and good unit classes. -/
theorem primeIntervalWeightedMass_eq_bad_add_good
    (A U q : ℕ) (B : Finset (ZMod q)ˣ)
    (hcop : ∀ ell ∈ largePrimeInterval A U, ell.Coprime q) :
    primeIntervalWeightedMass A U =
      primeBadUnitWeightedMass A U q B +
        primeGoodUnitWeightedMass A U q B := by
  unfold primeIntervalWeightedMass primeBadUnitWeightedMass
    primeGoodUnitWeightedMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ell hell
  rw [dif_pos (hcop ell hell), dif_pos (hcop ell hell)]
  by_cases hB : ZMod.unitOfCoprime ell (hcop ell hell) ∈ B
  · simp [hB]
  · simp [hB]

/-- Subtracting any valid bad-mass upper bound gives a good-mass lower bound. -/
theorem lower_sub_bad_le_primeGoodUnitWeightedMass
    (A U q : ℕ) (B : Finset (ZMod q)ˣ)
    (hcop : ∀ ell ∈ largePrimeInterval A U, ell.Coprime q)
    {L E : ℝ} (htotal : L ≤ primeIntervalWeightedMass A U)
    (hbad : primeBadUnitWeightedMass A U q B ≤ E) :
    L - E ≤ primeGoodUnitWeightedMass A U q B := by
  rw [primeIntervalWeightedMass_eq_bad_add_good A U q B hcop] at htotal
  linarith

/-- `t_K(ell q)` mass contributed by primes in shifted-good classes. -/
noncomputable def shiftedGoodPrimeTMass
    (P : Finset ℕ) (K Y A U : ℕ) (hprime : ∀ p ∈ P, p.Prime) : ℝ :=
  ∑ ell ∈ largePrimeInterval A U,
    if hcop : ell.Coprime (primeProduct P) then
      if ZMod.unitOfCoprime ell hcop ∉
          globalShiftedRootBadUnitSet P K Y hprime then
        (t K (ell * primeProduct P) : ℝ)
      else 0
    else 0

/-- On a sufficiently high prime interval, F-076 turns weighted good-prime
mass into at least `Y/2` times that mass in `t_K`. -/
theorem mul_primeGoodMass_le_two_shiftedGoodPrimeTMass
    (P : Finset ℕ) (K Y A U : ℕ) (hK : 0 < K)
    (hprime : ∀ p ∈ P, p.Prime)
    (hheight : 2 * K ≤ Y * A) :
    (Y : ℝ) * primeGoodUnitWeightedMass A U (primeProduct P)
        (globalShiftedRootBadUnitSet P K Y hprime) ≤
      2 * shiftedGoodPrimeTMass P K Y A U hprime := by
  unfold primeGoodUnitWeightedMass shiftedGoodPrimeTMass
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro ell hell
  by_cases hcop : ell.Coprime (primeProduct P)
  · rw [dif_pos hcop, dif_pos hcop]
    by_cases hgood : ZMod.unitOfCoprime ell hcop ∉
        globalShiftedRootBadUnitSet P K Y hprime
    · rw [if_pos hgood, if_pos hgood]
      have ht := shifted_good_unit_forces_t_add_large
        P K Y ell hK hprime (mem_largePrimeInterval_iff.mp hell).2.2 hcop hgood
      have hAell := (mem_largePrimeInterval_iff.mp hell).1
      have hheight' : 2 * K ≤ Y * ell := by
        exact hheight.trans (Nat.mul_le_mul_left Y hAell.le)
      have hnat : Y * ell ≤ 2 * t K (ell * primeProduct P) := by omega
      exact_mod_cast hnat
    · rw [if_neg hgood, if_neg hgood]
      norm_num
  · rw [dif_neg hcop, dif_neg hcop]
    norm_num

/-- A convenient divided form of the preceding lower bound. -/
theorem half_mul_primeGoodMass_le_shiftedGoodPrimeTMass
    (P : Finset ℕ) (K Y A U : ℕ) (hK : 0 < K)
    (hprime : ∀ p ∈ P, p.Prime)
    (hheight : 2 * K ≤ Y * A) :
    ((Y : ℝ) / 2) * primeGoodUnitWeightedMass A U (primeProduct P)
        (globalShiftedRootBadUnitSet P K Y hprime) ≤
      shiftedGoodPrimeTMass P K Y A U hprime := by
  have h := mul_primeGoodMass_le_two_shiftedGoodPrimeTMass
    P K Y A U hK hprime hheight
  nlinarith

end Erdos394
