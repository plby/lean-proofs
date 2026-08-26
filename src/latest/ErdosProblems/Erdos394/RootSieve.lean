import ErdosProblems.Erdos394.RestrictedRootGap
import ErdosProblems.Erdos394.PrimeBrun
import ErdosProblems.Erdos394.UnitProgressions

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Aggregating the restricted-root mean with the explicit prime sieve
-/

open Nat Finset

namespace Erdos394

/-- A sum over all elements is independent of the chosen `Fintype` instance. -/
theorem sum_univ_fintype_independent {α : Type*} {β : Type*}
    [AddCommMonoid β] (i₁ i₂ : Fintype α) (f : α → β) :
    (@Finset.univ α i₁).sum f = (@Finset.univ α i₂).sum f := by
  apply Finset.sum_congr
  · ext a
    simp
  · intro a ha
    rfl

/-- `t₂(mq)` mass over positive, coprime, sifted starts `m≤M`. -/
noncomputable def tMulCoprimeSiftedMass
    (P : Finset ℕ) (M q : ℕ) : ℝ :=
  ∑ m ∈ Finset.range (M + 1),
    if hm : 0 < m then
      if hcop : m.Coprime q then
        if badPrimeSet P m = ∅ then (t 2 (m * q) : ℝ) else 0
      else 0
    else 0

/-- The corresponding restricted-root weighted mass. -/
noncomputable def rootWeightedSiftedMass
    (P : Finset ℕ) (M q : ℕ) (hodd : Odd q) : ℝ :=
  ∑ m ∈ Finset.range (M + 1),
    if hm : 0 < m then
      if hcop : m.Coprime q then
        if badPrimeSet P m = ∅ then
          (m : ℝ) * restrictedRootMin q hodd (ZMod.unitOfCoprime m hcop)
        else 0
      else 0
    else 0

/-- The restricted root gives a pointwise majorant for the sifted `t₂` mass. -/
theorem tMulCoprimeSiftedMass_le_rootWeighted
    (P : Finset ℕ) (M : ℕ) {q : ℕ} (hodd : Odd q) :
    tMulCoprimeSiftedMass P M q ≤ rootWeightedSiftedMass P M q hodd := by
  unfold tMulCoprimeSiftedMass rootWeightedSiftedMass
  apply Finset.sum_le_sum
  intro m hm
  by_cases hmpos : 0 < m
  · rw [dif_pos hmpos, dif_pos hmpos]
    by_cases hcop : m.Coprime q
    · rw [dif_pos hcop, dif_pos hcop]
      by_cases hsift : badPrimeSet P m = ∅
      · rw [if_pos hsift, if_pos hsift]
        exact_mod_cast t_two_mul_le_restrictedRootMin hmpos hodd hcop
      · rw [if_neg hsift, if_neg hsift]
    · rw [dif_neg hcop, dif_neg hcop]
  · rw [dif_neg hmpos, dif_neg hmpos]

/-- Partition the restricted-root weighted mass into unit residue classes. -/
theorem rootWeightedSiftedMass_eq_sum_units
    (P : Finset ℕ) (M : ℕ) {q : ℕ} [NeZero q] (hodd : Odd q) :
    rootWeightedSiftedMass P M q hodd =
      ∑ a : (ZMod q)ˣ,
        restrictedRootMin q hodd a *
          siftedMass (residueClassUpTo M q (unitResidue q a))
            (fun m : ℕ ↦ (m : ℝ)) (badPrimeSet P) := by
  let F : (ZMod q)ˣ → ℕ → ℝ := fun a m ↦
    if 0 < m ∧ badPrimeSet P m = ∅ then
      restrictedRootMin q hodd a * (m : ℝ)
    else 0
  have hpartition := sum_unit_residueClasses_eq_sum_coprime
    (M := M) (q := q) hodd.pos F
  have hnatural : rootWeightedSiftedMass P M q hodd =
      ∑ m ∈ Finset.range (M + 1),
        if hcop : m.Coprime q then F (ZMod.unitOfCoprime m hcop) m else 0 := by
    unfold rootWeightedSiftedMass
    apply Finset.sum_congr rfl
    intro m hm
    by_cases hmpos : 0 < m
    · rw [dif_pos hmpos]
      by_cases hcop : m.Coprime q
      · rw [dif_pos hcop, dif_pos hcop]
        by_cases hsift : badPrimeSet P m = ∅
        · rw [if_pos hsift]
          simp [F, hmpos, hsift]
          ring
        · rw [if_neg hsift]
          simp [F, hmpos, hsift]
      · rw [dif_neg hcop, dif_neg hcop]
    · rw [dif_neg hmpos]
      by_cases hcop : m.Coprime q
      · rw [dif_pos hcop]
        simp [F, hmpos]
      · rw [dif_neg hcop]
  rw [hnatural, ← hpartition]
  apply Finset.sum_congr rfl
  intro a ha
  unfold siftedMass F
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  by_cases hsift : badPrimeSet P m = ∅
  · rw [if_pos hsift]
    by_cases hmpos : 0 < m
    · rw [if_pos ⟨hmpos, hsift⟩]
    · have hmzero : m = 0 := Nat.eq_zero_of_not_pos hmpos
      subst m
      simp
  · rw [if_neg hsift]
    have hpair : ¬(0 < m ∧ badPrimeSet P m = ∅) := fun h ↦ hsift h.2
    rw [if_neg hpair]
    ring

/-- Real form of the exact restricted-root mean. -/
theorem sum_restrictedRootMin_real {q : ℕ} [NeZero q]
    (hsq : Squarefree q) (hodd : Odd q) :
    (∑ a : (ZMod q)ˣ, (restrictedRootMin q hodd a : ℝ)) =
      ((q : ℝ) * (q.totient : ℝ)) /
        ((2 ^ q.primeFactors.card : ℕ) : ℝ) := by
  have hmean := pow_card_mul_sum_restrictedRootMin hsq hodd
  have hmeanR : ((2 ^ q.primeFactors.card : ℕ) : ℝ) *
      (∑ a : (ZMod q)ˣ, (restrictedRootMin q hodd a : ℝ)) =
      (q : ℝ) * (q.totient : ℝ) := by
    have hcast := congrArg (fun n : ℕ ↦ (n : ℝ)) hmean
    push_cast at hcast
    convert hcast using 1
    congr 1
    · norm_num
    · apply sum_univ_fintype_independent
  have hpow : (0 : ℝ) < ((2 ^ q.primeFactors.card : ℕ) : ℝ) := by positivity
  apply (eq_div_iff hpow.ne').2
  nlinarith

/-- Fixed-modulus aggregate Brun bound after summing all unit residue classes. -/
theorem tMulCoprimeSiftedMass_le_brun
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    {M q R : ℕ} [NeZero q] (hsq : Squarefree q) (hodd : Odd q)
    (hcopP : ∀ p ∈ P, q.Coprime p) (hR : Even R)
    (htail :
      (∑ p ∈ P, (1 / (p : ℝ))) ^ (R + 1) /
          ((R + 1).factorial : ℝ) ≤
        localEulerProduct P (fun p ↦ 1 / (p : ℝ))) :
    tMulCoprimeSiftedMass P M q ≤
      (((M : ℝ) ^ 2 / (q : ℝ)) *
          localEulerProduct P (fun p ↦ 1 / (p : ℝ)) +
        (truncatedSubsets P R).card * (2 * (M : ℝ))) *
      (((q : ℝ) * (q.totient : ℝ)) /
        ((2 ^ q.primeFactors.card : ℕ) : ℝ)) := by
  apply (tMulCoprimeSiftedMass_le_rootWeighted P M hodd).trans
  rw [rootWeightedSiftedMass_eq_sum_units P M hodd]
  let Xmain : ℝ := ((M : ℝ) ^ 2 / (q : ℝ)) *
    localEulerProduct P (fun p ↦ 1 / (p : ℝ)) +
      (truncatedSubsets P R).card * (2 * (M : ℝ))
  have hroot0 : ∀ a : (ZMod q)ˣ,
      0 ≤ (restrictedRootMin q hodd a : ℝ) := by
    intro a
    positivity
  have hclass : ∀ a : (ZMod q)ˣ,
      siftedMass (residueClassUpTo M q (unitResidue q a))
          (fun m : ℕ ↦ (m : ℝ)) (badPrimeSet P) ≤ Xmain := by
    intro a
    have ha_lt : unitResidue q a < q := ZMod.val_lt (a : ZMod q)
    have hsieve := primeSiftedMass_le_two_product_add_error
      P hprime (M := M) (q := q) (h := unitResidue q a) (R := R)
      hodd.pos ha_lt hcopP hR htail
    dsimp [Xmain]
    convert hsieve using 1 <;> ring
  calc
    (∑ a : (ZMod q)ˣ,
      (restrictedRootMin q hodd a : ℝ) *
        siftedMass (residueClassUpTo M q (unitResidue q a))
          (fun m : ℕ ↦ (m : ℝ)) (badPrimeSet P)) ≤
        ∑ a : (ZMod q)ˣ,
          (restrictedRootMin q hodd a : ℝ) * Xmain := by
      apply Finset.sum_le_sum
      intro a ha
      exact mul_le_mul_of_nonneg_left (hclass a) (hroot0 a)
    _ = Xmain * ∑ a : (ZMod q)ˣ,
        (restrictedRootMin q hodd a : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      ring
    _ = Xmain * (((q : ℝ) * (q.totient : ℝ)) /
        ((2 ^ q.primeFactors.card : ℕ) : ℝ)) := by
      rw [sum_restrictedRootMin_real hsq hodd]

end Erdos394
