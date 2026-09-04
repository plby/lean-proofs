import ErdosProblems.Erdos394.ShiftedRootLower

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Sieve upper bound for primes in a finite set of bad unit classes
-/

open Nat Finset

namespace Erdos394

noncomputable local instance badPrimeSieveUnitsFintype (q : ℕ) :
    Fintype (ZMod q)ˣ := Fintype.ofFinite _

/-- Primes in the half-open block `(A,U]`. -/
def largePrimeInterval (A U : ℕ) : Finset ℕ := U.primesLE \ A.primesLE

lemma mem_largePrimeInterval_iff {A U ell : ℕ} :
    ell ∈ largePrimeInterval A U ↔ A < ell ∧ ell ≤ U ∧ ell.Prime := by
  unfold largePrimeInterval
  simp only [Finset.mem_sdiff, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨hle, hp⟩, hnot⟩
    exact ⟨by
      by_contra h
      exact hnot ⟨Nat.le_of_not_gt h, hp⟩, hle, hp⟩
  · rintro ⟨hA, hU, hp⟩
    exact ⟨⟨hU, hp⟩, fun h ↦ (not_le_of_gt hA) h.1⟩

/-- Weighted prime mass in a prescribed finite set of global unit classes. -/
noncomputable def primeBadUnitWeightedMass
    (A U q : ℕ) (B : Finset (ZMod q)ˣ) : ℝ :=
  ∑ ell ∈ largePrimeInterval A U,
    if hcop : ell.Coprime q then
      if ZMod.unitOfCoprime ell hcop ∈ B then (ell : ℝ) else 0
    else 0

/-- The bad-class prime mass is dominated by the generic weighted sifted mass
with the indicator of `B` as its unit-class weight. -/
theorem primeBadUnitWeightedMass_le_unitWeightedSiftedMass
    (A U q : ℕ) (S : Finset ℕ) (B : Finset (ZMod q)ˣ)
    (hfree : ∀ ell ∈ largePrimeInterval A U, badPrimeSet S ell = ∅) :
    primeBadUnitWeightedMass A U q B ≤
      unitWeightedSiftedMass S U q
        (fun u ↦ if u ∈ B then (1 : ℝ) else 0) := by
  classical
  let f : ℕ → ℝ := fun ell ↦
    if hellpos : 0 < ell then
      if hcop : ell.Coprime q then
        if badPrimeSet S ell = ∅ then
          (ell : ℝ) * (if ZMod.unitOfCoprime ell hcop ∈ B then 1 else 0)
        else 0
      else 0
    else 0
  have hsub : largePrimeInterval A U ⊆ Finset.range (U + 1) := by
    intro ell hell
    exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (mem_largePrimeInterval_iff.mp hell).2.1)
  have heq : primeBadUnitWeightedMass A U q B =
      ∑ ell ∈ largePrimeInterval A U, f ell := by
    unfold primeBadUnitWeightedMass
    apply Finset.sum_congr rfl
    intro ell hell
    have hp := (mem_largePrimeInterval_iff.mp hell).2.2
    have hellpos := hp.pos
    dsimp [f]
    rw [if_pos hellpos]
    by_cases hcop : ell.Coprime q
    · simp only [dif_pos hcop, if_pos (hfree ell hell)]
      by_cases hB : ZMod.unitOfCoprime ell hcop ∈ B
      · simp [hB]
      · simp [hB]
    · simp only [dif_neg hcop]
  rw [heq]
  calc
    (∑ ell ∈ largePrimeInterval A U, f ell) ≤
        ∑ ell ∈ Finset.range (U + 1), f ell := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro ell hell hnot
      dsimp [f]
      split_ifs <;> positivity
    _ = unitWeightedSiftedMass S U q
        (fun u ↦ if u ∈ B then (1 : ℝ) else 0) := by
      unfold unitWeightedSiftedMass
      apply Finset.sum_congr rfl
      intro ell hell
      rfl

/-- Applying the uniform Brun progression bound to every bad unit class costs
exactly their cardinality. -/
theorem primeBadUnitWeightedMass_le_card_mul_brun
    (A U q : ℕ) (S : Finset ℕ) (B : Finset (ZMod q)ˣ)
    (hq : 0 < q) (hSprime : ∀ p ∈ S, p.Prime)
    (hcopS : ∀ p ∈ S, q.Coprime p)
    (hfree : ∀ ell ∈ largePrimeInterval A U, badPrimeSet S ell = ∅)
    (R : ℕ) (hR : Even R)
    (htail :
      (∑ p ∈ S, (1 / (p : ℝ))) ^ (R + 1) /
          ((R + 1).factorial : ℝ) ≤
        localEulerProduct S (fun p ↦ 1 / (p : ℝ))) :
    primeBadUnitWeightedMass A U q B ≤
      (B.card : ℝ) *
        (((U : ℝ) ^ 2 / (q : ℝ)) *
          localEulerProduct S (fun p ↦ 1 / (p : ℝ)) +
        (truncatedSubsets S R).card * (2 * (U : ℝ))) := by
  let : NeZero q := ⟨hq.ne'⟩
  let L : (ZMod q)ˣ → ℝ := fun u ↦ if u ∈ B then 1 else 0
  let Xmain : ℝ := ((U : ℝ) ^ 2 / (q : ℝ)) *
    localEulerProduct S (fun p ↦ 1 / (p : ℝ)) +
      (truncatedSubsets S R).card * (2 * (U : ℝ))
  have hmass := primeBadUnitWeightedMass_le_unitWeightedSiftedMass
    A U q S B hfree
  apply hmass.trans
  rw [unitWeightedSiftedMass_eq_sum_units S U q hq L]
  have hclass : ∀ a : (ZMod q)ˣ,
      siftedMass (residueClassUpTo U q (unitResidue q a))
          (fun m : ℕ ↦ (m : ℝ)) (badPrimeSet S) ≤ Xmain := by
    intro a
    have hsieve := primeSiftedMass_le_two_product_add_error
      S hSprime (M := U) (q := q) (h := unitResidue q a) (R := R)
      hq (ZMod.val_lt (a : ZMod q)) hcopS hR htail
    dsimp [Xmain]
    convert hsieve using 1 <;> ring
  have hX0 : 0 ≤ Xmain := by
    have hEuler0 : 0 ≤ localEulerProduct S (fun p ↦ 1 / (p : ℝ)) := by
      apply localEulerProduct_nonneg S (fun p ↦ 1 / (p : ℝ))
      · intro p hp; positivity
      · intro p hp
        have hp0 : (0 : ℝ) < p := by exact_mod_cast (hSprime p hp).pos
        exact (div_le_one hp0).2 (by exact_mod_cast (hSprime p hp).one_le)
    dsimp [Xmain]
    positivity
  calc
    (∑ a : (ZMod q)ˣ,
      L a * siftedMass (residueClassUpTo U q (unitResidue q a))
        (fun m : ℕ ↦ (m : ℝ)) (badPrimeSet S)) ≤
      ∑ a : (ZMod q)ˣ, L a * Xmain := by
        apply Finset.sum_le_sum
        intro a ha
        apply mul_le_mul_of_nonneg_left (hclass a)
        dsimp [L]
        split_ifs <;> positivity
    _ = ∑ a : (ZMod q)ˣ, if a ∈ B then Xmain else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      dsimp [L]
      split_ifs <;> ring
    _ = (B.card : ℝ) * Xmain := by
      rw [← Finset.sum_filter]
      have hfilter : (Finset.univ.filter (fun a : (ZMod q)ˣ ↦ a ∈ B)) = B := by
        ext a
        simp
      rw [hfilter]
      simp
    _ = (B.card : ℝ) *
        (((U : ℝ) ^ 2 / (q : ℝ)) *
          localEulerProduct S (fun p ↦ 1 / (p : ℝ)) +
        (truncatedSubsets S R).card * (2 * (U : ℝ))) := by rfl

end Erdos394
