/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.Counting
import ErdosProblems.Erdos469

/-!
# Erdős Problem 446: removal of the powerful part

This is the first, entirely finite, step in Ford's Lemma 3.2.  We use the
canonical factorization

`m = powerfulPart m * squarefreePart m`,

where the two factors are coprime, the first is powerful (every prime occurs
to exponent at least two), and the second is squarefree.  The divisor event
then splits exactly into divisors of the two factors.

The main result `divisorPrefixCount_le_powerfulTail_add_squarefreeFibers`
does two things without an analytic hypothesis:

* the integers whose powerful part exceeds `Q` are covered by the multiples
  of the finitely many powerful `q` in `(Q,X)`;
* every remaining integer is injected into a pair `(q,a)`, with `q ≤ Q`
  powerful and `a` squarefree, and the original divisor witness is split as
  `f*g`, `f ∣ q`, `g ∣ a`.

Thus no multiplicity is lost in the squarefree reduction.  Later sieve and
cluster estimates may be applied separately to each displayed finite fiber.
-/

namespace Erdos446

open Finset
open scoped BigOperators

noncomputable section

local instance : DecidablePred Erdos469.Powerful := Classical.decPred _

/-- The finite set counted by `divisorPrefixCount`. -/
def divisorPrefixSet (X y z : ℕ) : Finset ℕ :=
  (Finset.range X).filter fun m ↦ 0 < divisorCountIoc y z m

@[simp] theorem card_divisorPrefixSet (X y z : ℕ) :
    (divisorPrefixSet X y z).card = divisorPrefixCount X y z :=
  rfl

/-- Positive multiples of `q` below `X`. -/
def multiplePrefix (X q : ℕ) : Finset ℕ :=
  (Finset.range X).filter fun m ↦ q ∣ m

/-- Positive multiples of `q` below `X`. -/
def positiveMultiplePrefix (X q : ℕ) : Finset ℕ :=
  (multiplePrefix X q).erase 0

/-- Powerful integers in the half-open interval `(Q,X)`. -/
def powerfulShell (X Q : ℕ) : Finset ℕ :=
  (Finset.Ioo Q X).filter Erdos469.Powerful

/-- The positive part of the finite divisor event.  The residue `0` is kept
separate because every positive integer divides it. -/
def positiveDivisorPrefixSet (X y z : ℕ) : Finset ℕ :=
  (divisorPrefixSet X y z).erase 0

/-- The positive part of the divisor event whose canonical powerful part
exceeds `Q`. -/
def largePowerfulDivisorPrefix (X y z Q : ℕ) : Finset ℕ :=
  (positiveDivisorPrefixSet X y z).filter fun m ↦
    Q < Erdos469.powerfulPart m

/-- A squarefree cofactor occurring above the fixed powerful part `q`.

The last four conjuncts retain the exact split divisor witness.  Writing it
this way (rather than introducing rounded endpoints `y/f`) avoids every
floor/ceiling error in the finite reduction. -/
def squarefreeCofactorFiber (X y z q : ℕ) : Finset ℕ :=
  (Finset.range X).filter fun a ↦
    Squarefree a ∧ q * a < X ∧
      ∃ f ∈ q.divisors, ∃ g ∈ a.divisors,
        y < f * g ∧ f * g ≤ z

theorem positiveDivisorPrefixSet_member_pos {X y z m : ℕ}
    (hm : m ∈ positiveDivisorPrefixSet X y z) :
    0 < m := by
  rw [positiveDivisorPrefixSet, Finset.mem_erase] at hm
  exact Nat.pos_of_ne_zero hm.1

theorem largePowerfulDivisorPrefix_subset_biUnion
    {X y z Q : ℕ} :
    largePowerfulDivisorPrefix X y z Q ⊆
      (powerfulShell X Q).biUnion (positiveMultiplePrefix X) := by
  intro m hm
  rw [largePowerfulDivisorPrefix, Finset.mem_filter] at hm
  have hmpos := positiveDivisorPrefixSet_member_pos hm.1
  let q := Erdos469.powerfulPart m
  have hqpos : 0 < q :=
    (Erdos469.powerfulPart_pos_and_squarefreePart_pos hmpos).1
  have hqle : q ≤ m := Erdos469.powerfulPart_le hmpos
  have hmX : m < X := by
    have hm' := hm.1
    rw [positiveDivisorPrefixSet, Finset.mem_erase] at hm'
    exact Finset.mem_range.mp (Finset.mem_filter.mp hm'.2).1
  rw [Finset.mem_biUnion]
  refine ⟨q, ?_, ?_⟩
  · rw [powerfulShell, Finset.mem_filter, Finset.mem_Ioo]
    exact ⟨⟨hm.2, hqle.trans_lt hmX⟩,
      Erdos469.powerfulPart_powerful m⟩
  · rw [positiveMultiplePrefix, Finset.mem_erase]
    refine ⟨hmpos.ne', ?_⟩
    rw [multiplePrefix, Finset.mem_filter]
    exact ⟨Finset.mem_range.mpr hmX, Erdos469.powerfulPart_dvd hmpos⟩

/-- There are at most `X/q + 1` multiples of a positive `q` below `X`.
The extra endpoint is convenient in the subsequent reciprocal tail sum. -/
theorem card_multiplePrefix_le (X q : ℕ) (hq : 0 < q) :
    (multiplePrefix X q).card ≤ X / q + 1 := by
  let φ : ℕ → ℕ := fun m ↦ m / q
  have hmaps : ∀ m ∈ multiplePrefix X q, φ m ∈ Finset.range (X / q + 1) := by
    intro m hm
    rw [multiplePrefix, Finset.mem_filter] at hm
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le
      (Nat.div_le_div_right (Finset.mem_range.mp hm.1).le)
  have hinj : Set.InjOn φ (multiplePrefix X q) := by
    intro a ha b hb hab
    have ha' : a ∈ multiplePrefix X q := ha
    have hb' : b ∈ multiplePrefix X q := hb
    rw [multiplePrefix, Finset.mem_filter] at ha' hb'
    have haeq : q * (a / q) = a := by
      simpa [Nat.mul_comm] using (Nat.div_mul_cancel ha'.2)
    have hbeq : q * (b / q) = b := by
      simpa [Nat.mul_comm] using (Nat.div_mul_cancel hb'.2)
    change a / q = b / q at hab
    rw [← haeq, ← hbeq, hab]
  simpa using Finset.card_le_card_of_injOn φ hmaps hinj

/-- Removing the zero residue gives the sharp floor bound for positive
multiples. -/
theorem card_positiveMultiplePrefix_le (X q : ℕ) (hq : 0 < q) :
    (positiveMultiplePrefix X q).card ≤ X / q := by
  let φ : ℕ → ℕ := fun m ↦ m / q
  have hmaps : ∀ m ∈ positiveMultiplePrefix X q,
      φ m ∈ Finset.Icc 1 (X / q) := by
    intro m hm
    rw [positiveMultiplePrefix, Finset.mem_erase,
      multiplePrefix, Finset.mem_filter] at hm
    have hmpos : 0 < m := Nat.pos_of_ne_zero hm.1
    have hqle : q ≤ m := Nat.le_of_dvd hmpos hm.2.2
    rw [Finset.mem_Icc]
    exact ⟨Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt (Nat.div_pos hqle hq)),
      Nat.div_le_div_right (Finset.mem_range.mp hm.2.1).le⟩
  have hinj : Set.InjOn φ (positiveMultiplePrefix X q) := by
    intro a ha b hb hab
    have ha' : a ∈ positiveMultiplePrefix X q := ha
    have hb' : b ∈ positiveMultiplePrefix X q := hb
    rw [positiveMultiplePrefix, Finset.mem_erase,
      multiplePrefix, Finset.mem_filter] at ha' hb'
    have haeq : q * (a / q) = a := by
      simpa [Nat.mul_comm] using (Nat.div_mul_cancel ha'.2.2)
    have hbeq : q * (b / q) = b := by
      simpa [Nat.mul_comm] using (Nat.div_mul_cancel hb'.2.2)
    change a / q = b / q at hab
    rw [← haeq, ← hbeq, hab]
  have hcard := Finset.card_le_card_of_injOn φ hmaps hinj
  simpa [Nat.card_Icc] using hcard

/-- Explicit finite squarefull/powerful tail bound. -/
theorem card_largePowerfulDivisorPrefix_le
    {X y z Q : ℕ} :
    (largePowerfulDivisorPrefix X y z Q).card ≤
      ∑ q ∈ powerfulShell X Q, X / q := by
  calc
    (largePowerfulDivisorPrefix X y z Q).card ≤
        ((powerfulShell X Q).biUnion (positiveMultiplePrefix X)).card :=
      Finset.card_le_card largePowerfulDivisorPrefix_subset_biUnion
    _ ≤ ∑ q ∈ powerfulShell X Q,
        (positiveMultiplePrefix X q).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ q ∈ powerfulShell X Q, X / q := by
      apply Finset.sum_le_sum
      intro q hq
      have hq' : q ∈ powerfulShell X Q := hq
      have hqpos : 0 < q := by
        have := (Finset.mem_Ioo.mp
          (Finset.mem_filter.mp hq').1).1
        omega
      exact card_positiveMultiplePrefix_le X q hqpos

/-- The powerful exceptional set has a genuine uniform power saving.  This
is the analytic ``squarefull removal'' used before Ford's squarefree shell
argument.  The exponent `7/16` is more than sufficient for the customary
choice `Q = y^(1/10)`. -/
theorem card_largePowerfulDivisorPrefix_real_le_dirichletTail
    {X y z Q : ℕ} (hQ : 0 < Q) :
    ((largePowerfulDivisorPrefix X y z Q).card : ℝ) ≤
      (X : ℝ) * (Q : ℝ) ^ (-(7 / 16 : ℝ)) *
        Erdos469.powerfulNineSixteenthsMass := by
  have hcard := card_largePowerfulDivisorPrefix_le
    (X := X) (y := y) (z := z) (Q := Q)
  have hsub : powerfulShell X Q ⊆
      (Finset.Icc Q X).filter Erdos469.Powerful := by
    intro q hq
    rw [powerfulShell, Finset.mem_filter, Finset.mem_Ioo] at hq
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hq.1.1.le, hq.1.2.le⟩, hq.2⟩
  have hinv :
      (∑ q ∈ powerfulShell X Q, (q : ℝ)⁻¹) ≤
        (Q : ℝ) ^ (-(7 / 16 : ℝ)) *
          Erdos469.powerfulNineSixteenthsMass := by
    calc
      (∑ q ∈ powerfulShell X Q, (q : ℝ)⁻¹) ≤
          ∑ q ∈ (Finset.Icc Q X).filter Erdos469.Powerful,
            (q : ℝ)⁻¹ := by
        exact Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun _ _ _ ↦ inv_nonneg.mpr (Nat.cast_nonneg _))
      _ ≤ (Q : ℝ) ^ (-(7 / 16 : ℝ)) *
          Erdos469.powerfulNineSixteenthsMass :=
        Erdos469.sum_inv_powerful_Icc_le hQ
  calc
    ((largePowerfulDivisorPrefix X y z Q).card : ℝ) ≤
        ((∑ q ∈ powerfulShell X Q, X / q : ℕ) : ℝ) := by
      exact_mod_cast hcard
    _ = ∑ q ∈ powerfulShell X Q, ((X / q : ℕ) : ℝ) := by
      push_cast
      rfl
    _ ≤ ∑ q ∈ powerfulShell X Q,
        (X : ℝ) * (q : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro q hq
      simpa [div_eq_mul_inv] using
        (Nat.cast_div_le : ((X / q : ℕ) : ℝ) ≤
          (X : ℝ) / (q : ℝ))
    _ = (X : ℝ) *
        (∑ q ∈ powerfulShell X Q, (q : ℝ)⁻¹) := by
      rw [Finset.mul_sum]
    _ ≤ (X : ℝ) *
        ((Q : ℝ) ^ (-(7 / 16 : ℝ)) *
          Erdos469.powerfulNineSixteenthsMass) := by
      exact mul_le_mul_of_nonneg_left hinv (Nat.cast_nonneg X)
    _ = (X : ℝ) * (Q : ℝ) ^ (-(7 / 16 : ℝ)) *
        Erdos469.powerfulNineSixteenthsMass := by ring

/-- Split an exact divisor of two coprime positive factors. -/
theorem exists_divisor_split_of_dvd_mul
    {q a d : ℕ} (hq : 0 < q) (ha : 0 < a) (hd : d ∣ q * a) :
    ∃ f ∈ q.divisors, ∃ g ∈ a.divisors, d = f * g := by
  have hdmem : d ∈ (q * a).divisors :=
    Nat.mem_divisors.mpr ⟨hd, Nat.mul_ne_zero hq.ne' ha.ne'⟩
  rw [Nat.divisors_mul] at hdmem
  obtain ⟨f, hf, g, hg, hfg⟩ := Finset.mem_mul.mp hdmem
  exact ⟨f, hf, g, hg, hfg.symm⟩

/-- Every divisor-event integer with small powerful part supplies a member of
the corresponding squarefree cofactor fiber. -/
theorem squarefreePart_mem_squarefreeCofactorFiber
    {X y z Q m : ℕ}
    (hm : m ∈ positiveDivisorPrefixSet X y z)
    (hsmall : Erdos469.powerfulPart m ≤ Q) :
    Erdos469.squarefreePart m ∈
      squarefreeCofactorFiber X y z (Erdos469.powerfulPart m) := by
  have hmpos := positiveDivisorPrefixSet_member_pos hm
  have hparts := Erdos469.powerfulPart_pos_and_squarefreePart_pos hmpos
  have hprod := Erdos469.powerfulPart_mul_squarefreePart hmpos.ne'
  rw [squarefreeCofactorFiber, Finset.mem_filter]
  refine ⟨?_, Erdos469.squarefreePart_squarefree hmpos.ne', ?_, ?_⟩
  · have hm' := hm
    rw [positiveDivisorPrefixSet, Finset.mem_erase] at hm'
    have hmX : m < X :=
      Finset.mem_range.mp (Finset.mem_filter.mp hm'.2).1
    have hadvd : Erdos469.squarefreePart m ∣ m :=
      ⟨Erdos469.powerfulPart m,
        by rw [Nat.mul_comm, Erdos469.powerfulPart_mul_squarefreePart hmpos.ne']⟩
    exact Finset.mem_range.mpr
      ((Nat.le_of_dvd hmpos hadvd).trans_lt hmX)
  · have hm' := hm
    rw [positiveDivisorPrefixSet, Finset.mem_erase] at hm'
    simpa [hprod] using (Finset.mem_filter.mp hm'.2).1
  · have hm' := hm
    rw [positiveDivisorPrefixSet, Finset.mem_erase,
      divisorPrefixSet, Finset.mem_filter] at hm'
    rw [divisorCountIoc, Finset.card_pos] at hm'
    obtain ⟨d, hd⟩ := hm'.2.2
    rw [Finset.mem_filter] at hd
    obtain ⟨f, hf, g, hg, hfg⟩ :=
      exists_divisor_split_of_dvd_mul hparts.1 hparts.2
        (hprod.symm ▸ hd.2)
    refine ⟨f, hf, g, hg, ?_, ?_⟩
    · simpa [hfg] using (Finset.mem_Ioc.mp hd.1).1
    · simpa [hfg] using (Finset.mem_Ioc.mp hd.1).2

/-- The map `m ↦ (powerfulPart m, squarefreePart m)` is injective on
positive integers. -/
theorem powerfulSquarefreePair_injOn_positive :
    Set.InjOn
      (fun m : ℕ ↦
        (Erdos469.powerfulPart m, Erdos469.squarefreePart m))
      (Set.Ici 1 : Set ℕ) := by
  intro m hm n hn hpair
  have hmpos : 0 < m := hm
  have hnpos : 0 < n := hn
  have hq := congrArg Prod.fst hpair
  have ha := congrArg Prod.snd hpair
  change Erdos469.powerfulPart m = Erdos469.powerfulPart n at hq
  change Erdos469.squarefreePart m = Erdos469.squarefreePart n at ha
  calc
    m = Erdos469.powerfulPart m * Erdos469.squarefreePart m :=
      (Erdos469.powerfulPart_mul_squarefreePart hmpos.ne').symm
    _ = Erdos469.powerfulPart n * Erdos469.squarefreePart n := by
      rw [hq, ha]
    _ = n := Erdos469.powerfulPart_mul_squarefreePart hnpos.ne'

/-- The small-powerful-part contribution injects into the disjoint sigma
family of exact powerful parts and squarefree cofactor fibers. -/
theorem card_smallPowerfulDivisorPrefix_le_fibers
    {X y z Q : ℕ} :
    ((positiveDivisorPrefixSet X y z).filter fun m ↦
        Erdos469.powerfulPart m ≤ Q).card ≤
      ∑ q ∈ Finset.Icc 1 Q, (squarefreeCofactorFiber X y z q).card := by
  let s := (positiveDivisorPrefixSet X y z).filter fun m ↦
    Erdos469.powerfulPart m ≤ Q
  let t := (Finset.Icc 1 Q).sigma fun q ↦ squarefreeCofactorFiber X y z q
  let φ : ℕ → Σ q : ℕ, ℕ := fun m ↦
    ⟨Erdos469.powerfulPart m, Erdos469.squarefreePart m⟩
  have hmaps : ∀ m ∈ s, φ m ∈ t := by
    intro m hm
    change m ∈ (positiveDivisorPrefixSet X y z).filter (fun m ↦
      Erdos469.powerfulPart m ≤ Q) at hm
    rw [Finset.mem_filter] at hm
    have hmpos := positiveDivisorPrefixSet_member_pos hm.1
    change φ m ∈ (Finset.Icc 1 Q).sigma (fun q ↦
      squarefreeCofactorFiber X y z q)
    rw [Finset.mem_sigma]
    exact ⟨Finset.mem_Icc.mpr
        ⟨(Erdos469.powerfulPart_pos_and_squarefreePart_pos hmpos).1,
          hm.2⟩,
      squarefreePart_mem_squarefreeCofactorFiber hm.1 hm.2⟩
  have hinj : Set.InjOn φ s := by
    intro m hm n hn hmn
    apply powerfulSquarefreePair_injOn_positive
    · exact positiveDivisorPrefixSet_member_pos
        (Finset.mem_filter.mp hm).1
    · exact positiveDivisorPrefixSet_member_pos
        (Finset.mem_filter.mp hn).1
    · have hq : Erdos469.powerfulPart m =
          Erdos469.powerfulPart n := congrArg Sigma.fst hmn
      have ha : Erdos469.squarefreePart m =
          Erdos469.squarefreePart n := by
        simpa using congrArg (fun x ↦ x.2) hmn
      exact Prod.ext hq ha
  calc
    s.card ≤ t.card := Finset.card_le_card_of_injOn φ hmaps hinj
    _ = ∑ q ∈ Finset.Icc 1 Q, (squarefreeCofactorFiber X y z q).card := by
      change ((Finset.Icc 1 Q).sigma fun q ↦
        squarefreeCofactorFiber X y z q).card = _
      rw [Finset.card_sigma]

/-- Ford's exact first reduction, in finite prefix-count form.  The first sum
is the powerful tail; the second is a family of squarefree divisor problems
with no hidden endpoint rounding. -/
theorem divisorPrefixCount_le_powerfulTail_add_squarefreeFibers
    {X y z Q : ℕ} :
    divisorPrefixCount X y z ≤
      1 + (∑ q ∈ powerfulShell X Q, X / q) +
        ∑ q ∈ Finset.Icc 1 Q,
          (squarefreeCofactorFiber X y z q).card := by
  have hpartition :
      (positiveDivisorPrefixSet X y z).card =
        (largePowerfulDivisorPrefix X y z Q).card +
          ((positiveDivisorPrefixSet X y z).filter fun m ↦
            Erdos469.powerfulPart m ≤ Q).card := by
    have h := Finset.card_filter_add_card_filter_not
      (s := positiveDivisorPrefixSet X y z)
      (fun m ↦ Erdos469.powerfulPart m ≤ Q)
    have heq :
        (positiveDivisorPrefixSet X y z).filter (fun m ↦
            ¬ Erdos469.powerfulPart m ≤ Q) =
          largePowerfulDivisorPrefix X y z Q := by
      ext m
      simp [largePowerfulDivisorPrefix]
    rw [heq] at h
    omega
  have herase :
      (divisorPrefixSet X y z).card ≤
        (positiveDivisorPrefixSet X y z).card + 1 := by
    rw [positiveDivisorPrefixSet]
    by_cases hzero : 0 ∈ divisorPrefixSet X y z
    · rw [Finset.card_erase_add_one hzero]
    · simp [hzero]
  have hlarge := card_largePowerfulDivisorPrefix_le
    (X := X) (y := y) (z := z) (Q := Q)
  have hsmall := card_smallPowerfulDivisorPrefix_le_fibers
    (X := X) (y := y) (z := z) (Q := Q)
  rw [← card_divisorPrefixSet]
  omega

end

end Erdos446
