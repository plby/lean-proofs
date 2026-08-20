/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.UpperSquarefreePrefix
import ErdosProblems.Erdos446.UpperPowerfulReduction

/-!
# Erdős Problem 446: squarefree fibers after powerful-part removal

For a fixed divisor `f` of the powerful part, put `v = y / f`.  An exact
witness `y < f*g ≤ 2y` has `v < g ≤ 2v+1`.  Thus it is either in the
ordinary dyadic divisor window `(v,2v]`, or it is the single endpoint
`2v+1`.  This file records that rounding step as a literal finite cover.
-/

namespace Erdos446

open Finset
open scoped BigOperators

noncomputable section

local instance powerfulFiberCoverDecidable :
    DecidablePred Erdos469.Powerful := Classical.decPred _

/-- The genuinely occurring small powerful parts.  Keeping this predicate in
the indexing set is essential: its reciprocal divisor-weighted mass is
uniformly bounded. -/
def smallPowerfulParts (Q : ℕ) : Finset ℕ :=
  (Finset.Icc 1 Q).filter Erdos469.Powerful

/-- Filtered version of the canonical powerful/squarefree injection. -/
theorem card_smallPowerfulDivisorPrefix_le_powerfulFibers
    {X y z Q : ℕ} :
    ((positiveDivisorPrefixSet X y z).filter fun m ↦
        Erdos469.powerfulPart m ≤ Q).card ≤
      ∑ q ∈ smallPowerfulParts Q,
        (squarefreeCofactorFiber X y z q).card := by
  let s := (positiveDivisorPrefixSet X y z).filter fun m ↦
    Erdos469.powerfulPart m ≤ Q
  let t := (smallPowerfulParts Q).sigma fun q ↦
    squarefreeCofactorFiber X y z q
  let φ : ℕ → Σ q : ℕ, ℕ := fun m ↦
    ⟨Erdos469.powerfulPart m, Erdos469.squarefreePart m⟩
  have hmaps : ∀ m ∈ s, φ m ∈ t := by
    intro m hm
    change m ∈ (positiveDivisorPrefixSet X y z).filter (fun m ↦
      Erdos469.powerfulPart m ≤ Q) at hm
    rw [Finset.mem_filter] at hm
    have hmpos := positiveDivisorPrefixSet_member_pos hm.1
    change φ m ∈ (smallPowerfulParts Q).sigma (fun q ↦
      squarefreeCofactorFiber X y z q)
    rw [Finset.mem_sigma]
    refine ⟨?_, squarefreePart_mem_squarefreeCofactorFiber hm.1 hm.2⟩
    rw [smallPowerfulParts, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨(Erdos469.powerfulPart_pos_and_squarefreePart_pos hmpos).1,
      hm.2⟩, Erdos469.powerfulPart_powerful m⟩
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
    _ = ∑ q ∈ smallPowerfulParts Q,
        (squarefreeCofactorFiber X y z q).card := by
      change ((smallPowerfulParts Q).sigma fun q ↦
        squarefreeCofactorFiber X y z q).card = _
      rw [Finset.card_sigma]

/-- Exact first reduction with the small sum restricted to powerful `q` and
the large contribution kept as its literal finite set. -/
theorem divisorPrefixCount_le_largePowerfulCard_add_powerfulFibers
    {X y z Q : ℕ} :
    divisorPrefixCount X y z ≤
      1 + (largePowerfulDivisorPrefix X y z Q).card +
        ∑ q ∈ smallPowerfulParts Q,
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
  have hsmall := card_smallPowerfulDivisorPrefix_le_powerfulFibers
    (X := X) (y := y) (z := z) (Q := Q)
  rw [← card_divisorPrefixSet]
  omega

/-- The two pieces associated with one divisor `f` of the powerful part. -/
def squarefreeCofactorDivisorCover (X y q f : ℕ) : Finset ℕ :=
  squarefreeDivisorPrefixSet (X / q + 1) (y / f) (2 * (y / f)) ∪
    multiplePrefix (X / q + 1) (2 * (y / f) + 1)

theorem squarefreeCofactorFiber_subset_divisorCovers
    {X y q : ℕ} (hq : 0 < q) :
    squarefreeCofactorFiber X y (2 * y) q ⊆
      q.divisors.biUnion (squarefreeCofactorDivisorCover X y q) := by
  intro a ha
  rw [squarefreeCofactorFiber, Finset.mem_filter] at ha
  obtain ⟨haRange, haSq, hqaX, f, hf, g, hg, hyfg, hfg⟩ := ha
  have hfpos : 0 < f := Nat.pos_of_mem_divisors hf
  have hapos : 0 < a := by
    exact Nat.pos_of_ne_zero (Nat.mem_divisors.mp hg).2
  have haN : a < X / q + 1 := by
    apply Nat.lt_succ_of_le
    apply (Nat.le_div_iff_mul_le hq).2
    simpa [Nat.mul_comm] using (Nat.le_of_lt hqaX)
  have hvg : y / f < g := by
    rw [Nat.div_lt_iff_lt_mul hfpos]
    simpa [Nat.mul_comm] using hyfg
  have hylt : y < (y / f + 1) * f := by
    apply (Nat.div_lt_iff_lt_mul hfpos).1
    exact Nat.lt_succ_self _
  have hgle : g ≤ 2 * (y / f) + 1 := by
    nlinarith
  rw [Finset.mem_biUnion]
  refine ⟨f, hf, ?_⟩
  rw [squarefreeCofactorDivisorCover, Finset.mem_union]
  by_cases hgmain : g ≤ 2 * (y / f)
  · apply Or.inl
    rw [squarefreeDivisorPrefixSet, Finset.mem_filter]
    refine ⟨Finset.mem_range.mpr haN, haSq, ?_⟩
    rw [divisorCountIoc, Finset.card_pos]
    refine ⟨g, Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hvg, hgmain⟩, ?_⟩⟩
    exact Nat.dvd_of_mem_divisors hg
  · apply Or.inr
    have hgeq : g = 2 * (y / f) + 1 := by omega
    rw [multiplePrefix, Finset.mem_filter]
    exact ⟨Finset.mem_range.mpr haN,
      hgeq ▸ Nat.dvd_of_mem_divisors hg⟩

/-- Cardinality form of the exact divisor cover.  The singleton rounding
piece is bounded by the elementary multiple count. -/
theorem card_squarefreeCofactorFiber_le_divisorCoverSum
    {X y q : ℕ} (hq : 0 < q) :
    (squarefreeCofactorFiber X y (2 * y) q).card ≤
      ∑ f ∈ q.divisors,
        (squarefreeDivisorPrefixCount (X / q + 1)
            (y / f) (2 * (y / f)) +
          ((X / q + 1) / (2 * (y / f) + 1) + 1)) := by
  calc
    (squarefreeCofactorFiber X y (2 * y) q).card ≤
        (q.divisors.biUnion
          (squarefreeCofactorDivisorCover X y q)).card :=
      Finset.card_le_card (squarefreeCofactorFiber_subset_divisorCovers hq)
    _ ≤ ∑ f ∈ q.divisors,
          (squarefreeCofactorDivisorCover X y q f).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ f ∈ q.divisors,
        (squarefreeDivisorPrefixCount (X / q + 1)
            (y / f) (2 * (y / f)) +
          ((X / q + 1) / (2 * (y / f) + 1) + 1)) := by
      apply Finset.sum_le_sum
      intro f hf
      have hden : 0 < 2 * (y / f) + 1 := by omega
      calc
        (squarefreeCofactorDivisorCover X y q f).card ≤
            (squarefreeDivisorPrefixSet (X / q + 1)
                (y / f) (2 * (y / f))).card +
              (multiplePrefix (X / q + 1)
                (2 * (y / f) + 1)).card := by
          unfold squarefreeCofactorDivisorCover
          exact Finset.card_union_le _ _
        _ ≤ (squarefreeDivisorPrefixCount (X / q + 1)
                (y / f) (2 * (y / f)) +
              ((X / q + 1) / (2 * (y / f) + 1) + 1)) := by
          rw [card_squarefreeDivisorPrefixSet]
          gcongr
          exact card_multiplePrefix_le _ _ hden

/-- Uniform real-valued estimate for one squarefree cofactor fiber, assuming
the explicit cutoff conditions at every divisor of `q`.  The factor `6`
consists of four main dyadic slopes, one affine-base absorption, and one
rounding-endpoint absorption. -/
theorem exists_pos_squarefreeCofactorFiber_le_targetDenominator :
    ∃ K : ℝ, 0 < K ∧ ∀ Y X q : ℕ, ∀ M : ℕ → ℕ,
      2 ≤ Y → 0 < q →
      (∀ f ∈ q.divisors,
        let v := Y / f
        let N := X / q + 1
        1 ≤ v ∧ v ≤ Y ∧
        (Y : ℝ) ^ (2 / 3 : ℝ) ≤ (v : ℝ) ∧
        4 * v ≤ M f ∧
        (Y : ℝ) ^ (2 / 3 : ℝ) ≤ (M f / (4 * v) : ℕ) ∧
        ((2 * v + 1 : ℕ) : ℝ) ≤
          K * fordVariableDenominatorSum Y (2 * Y) * (M f : ℝ) ∧
        2 * (M f : ℝ) ≤
          K * fordVariableDenominatorSum Y (2 * Y) * (N : ℝ) ∧
        (((N / (2 * v + 1) : ℕ) + 1 : ℕ) : ℝ) ≤
          K * fordVariableDenominatorSum Y (2 * Y) * (N : ℝ)) →
      ((squarefreeCofactorFiber X Y (2 * Y) q).card : ℝ) ≤
        6 * K * fordVariableDenominatorSum Y (2 * Y) *
          (X / q + 1 : ℕ) * (q.divisors.card : ℝ) := by
  obtain ⟨K, hK, hprefix⟩ :=
    exists_pos_squarefreeDivisorPrefix_le_affine_targetDenominator
  refine ⟨K, hK, fun Y X q M hY hq hnum ↦ ?_⟩
  let V : ℝ := fordVariableDenominatorSum Y (2 * Y)
  let N : ℕ := X / q + 1
  have hcover := card_squarefreeCofactorFiber_le_divisorCoverSum
    (X := X) (y := Y) hq
  calc
    ((squarefreeCofactorFiber X Y (2 * Y) q).card : ℝ) ≤
        ((∑ f ∈ q.divisors,
          (squarefreeDivisorPrefixCount N (Y / f) (2 * (Y / f)) +
            (N / (2 * (Y / f) + 1) + 1)) : ℕ) : ℝ) := by
      exact_mod_cast hcover
    _ = ∑ f ∈ q.divisors, (
          ((squarefreeDivisorPrefixCount N (Y / f)
              (2 * (Y / f)) : ℕ) : ℝ) +
            ((N / (2 * (Y / f) + 1) + 1 : ℕ) : ℝ)) := by
      push_cast
      rfl
    _ ≤ ∑ f ∈ q.divisors, 6 * K * V * (N : ℝ) := by
      apply Finset.sum_le_sum
      intro f hf
      obtain ⟨hv, hvY, hvscale, hMv, hscale, hendpoint,
          hMabsorb, hendabsorb⟩ := hnum f hf
      have hpre := hprefix Y (Y / f) (M f) N hY hv hvY
        hvscale hMv hscale hendpoint
      have hpre' :
          (squarefreeDivisorPrefixCount N (Y / f)
              (2 * (Y / f)) : ℝ) ≤
            5 * K * V * (N : ℝ) := by
        dsimp [V] at hpre hMabsorb ⊢
        linarith
      dsimp [V] at hendabsorb ⊢
      linarith
    _ = 6 * K * fordVariableDenominatorSum Y (2 * Y) *
          (X / q + 1 : ℕ) * (q.divisors.card : ℝ) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      dsimp [V, N]
      ring

end

end Erdos446
