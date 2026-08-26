/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.ReducedCollision
import ErdosProblems.Erdos822.OuterCollisionPairs

/-!
# Fixed-cofactor collision fibers

For fixed cofactors, choose the least first outer prime occurring in a
collision.  Positivity of the primitive coefficients forces the associated
second prime to be least as well.  Thus the whole collision fiber embeds
into one ordered primitive prime-solution set.
-/

namespace Erdos822

theorem outerPrime_le_scale {x m p : ℕ}
    (hp : p ∈ outerPrimes x m) : p ≤ x := by
  have hp' := mem_outerPrimes_iff.mp hp
  exact hp'.2.1.trans (Nat.div_le_self _ _)

/-- Any nonempty fixed-cofactor collision fiber is contained in an ordered
primitive linear prime-solution set through a least first-coordinate base
point. -/
theorem exists_orderedLinearPrimeSolutions_cover_outerCollisionPairs
    {x m m' y : ℕ}
    (hm : 0 < m) (hm' : 0 < m')
    (hlarge : ∀ p ∈ outerPrimes x m, m < p)
    (hlarge' : ∀ p ∈ outerPrimes x m', m' < p)
    (hy : ∀ p ∈ outerPrimes x m, y < p)
    (hy' : ∀ p ∈ outerPrimes x m', y < p)
    (hne : (outerCollisionPairs x m m').Nonempty) :
    ∃ q q' : ℕ,
      (q, q') ∈ outerCollisionPairs x m m' ∧
      outerCollisionPairs x m m' ⊆
        orderedLinearPrimeSolutions
          (reducedCollisionLeft m m') (reducedCollisionRight m m')
          q q' x y := by
  classical
  let P : Finset ℕ := (outerCollisionPairs x m m').image Prod.fst
  have hPne : P.Nonempty := by
    obtain ⟨z, hz⟩ := hne
    exact ⟨z.1, Finset.mem_image.mpr ⟨z, hz, rfl⟩⟩
  let q : ℕ := P.min' hPne
  have hqP : q ∈ P := Finset.min'_mem P hPne
  obtain ⟨z, hz, hzq⟩ := Finset.mem_image.mp hqP
  rcases z with ⟨q0, q'⟩
  change q0 = q at hzq
  subst q0
  refine ⟨q, q', hz, ?_⟩
  intro z hzcol
  rcases z with ⟨p, p'⟩
  rw [mem_outerCollisionPairs_iff] at hz hzcol
  rw [mem_orderedLinearPrimeSolutions_iff]
  have hpP : p ∈ P := Finset.mem_image.mpr
    ⟨(p, p'), by
      rw [mem_outerCollisionPairs_iff]
      exact hzcol, rfl⟩
  have hqp : q ≤ p := Finset.min'_le P p hpP
  have hApos := reducedCollisionLeft_pos hm hm'
  have hBpos := reducedCollisionRight_pos hm hm'
  have hred := reduced_linear_eq_of_two_outer_collisions
    hzcol.1 hzcol.2.1 hz.1 hz.2.1 hm hm'
    (hlarge p hzcol.1) (hlarge' p' hzcol.2.1)
    (hlarge q hz.1) (hlarge' q' hz.2.1)
    hzcol.2.2 hz.2.2
  have hq'p' : q' ≤ p' := by
    by_contra hnot
    have hp'q' : p' < q' := by omega
    nlinarith
  refine ⟨hqp, outerPrime_le_scale hzcol.1,
    (mem_outerPrimes_iff.mp hzcol.1).2.2, hy p hzcol.1,
    hq'p', outerPrime_le_scale hzcol.2.1,
    (mem_outerPrimes_iff.mp hzcol.2.1).2.2, hy' p' hzcol.2.1, ?_⟩
  exact hred

/-- Consequently a fixed-cofactor collision fiber is bounded by one affine
prime-candidate set, with the base point supplied by the least collision. -/
theorem outerCollisionPairs_card_le_primeCandidates_of_nonempty
    {x m m' y : ℕ}
    (hm : 0 < m) (hm' : 0 < m')
    (hlarge : ∀ p ∈ outerPrimes x m, m < p)
    (hlarge' : ∀ p ∈ outerPrimes x m', m' < p)
    (hy : ∀ p ∈ outerPrimes x m, y < p)
    (hy' : ∀ p ∈ outerPrimes x m', y < p)
    (hne : (outerCollisionPairs x m m').Nonempty) :
    ∃ q q' : ℕ,
      (outerCollisionPairs x m m').card ≤
        (twoAffinePrimeCandidates
          (reducedCollisionRight m m') q
          (reducedCollisionLeft m m') q' (x + 1) y).card := by
  obtain ⟨q, q', _hbase, hsub⟩ :=
    exists_orderedLinearPrimeSolutions_cover_outerCollisionPairs
      hm hm' hlarge hlarge' hy hy' hne
  refine ⟨q, q', (Finset.card_le_card hsub).trans ?_⟩
  exact card_orderedLinearPrimeSolutions_le_primeCandidates
    (reducedCollisionLeft_pos hm hm')
    (reducedCollisionRight_pos hm hm')
    (reducedCollision_coprime hm hm')

/-- Scale-sensitive version of the fiber cover.  The parameter interval is
cut down by the first primitive slope and the actual outer-prime ceilings
instead of by the ambient scale. -/
theorem outerCollisionPairs_card_le_primeCandidates_div_of_nonempty
    {x m m' y : ℕ}
    (hm : 0 < m) (hm' : 0 < m')
    (hlarge : ∀ p ∈ outerPrimes x m, m < p)
    (hlarge' : ∀ p ∈ outerPrimes x m', m' < p)
    (hy : ∀ p ∈ outerPrimes x m, y < p)
    (hy' : ∀ p ∈ outerPrimes x m', y < p)
    (hne : (outerCollisionPairs x m m').Nonempty) :
    ∃ q q' : ℕ,
      let B := reducedCollisionRight m m'
      let A := reducedCollisionLeft m m'
      let U := max (x / m) (x / m')
      (q, q') ∈ outerCollisionPairs x m m' ∧
        (outerCollisionPairs x m m').card ≤
          (twoAffinePrimeCandidates B q A q' (U / B + 1) y).card := by
  obtain ⟨q, q', hbase, hsub⟩ :=
    exists_orderedLinearPrimeSolutions_cover_outerCollisionPairs
      hm hm' hlarge hlarge' hy hy' hne
  refine ⟨q, q', hbase, ?_⟩
  let U := max (x / m) (x / m')
  have hsubU :
      outerCollisionPairs x m m' ⊆
        orderedLinearPrimeSolutions
          (reducedCollisionLeft m m') (reducedCollisionRight m m')
          q q' U y := by
    intro z hz
    rcases z with ⟨p, p'⟩
    have hzold := hsub hz
    rw [mem_orderedLinearPrimeSolutions_iff] at hzold ⊢
    rw [mem_outerCollisionPairs_iff] at hz
    refine ⟨hzold.1, ?_, hzold.2.2.1, hzold.2.2.2.1,
      hzold.2.2.2.2.1, ?_, hzold.2.2.2.2.2.2.1,
      hzold.2.2.2.2.2.2.2.1, hzold.2.2.2.2.2.2.2.2⟩
    · dsimp [U]
      exact (mem_outerPrimes_iff.mp hz.1).2.1.trans
        (Nat.le_max_left _ _)
    · dsimp [U]
      exact (mem_outerPrimes_iff.mp hz.2.1).2.1.trans
        (Nat.le_max_right _ _)
  calc
    (outerCollisionPairs x m m').card ≤
        (orderedLinearPrimeSolutions
          (reducedCollisionLeft m m') (reducedCollisionRight m m')
          q q' U y).card := Finset.card_le_card hsubU
    _ ≤ (twoAffinePrimeCandidates
          (reducedCollisionRight m m') q
          (reducedCollisionLeft m m') q'
          (U / reducedCollisionRight m m' + 1) y).card :=
      card_orderedLinearPrimeSolutions_le_primeCandidates_div
        (reducedCollisionLeft_pos hm hm')
        (reducedCollisionRight_pos hm hm')
        (reducedCollision_coprime hm hm')

/-- The fixed-cofactor collision fiber satisfies the slope-aware Rosser
upper-main bound, with its least collision supplying the two large prime
constant terms. -/
theorem outerCollisionPairs_card_le_slopeAware_upperMain_of_nonempty
    {x m m' z y S : ℕ}
    (hm : 0 < m) (hm' : 0 < m')
    (hlarge : ∀ p ∈ outerPrimes x m, m < p)
    (hlarge' : ∀ p ∈ outerPrimes x m', m' < p)
    (hy : ∀ p ∈ outerPrimes x m, y < p)
    (hy' : ∀ p ∈ outerPrimes x m', y < p)
    (hz : 2 ≤ z) (hyTwo : 1 < y) (hS : 1 ≤ S)
    (hne : (outerCollisionPairs x m m').Nonempty) :
    ∃ q q' : ℕ,
      let A := reducedCollisionLeft m m'
      let B := reducedCollisionRight m m'
      let P := ascendingSlopeAwareSievePrimes B A z (y + 1)
      let D := y ^ S
      let stop := Erdos851.FiniteCombinatorialSieve.rosserStoppingPredicate 100 D
      ((outerCollisionPairs x m m').card : ℝ) ≤
        ((x + 1 : ℕ) : ℝ) *
          Erdos851.FiniteCombinatorialSieve.upperMainTerm stop
            (twoAffineNu B q A q') P + (D : ℝ) ^ 2 := by
  obtain ⟨q, q', hbase, hsub⟩ :=
    exists_orderedLinearPrimeSolutions_cover_outerCollisionPairs
      hm hm' hlarge hlarge' hy hy' hne
  refine ⟨q, q', ?_⟩
  dsimp only
  have hqPrime : q.Prime := (mem_outerPrimes_iff.mp
    (mem_outerCollisionPairs_iff.mp hbase).1).2.2
  have hq'Prime : q'.Prime := (mem_outerPrimes_iff.mp
    (mem_outerCollisionPairs_iff.mp hbase).2.1).2.2
  calc
    ((outerCollisionPairs x m m').card : ℝ) ≤
        ((orderedLinearPrimeSolutions
          (reducedCollisionLeft m m') (reducedCollisionRight m m')
          q q' x y).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    _ ≤ ((x + 1 : ℕ) : ℝ) *
          Erdos851.FiniteCombinatorialSieve.upperMainTerm
            (Erdos851.FiniteCombinatorialSieve.rosserStoppingPredicate
              100 (y ^ S))
            (twoAffineNu (reducedCollisionRight m m') q
              (reducedCollisionLeft m m') q')
            (ascendingSlopeAwareSievePrimes
              (reducedCollisionRight m m')
              (reducedCollisionLeft m m') z (y + 1)) +
          ((y ^ S : ℕ) : ℝ) ^ 2 := by
      exact card_orderedLinearPrimeSolutions_le_slopeAware_upperMain
        (reducedCollisionLeft_pos hm hm')
        (reducedCollisionRight_pos hm hm')
        (reducedCollision_coprime hm hm')
        hqPrime hq'Prime
        (hy q (mem_outerCollisionPairs_iff.mp hbase).1)
        (hy' q' (mem_outerCollisionPairs_iff.mp hbase).2.1)
        hz hyTwo hS

/-- For a fixed cofactor the outer linear form is injective in the new
prime, so the diagonal cofactor fiber contributes exactly one pair per outer
prime. -/
theorem outerCollisionPairs_self_card_eq_outerPrimes_card
    {x m : ℕ} (hm : 0 < m)
    (hlarge : ∀ p ∈ outerPrimes x m, m < p) :
    (outerCollisionPairs x m m).card = (outerPrimes x m).card := by
  classical
  have hset :
      outerCollisionPairs x m m =
        (outerPrimes x m).image fun p ↦ (p, p) := by
    ext z
    rcases z with ⟨p, p'⟩
    rw [mem_outerCollisionPairs_iff]
    constructor
    · rintro ⟨hp, hp', hcollision⟩
      have hlin := outer_collision_linear_eq_int hp hp' hm hm
        (hlarge p hp) (hlarge p' hp') hcollision
      have hcoef : (0 : ℤ) < shiftedTotient m := by
        exact_mod_cast shiftedTotient_pos_of_pos hm
      have hpp' : p = p' := by
        have : (p : ℤ) = p' := by nlinarith
        exact_mod_cast this
      subst p'
      exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
    · intro hz
      rw [Finset.mem_image] at hz
      obtain ⟨q, hq, hqeq⟩ := hz
      injection hqeq with hp hp'
      subst p
      subst p'
      exact ⟨hq, hq, rfl⟩
  rw [hset, Finset.card_image_of_injective]
  intro p p' h
  exact (Prod.ext_iff.mp h).1

end Erdos822
