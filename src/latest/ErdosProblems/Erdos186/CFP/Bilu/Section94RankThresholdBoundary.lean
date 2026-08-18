/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.Section5SortedTail
import ErdosProblems.Erdos186.CFP.Bilu.Section9KernelAffineReduction

/-!
# Sections 5.5 and 9: rank and doubling-threshold boundary

This file records the strongest adapters available from the current APIs.

* Minimal-rank repair in Section 9 preserves every rank bound enjoyed by an
  initial admissible presentation.
* A real `rpow` doubling estimate implies the natural-cardinality threshold
  used by the current `Section5Theorem56` whenever the two constants have the
  required strict order.
* An affine slice of dimension below `d + 1` already bounds widths beginning
  at zero-based coordinate `d`.  This is the indexing needed by
  `SortedFsContainer`.

The source's general `2 ^ (d + 1 - delta)` branch requires the actual
generalized `2^n` affine-slice theorem.  The current theorem in
`Section5Theorem56` has the stronger hypothesis `(2 * n - 1) * |S|` instead.
`RpowAffineSliceStatement` below isolates the exact missing geometric theorem,
and the final result proves that this theorem is sufficient for the complete
uniform tail estimate.
-/

namespace Erdos186.CFP.Bilu.Section94RankThresholdBoundary

open Module Submodule
open Section7FreimanMap Section5TwoN Section5EpsilonInduction
open Section5SortedTail Section9KernelAffineReduction

noncomputable section

/-! ## Rank preservation through Section 9.2 -/

/-- Minimal-rank descent can be performed without losing a rank bound supplied
by any initial admissible presentation. -/
theorem exists_good_of_rank_reduction_with_rank_bound
    {P : ℕ → Type*}
    (admissible good : Ranked P → Prop)
    (initial : Ranked P) (hinitial : admissible initial)
    (rankBound : ℕ) (hinitialRank : initial.1 ≤ rankBound)
    (reduce : ∀ x, admissible x → ¬ good x →
      ∃ y, admissible y ∧ y.1 < x.1) :
    ∃ x, admissible x ∧ good x ∧ x.1 ≤ rankBound := by
  obtain ⟨x, hx, hxmin⟩ :=
    exists_rankMinimal admissible ⟨initial, hinitial⟩
  have hxgood : good x := by
    by_contra hbad
    obtain ⟨y, hy, hyrank⟩ := reduce x hx hbad
    exact (not_lt_of_ge (hxmin y hy)) hyrank
  exact ⟨x, hx, hxgood, (hxmin initial hinitial).trans hinitialRank⟩

/-! ## Converting the real source inequality on the valid branch -/

/-- A strict comparison of the real doubling constants converts the source's
`rpow` inequality to the natural-cardinality threshold consumed by the current
generalized `2n` theorem. -/
theorem pairSumset_card_lt_twoN_of_rpow
    {V : Type*} [AddCommGroup V] [DecidableEq V]
    {d : ℕ} {delta : ℝ} {S : Finset V}
    (hS : S.Nonempty)
    (hdouble : ((pairSumset S).card : ℝ) ≤
      Real.rpow 2 ((d : ℝ) + 1 - delta) * S.card)
    (hthreshold : Real.rpow 2 ((d : ℝ) + 1 - delta) <
      ((2 * (d + 1) - 1 : ℕ) : ℝ)) :
    (pairSumset S).card < (2 * (d + 1) - 1) * S.card := by
  have hcard : (0 : ℝ) < S.card := by
    exact_mod_cast Finset.card_pos.mpr hS
  have hstrict :
      Real.rpow 2 ((d : ℝ) + 1 - delta) * S.card <
        ((2 * (d + 1) - 1 : ℕ) : ℝ) * S.card :=
    mul_lt_mul_of_pos_right hthreshold hcard
  have := hdouble.trans_lt hstrict
  exact_mod_cast this

/-! ## The successor-indexed affine-slice packing bound -/

/-- A slice whose direction has dimension below `d + 1` gives a transverse
coordinate among `0, ..., d`.  Sortedness therefore bounds every coordinate
whose zero-based index is at least `d`. -/
theorem sorted_tail_width_le_of_succ_affineSliceWitness
    {ambient rank d proportionConstant volumeConstant rankBound : ℕ}
    (P : GAP ambient rank) (K : Finset P.Coord) (hK : K.Nonempty)
    (hdrank : d + 1 ≤ rank) (hrank : rank ≤ rankBound)
    (hsorted : ∀ i j : Fin rank, (i : ℕ) ≤ (j : ℕ) →
      P.widths j ≤ P.widths i)
    (hvolume : P.volume ≤ volumeConstant * K.card)
    (W : AffineSliceWitness (d + 1) proportionConstant
      (realCoordinateSet P K)) :
    ∀ i : Fin rank, d ≤ (i : ℕ) →
      P.widths i ≤ 3 ^ rankBound * volumeConstant * proportionConstant := by
  obtain ⟨j, hj, hjwidth⟩ :=
    width_le_of_affineSliceWitness P K hK hdrank hvolume W
  intro i hdi
  calc
    P.widths i ≤ P.widths j := hsorted j i (by omega)
    _ ≤ 3 ^ rank * volumeConstant * proportionConstant := hjwidth
    _ ≤ 3 ^ rankBound * volumeConstant * proportionConstant := by
      gcongr
      omega

/-- On the branch where the source `rpow` constant is already below the
current `(2 * (d + 1) - 1)` API threshold, all downstream constants are
uniform and the required zero-based tail begins at `d`. -/
theorem exists_uniform_tailBound_of_rpow_twoN_branch
    (d rankBound volumeConstant : ℕ) (delta : ℝ)
    (hthreshold : Real.rpow 2 ((d : ℝ) + 1 - delta) <
      ((2 * (d + 1) - 1 : ℕ) : ℝ)) :
    ∃ tailBound : ℕ, 0 < tailBound ∧
      ∀ {ambient rank : ℕ} (P : GAP ambient rank) (K : Finset P.Coord),
        K.Nonempty → d + 1 ≤ rank → rank ≤ rankBound →
        (∀ i j : Fin rank, (i : ℕ) ≤ (j : ℕ) →
          P.widths j ≤ P.widths i) →
        P.volume ≤ volumeConstant * K.card →
        ((pairSumset (realCoordinateSet P K)).card : ℝ) ≤
          Real.rpow 2 ((d : ℝ) + 1 - delta) *
            (realCoordinateSet P K).card →
        ∀ i : Fin rank, d ≤ (i : ℕ) → P.widths i ≤ tailBound := by
  obtain ⟨proportionConstant, hslice⟩ :=
    exists_constant_affineSlice (d + 1) (by omega)
  let tailBound := 3 ^ rankBound * volumeConstant * proportionConstant + 1
  refine ⟨tailBound, by simp [tailBound], ?_⟩
  intro ambient rank P K hK hdrank hrank hsorted hvolume hdouble
  have hdoubleNat : (pairSumset (realCoordinateSet P K)).card <
      (2 * (d + 1) - 1) * (realCoordinateSet P K).card :=
    pairSumset_card_lt_twoN_of_rpow (hK.image _) hdouble hthreshold
  have hfinrank : d + 1 ≤ finrank ℝ (Fin rank → ℝ) := by
    simpa using hdrank
  obtain ⟨W⟩ := hslice (Fin rank → ℝ) hfinrank
    (realCoordinateSet P K) (hK.image _) hdoubleNat
  intro i hdi
  exact (sorted_tail_width_le_of_succ_affineSliceWitness P K hK hdrank
    hrank hsorted hvolume W i hdi).trans (Nat.le_succ _)

/-! ## Exact missing source theorem and its complete consumer -/

/-- The exact affine-slice input needed for the full source doubling range.

This is the real-coordinate specialization of Bilu's generalized `2^n`
theorem at rank `d + 1`.  Unlike the existing `RankTwoNStatement`, its
hypothesis is the source-facing real `rpow` inequality. -/
def RpowAffineSliceStatement
    (d proportionConstant : ℕ) (delta : ℝ) : Prop :=
  ∀ rank : ℕ, d + 1 ≤ rank →
    ∀ S : Finset (Fin rank → ℝ), S.Nonempty →
      ((pairSumset S).card : ℝ) ≤
        Real.rpow 2 ((d : ℝ) + 1 - delta) * S.card →
      Nonempty (AffineSliceWitness (d + 1) proportionConstant S)

/-- The exact generalized `2^n` affine-slice statement, together with the
already-proved Section 5.5 packing argument, supplies the full uniform tail
bound required by the sorted-container consumer. -/
theorem exists_uniform_tailBound_of_rpowAffineSlice
    (d rankBound volumeConstant proportionConstant : ℕ) (delta : ℝ)
    (hslice : RpowAffineSliceStatement d proportionConstant delta) :
    ∃ tailBound : ℕ, 0 < tailBound ∧
      ∀ {ambient rank : ℕ} (P : GAP ambient rank) (K : Finset P.Coord),
        K.Nonempty → d + 1 ≤ rank → rank ≤ rankBound →
        (∀ i j : Fin rank, (i : ℕ) ≤ (j : ℕ) →
          P.widths j ≤ P.widths i) →
        P.volume ≤ volumeConstant * K.card →
        ((pairSumset (realCoordinateSet P K)).card : ℝ) ≤
          Real.rpow 2 ((d : ℝ) + 1 - delta) *
            (realCoordinateSet P K).card →
        ∀ i : Fin rank, d ≤ (i : ℕ) → P.widths i ≤ tailBound := by
  let tailBound := 3 ^ rankBound * volumeConstant * proportionConstant + 1
  refine ⟨tailBound, by simp [tailBound], ?_⟩
  intro ambient rank P K hK hdrank hrank hsorted hvolume hdouble
  obtain ⟨W⟩ := hslice rank hdrank (realCoordinateSet P K) (hK.image _) hdouble
  intro i hdi
  exact (sorted_tail_width_le_of_succ_affineSliceWitness P K hK hdrank
    hrank hsorted hvolume W i hdi).trans (Nat.le_succ _)

end


end Erdos186.CFP.Bilu.Section94RankThresholdBoundary

#print axioms
  Erdos186.CFP.Bilu.Section94RankThresholdBoundary.exists_good_of_rank_reduction_with_rank_bound
#print axioms
  Erdos186.CFP.Bilu.Section94RankThresholdBoundary.pairSumset_card_lt_twoN_of_rpow
#print axioms
  Erdos186.CFP.Bilu.Section94RankThresholdBoundary.exists_uniform_tailBound_of_rpow_twoN_branch
#print axioms
  Erdos186.CFP.Bilu.Section94RankThresholdBoundary.exists_uniform_tailBound_of_rpowAffineSlice
