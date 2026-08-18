/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.Section5RpowAffineSlice
import ErdosProblems.Erdos186.CFP.Bilu.Section94SortedContainerAssembly

/-!
# Source-range Sections 9--4 sorted-container assembly

This module removes the temporary natural-cardinality threshold from the
terminal Section 9 API.  It consumes the source-facing `rpow` affine-slice
theorem and a concrete reduced outer realization.  The case in which the
realization has rank at most `d` is handled internally, since then there are
no tail coordinates.
-/

namespace Erdos186.CFP.Bilu.Section94RpowContainerAssembly

open CFP.BiluFreiman Section7FreimanMap Section5SortedTail
open Section9ContainerIntegration
open Section94RankThresholdBoundary Section94SortedContainerAssembly
open Section5RpowAffineSlice

noncomputable section

/-- A fixed Section 5.5 tail bound obtained from the source-range affine
slice theorem. -/
def rpowTailBound
    (d rankBound volumeConstant proportionConstant : ℕ) (delta : ℝ)
    (hslice : RpowAffineSliceStatement d proportionConstant delta) : ℕ :=
  (exists_uniform_tailBound_of_rpowAffineSlice d rankBound volumeConstant
    proportionConstant delta hslice).choose

theorem rpowTailBound_pos
    (d rankBound volumeConstant proportionConstant : ℕ) (delta : ℝ)
    (hslice : RpowAffineSliceStatement d proportionConstant delta) :
    0 < rpowTailBound d rankBound volumeConstant proportionConstant delta
      hslice :=
  (exists_uniform_tailBound_of_rpowAffineSlice d rankBound volumeConstant
    proportionConstant delta hslice).choose_spec.1

/-- The chosen source-range bound controls all sorted tail coordinates. -/
theorem tail_width_le_rpowTailBound
    {ambient rank d rankBound volumeConstant proportionConstant : ℕ}
    {delta : ℝ}
    (hslice : RpowAffineSliceStatement d proportionConstant delta)
    (P : GAP ambient rank) (K : Finset P.Coord)
    (hK : K.Nonempty) (hdrank : d + 1 ≤ rank) (hrank : rank ≤ rankBound)
    (hsorted : ∀ i j : Fin rank, (i : ℕ) ≤ (j : ℕ) →
      P.widths j ≤ P.widths i)
    (hvolume : P.volume ≤ volumeConstant * K.card)
    (hdouble : ((pairSumset (realCoordinateSet P K)).card : ℝ) ≤
      Real.rpow 2 ((d : ℝ) + 1 - delta) *
        (realCoordinateSet P K).card) :
    ∀ i : Fin rank, d ≤ (i : ℕ) →
      P.widths i ≤ rpowTailBound d rankBound volumeConstant
        proportionConstant delta hslice := by
  exact (exists_uniform_tailBound_of_rpowAffineSlice d rankBound
    volumeConstant proportionConstant delta hslice).choose_spec.2
      P K hK hdrank hrank hsorted hvolume hdouble

namespace ReducedOuterRealization

variable {s d volumeConstant rankBound proportionConstant : ℕ}
  {delta : ℝ} {A : Finset ℤ}

/-- Terminal source-range constructor.  The only geometric input not already
bundled by `ReducedOuterRealization` is a coefficient realization preserving
the original `rpow` doubling inequality. -/
def toSortedFsContainer_of_rpowAffineSlice
    (R : ReducedOuterRealization s volumeConstant rankBound A)
    (hd : 0 < d)
    (hslice : RpowAffineSliceStatement d proportionConstant delta)
    (hcoordinates : d + 1 ≤ R.rank →
      ∃ K : Finset R.outer.source.Coord,
        K.Nonempty ∧
        R.outer.source.volume ≤ volumeConstant * K.card ∧
        ((pairSumset (realCoordinateSet R.outer.source K)).card : ℝ) ≤
          Real.rpow 2 ((d : ℝ) + 1 - delta) *
            (realCoordinateSet R.outer.source K).card)
    (hvolumeConstant : 0 < volumeConstant) :
    SortedFsContainer s d volumeConstant
      (rpowTailBound d rankBound volumeConstant proportionConstant delta
        hslice) rankBound A := by
  apply R.outer.toSortedFsContainer R.enlarged_injective R.lifts
    R.volume_le R.rank_le
  · intro i hdi
    by_cases hdrank : d + 1 ≤ R.rank
    · obtain ⟨K, hK, hvolumeK, hdoubleK⟩ := hcoordinates hdrank
      exact tail_width_le_rpowTailBound hslice R.outer.source K hK hdrank
        R.rank_le R.outer.widths_sorted hvolumeK hdoubleK i hdi
    · omega
  · exact hvolumeConstant
  · exact rpowTailBound_pos d rankBound volumeConstant proportionConstant
      delta hslice

/-- Existential form used by a source construction which produces its
reduced realization noncomputably. -/
theorem exists_sortedFsContainer_of_rpowAffineSlice
    (hd : 0 < d)
    (hslice : RpowAffineSliceStatement d proportionConstant delta)
    (hR : Nonempty
      (ReducedOuterRealization s volumeConstant rankBound A))
    (hcoordinates : ∀ R :
        ReducedOuterRealization s volumeConstant rankBound A,
      d + 1 ≤ R.rank → ∃ K : Finset R.outer.source.Coord,
        K.Nonempty ∧
        R.outer.source.volume ≤ volumeConstant * K.card ∧
        ((pairSumset (realCoordinateSet R.outer.source K)).card : ℝ) ≤
          Real.rpow 2 ((d : ℝ) + 1 - delta) *
            (realCoordinateSet R.outer.source K).card)
    (hvolumeConstant : 0 < volumeConstant) :
    Nonempty (SortedFsContainer s d volumeConstant
      (rpowTailBound d rankBound volumeConstant proportionConstant delta
        hslice) rankBound A) := by
  obtain ⟨R⟩ := hR
  exact ⟨toSortedFsContainer_of_rpowAffineSlice R hd hslice
    (hcoordinates R) hvolumeConstant⟩

/-- Fully unconditional Section 5 consumer.  The generalized `2^n` theorem
chooses both the affine-slice proportion and the resulting tail bound; the
remaining arguments are exactly the outputs of the Section 9 realization. -/
theorem exists_tailBound_and_sortedFsContainer_of_sourceDoubling
    (hd : 0 < d) (hdelta : 0 < delta)
    (hR : Nonempty
      (ReducedOuterRealization s volumeConstant rankBound A))
    (hcoordinates : ∀ R :
        ReducedOuterRealization s volumeConstant rankBound A,
      d + 1 ≤ R.rank → ∃ K : Finset R.outer.source.Coord,
        K.Nonempty ∧
        R.outer.source.volume ≤ volumeConstant * K.card ∧
        ((pairSumset (realCoordinateSet R.outer.source K)).card : ℝ) ≤
          Real.rpow 2 ((d : ℝ) + 1 - delta) *
            (realCoordinateSet R.outer.source K).card)
    (hvolumeConstant : 0 < volumeConstant) :
    ∃ tailBound : ℕ, 0 < tailBound ∧
      Nonempty (SortedFsContainer s d volumeConstant tailBound rankBound A) := by
  obtain ⟨proportionConstant, hslice⟩ :=
    exists_rpowAffineSliceStatement d delta hdelta
  let tailBound := rpowTailBound d rankBound volumeConstant
    proportionConstant delta hslice
  refine ⟨tailBound, ?_, ?_⟩
  · exact rpowTailBound_pos d rankBound volumeConstant proportionConstant
      delta hslice
  · exact exists_sortedFsContainer_of_rpowAffineSlice hd hslice hR
      hcoordinates hvolumeConstant

end ReducedOuterRealization

/-! ## Uniform source statement and exact public bridge -/

/-- The sole remaining Section 9--4 construction, with quantifiers ordered
as in Bilu's theorem.  The volume and rank constants are fixed before `A`;
the realization may depend on `A`, and its coefficient set preserves the
original source-range doubling inequality. -/
def ReducedOuterRealizationStatement : Prop :=
  ∀ s d : ℕ, 0 < s → 0 < d →
    ∀ delta : ℝ, 0 < delta →
      ∃ volumeConstant rankBound : ℕ,
        0 < volumeConstant ∧
        ∀ A : Finset ℤ, A.Nonempty →
          ((twoA A).card : ℝ) ≤
              Real.rpow 2 ((d : ℝ) + 1 - delta) * A.card →
            ∃ R : ReducedOuterRealization s volumeConstant rankBound A,
              d + 1 ≤ R.rank →
                ∃ K : Finset R.outer.source.Coord,
                  K.Nonempty ∧
                  R.outer.source.volume ≤ volumeConstant * K.card ∧
                  ((pairSumset
                    (realCoordinateSet R.outer.source K)).card : ℝ) ≤
                    Real.rpow 2 ((d : ℝ) + 1 - delta) *
                      (realCoordinateSet R.outer.source K).card

/-- Complete Sections 9--4 bridge to the exact public source theorem.  The
generalized `2^n` theorem and all tail-width reasoning are invoked here,
after the source construction has supplied a uniform reduced realization. -/
theorem sortedFsContainerStatement_of_reducedOuterRealization
    (hsource : ReducedOuterRealizationStatement) :
    SortedFsContainerStatement := by
  intro s d hs hd delta hdelta
  obtain ⟨volumeConstant, rankBound, hvolumeConstant, hrealize⟩ :=
    hsource s d hs hd delta hdelta
  obtain ⟨proportionConstant, hslice⟩ :=
    exists_rpowAffineSliceStatement d delta hdelta
  let tailBound := rpowTailBound d rankBound volumeConstant
    proportionConstant delta hslice
  refine ⟨volumeConstant, tailBound, rankBound, hvolumeConstant, ?_, ?_⟩
  · exact rpowTailBound_pos d rankBound volumeConstant proportionConstant
      delta hslice
  · intro A hA hdouble
    obtain ⟨R, hcoordinates⟩ := hrealize A hA hdouble
    exact ⟨ReducedOuterRealization.toSortedFsContainer_of_rpowAffineSlice
      R hd hslice hcoordinates hvolumeConstant⟩

end

end Erdos186.CFP.Bilu.Section94RpowContainerAssembly

#print axioms
  Erdos186.CFP.Bilu.Section94RpowContainerAssembly.tail_width_le_rpowTailBound
#print axioms
  Erdos186.CFP.Bilu.Section94RpowContainerAssembly.ReducedOuterRealization.toSortedFsContainer_of_rpowAffineSlice
#print axioms
  Erdos186.CFP.Bilu.Section94RpowContainerAssembly.ReducedOuterRealization.exists_sortedFsContainer_of_rpowAffineSlice
#print axioms
  Erdos186.CFP.Bilu.Section94RpowContainerAssembly.ReducedOuterRealization.exists_tailBound_and_sortedFsContainer_of_sourceDoubling
#print axioms
  Erdos186.CFP.Bilu.Section94RpowContainerAssembly.sortedFsContainerStatement_of_reducedOuterRealization
