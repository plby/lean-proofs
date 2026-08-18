/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.Section5SortedTail
import ErdosProblems.Erdos186.CFP.Bilu.Section9KernelAffineReduction

/-!
# Sections 9--4 terminal sorted-container assembly

This module feeds the unconditional Section 5.5 tail bound into the Section
3 Mahler outer container and its terminal `toSortedFsContainer` constructor.
The coefficient set required by Proposition 5.7 is needed only in the
nonvacuous case `d ≤ rank`; ranks below `d` have no tail coordinates.
-/

namespace Erdos186.CFP.Bilu.Section94SortedContainerAssembly

open Module
open CFP.BiluFreiman
open Section5SortedTail Section7FreimanMap
open Section9ContainerIntegration

noncomputable section

/-- A fixed choice of the uniform Section 5.5 tail bound. -/
def uniformTailBound (d rankBound volumeConstant : ℕ) (hd : 0 < d) : ℕ :=
  (exists_uniform_tailBound d rankBound volumeConstant hd).choose

theorem uniformTailBound_pos
    (d rankBound volumeConstant : ℕ) (hd : 0 < d) :
    0 < uniformTailBound d rankBound volumeConstant hd :=
  (exists_uniform_tailBound d rankBound volumeConstant hd).choose_spec.1

/-- The chosen tail bound has the full uniformity asserted by Proposition
5.7. -/
theorem tail_width_le_uniformTailBound
    {ambient rank d rankBound volumeConstant : ℕ} (hd : 0 < d)
    (P : GAP ambient rank) (K : Finset P.Coord)
    (hK : K.Nonempty) (hdrank : d ≤ rank) (hrank : rank ≤ rankBound)
    (hsorted : ∀ i j : Fin rank, (i : ℕ) ≤ (j : ℕ) →
      P.widths j ≤ P.widths i)
    (hvolume : P.volume ≤ volumeConstant * K.card)
    (hdouble : (pairSumset (realCoordinateSet P K)).card <
      (2 * d - 1) * (realCoordinateSet P K).card) :
    ∀ i : Fin rank, d ≤ (i : ℕ) →
      P.widths i ≤ uniformTailBound d rankBound volumeConstant hd := by
  exact (exists_uniform_tailBound d rankBound volumeConstant hd).choose_spec.2
    P K hK hdrank hrank hsorted hvolume hdouble

/-- Terminal construction of a source-facing sorted Freiman container.

All tail-width reasoning is discharged internally.  The hypotheses left
are the outputs of Sections 9--4: enlarged-body injectivity, unit-ball lifts
of `A`, linear volume and rank bounds, and (when `d ≤ rank`) the finite
coefficient realization to which the Section 5.5 packing theorem applies.
-/
def MappedOuterContainer.toSortedFsContainer_of_smallDoublingCoordinates
    {n s d volumeConstant rankBound : ℕ}
    {A : Finset ℤ} {p : Seminorm ℝ (Fin n → ℝ)}
    {phi : Mahler.IntegralPoint n →+ ℤ}
    (hd : 0 < d)
    (D : MappedOuterContainer p phi)
    (hinj : Set.InjOn (integerPointHom phi)
      (D.source.dilate (2 * s)).carrier)
    (hlifts : ∀ a ∈ A, ∃ z : Mahler.IntegralPoint n,
      p (Mahler.integralEmbed z) ≤ 1 ∧ phi z = a)
    (hvolumeA : D.source.volume ≤ volumeConstant * A.card)
    (hrank : n ≤ rankBound)
    (hcoordinates : d ≤ n → ∃ K : Finset D.source.Coord,
      K.Nonempty ∧
      D.source.volume ≤ volumeConstant * K.card ∧
      (pairSumset (realCoordinateSet D.source K)).card <
        (2 * d - 1) * (realCoordinateSet D.source K).card)
    (hvolumeConstant : 0 < volumeConstant) :
    SortedFsContainer s d volumeConstant
      (uniformTailBound d rankBound volumeConstant hd) rankBound A := by
  apply D.toSortedFsContainer hinj hlifts hvolumeA hrank
  · intro i hdi
    by_cases hdrank : d ≤ n
    · obtain ⟨K, hK, hvolumeK, hdoubleK⟩ := hcoordinates hdrank
      exact tail_width_le_uniformTailBound hd D.source K hK hdrank hrank
        D.widths_sorted hvolumeK hdoubleK i hdi
    · omega
  · exact hvolumeConstant
  · exact uniformTailBound_pos d rankBound volumeConstant hd

/-- Constructor which also performs the unconditional Section 3 Mahler
choice internally.  Since the selected basis is existential, the
coefficient-set property is supplied uniformly for every possible selected
outer container. -/
theorem exists_sortedFsContainer_of_reducedBody
    {n s d volumeConstant rankBound : ℕ}
    {A : Finset ℤ} (hn : 0 < n) (hd : 0 < d)
    (p : Seminorm ℝ (Fin n → ℝ)) (hp : Mahler.IsDefinite p)
    (hfull : Mahler.AdmitsIndependent p n 1)
    (phi : Mahler.IntegralPoint n →+ ℤ)
    (hinj : ∀ D : MappedOuterContainer p phi,
      Set.InjOn (integerPointHom phi) (D.source.dilate (2 * s)).carrier)
    (hlifts : ∀ a ∈ A, ∃ z : Mahler.IntegralPoint n,
      p (Mahler.integralEmbed z) ≤ 1 ∧ phi z = a)
    (hvolumeA : ∀ D : MappedOuterContainer p phi,
      D.source.volume ≤ volumeConstant * A.card)
    (hrank : n ≤ rankBound)
    (hcoordinates : ∀ D : MappedOuterContainer p phi, d ≤ n →
      ∃ K : Finset D.source.Coord, K.Nonempty ∧
        D.source.volume ≤ volumeConstant * K.card ∧
        (pairSumset (realCoordinateSet D.source K)).card <
          (2 * d - 1) * (realCoordinateSet D.source K).card)
    (hvolumeConstant : 0 < volumeConstant) :
    Nonempty (SortedFsContainer s d volumeConstant
      (uniformTailBound d rankBound volumeConstant hd) rankBound A) := by
  obtain ⟨D⟩ := exists_mappedOuterContainer hn p hp hfull phi
  exact ⟨MappedOuterContainer.toSortedFsContainer_of_smallDoublingCoordinates
    hd D (hinj D) hlifts (hvolumeA D) hrank (hcoordinates D)
      hvolumeConstant⟩

/-! ## Stable Section 9 output package -/

/-- The complete output expected from the minimal-rank kernel repair and
affine-span restriction before applying the Section 5 tail theorem.

Bundling the chosen Mahler container is important: the source construction
only has to prove injectivity and the volume estimate for the container it
actually selects, rather than uniformly for every possible Mahler basis. -/
structure ReducedOuterRealization
    (s volumeConstant rankBound : ℕ) (A : Finset ℤ) where
  rank : ℕ
  seminorm : Seminorm ℝ (Fin rank → ℝ)
  map : Mahler.IntegralPoint rank →+ ℤ
  outer : MappedOuterContainer seminorm map
  enlarged_injective : Set.InjOn (integerPointHom map)
    (outer.source.dilate (2 * s)).carrier
  lifts : ∀ a ∈ A, ∃ z : Mahler.IntegralPoint rank,
    seminorm (Mahler.integralEmbed z) ≤ 1 ∧ map z = a
  volume_le : outer.source.volume ≤ volumeConstant * A.card
  rank_le : rank ≤ rankBound

namespace ReducedOuterRealization

variable {s d volumeConstant rankBound : ℕ} {A : Finset ℤ}

/-- Consume a concrete minimal-rank realization.  This is the non-uniform
counterpart of `exists_sortedFsContainer_of_reducedBody` and is the terminal
API for the Proposition 7.5-to-Section 9 construction. -/
def toSortedFsContainer_of_smallDoublingCoordinates
    (R : ReducedOuterRealization s volumeConstant rankBound A)
    (hd : 0 < d)
    (hcoordinates : d ≤ R.rank → ∃ K : Finset R.outer.source.Coord,
      K.Nonempty ∧
      R.outer.source.volume ≤ volumeConstant * K.card ∧
      (pairSumset (realCoordinateSet R.outer.source K)).card <
        (2 * d - 1) * (realCoordinateSet R.outer.source K).card)
    (hvolumeConstant : 0 < volumeConstant) :
    SortedFsContainer s d volumeConstant
      (uniformTailBound d rankBound volumeConstant hd) rankBound A :=
  MappedOuterContainer.toSortedFsContainer_of_smallDoublingCoordinates hd
    R.outer R.enlarged_injective R.lifts R.volume_le R.rank_le hcoordinates
      hvolumeConstant

end ReducedOuterRealization

end

end Erdos186.CFP.Bilu.Section94SortedContainerAssembly

#print axioms Erdos186.CFP.Bilu.Section94SortedContainerAssembly.tail_width_le_uniformTailBound
#print axioms Erdos186.CFP.Bilu.Section94SortedContainerAssembly.MappedOuterContainer.toSortedFsContainer_of_smallDoublingCoordinates
#print axioms Erdos186.CFP.Bilu.Section94SortedContainerAssembly.exists_sortedFsContainer_of_reducedBody
#print axioms Erdos186.CFP.Bilu.Section94SortedContainerAssembly.ReducedOuterRealization.toSortedFsContainer_of_smallDoublingCoordinates
