/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.Section92BodyPresentationQuotient
import ErdosProblems.Erdos186.CFP.Bilu.Section92PresentationDescent

/-!
# The primitive quotient in the common presentation interface

This file is the downstream, nonanalytic assembly of Section 9.2.  The
normalized projected gauge already supplies a definite seminorm, exact
unit ball, positive volume, and preservation of all old lattice lifts.
Here those fields are assembled into `BodyPresentation`, the rank-one
drop is made literal, and failure of the enlarged injectivity test is
converted to a strictly smaller presentation.

The only analytic input kept explicit is the existence of a full-rank
independent integral family in the new unit ball.  The source volume-decay
estimate is intentionally kept separate, because it is the input to the
Section 4 minimization rather than a field of `BodyPresentation`.
-/

namespace Erdos186.CFP.Bilu.Section92PresentationQuotientAssembly

open MeasureTheory
open Mahler MinkowskiSecond
open Section9ContainerIntegration
open Section92OuterInjectivityBridge
open Section92BodyPresentationQuotient
open Section92PresentationDescent
open Section92ShortKernel
open Section92ShortKernel.PrimitiveKernelStep
open Section94SortedContainerAssembly

noncomputable section

set_option autoImplicit false

variable {A : Finset ℤ} {n s : ℕ} {T : ℝ}

/-- A quotient which still maps onto a set containing at least two points
cannot have rank zero. -/
theorem complementRank_pos_of_one_lt_card
    (X : BodyPresentation A n)
    (S : PrimitiveKernelStep X.seminorm X.map T)
    (hcard : 1 < A.card) :
    0 < S.quotient.complementRank := by
  apply Nat.pos_of_ne_zero
  intro hrank
  have hall : ∀ a ∈ A, a = 0 := by
    intro a ha
    obtain ⟨x, _hx, hmap⟩ := X.lifts a ha
    have hcoord : S.quotient.complementCoordinates x = 0 := by
      funext i
      have hi : i.val < 0 := by simpa [hrank] using i.isLt
      omega
    have hfactor := S.quotient.reducedMap_complementCoordinates x
    rw [hcoord, map_zero, hmap] at hfactor
    exact hfactor.symm
  have hsubset : A ⊆ {0} := by
    intro a ha
    simp [hall a ha]
  have hle : A.card ≤ ({0} : Finset ℤ).card :=
    Finset.card_le_card hsubset
  simp only [Finset.card_singleton] at hle
  omega

/-- The complement rank is exactly one below the old rank. -/
theorem complementRank_lt
    (X : BodyPresentation A n)
    (S : PrimitiveKernelStep X.seminorm X.map T) :
    S.quotient.complementRank < n := by
  have hrank := S.quotient.rank_eq
  omega

/-- Assemble the coordinate-normalized projected gauge and factored map
into the common presentation record.  All fields except the independent
unit-lattice family are supplied canonically by the primitive quotient. -/
def reducedBodyPresentation
    (X : BodyPresentation A n)
    (S : PrimitiveKernelStep X.seminorm X.map T)
    (hcard : 1 < A.card)
    (hfull : AdmitsIndependent
      (S.coordinateProjectedSeminorm X.definite)
      S.quotient.complementRank 1) :
    BodyPresentation A S.quotient.complementRank where
  rank_pos := complementRank_pos_of_one_lt_card X S hcard
  seminorm := S.coordinateProjectedSeminorm X.definite
  definite := S.isDefinite_coordinateProjectedSeminorm X.definite
  full := hfull
  map := S.quotient.reducedMap
  lifts := by
    intro a ha
    obtain ⟨x, hx, hmap⟩ := X.lifts a ha
    refine ⟨S.quotient.complementCoordinates x,
      S.coordinateProjectedSeminorm_complementCoordinates_le_one
        X.definite x hx, ?_⟩
    rw [S.quotient.reducedMap_complementCoordinates, hmap]
  bodyVolume_pos := by
    rw [S.unitBall_coordinateProjectedSeminorm X.definite]
    exact S.coordinateProjectedBody_volumeReal_pos X.definite

/-- Rank-unspecified form of the reduced presentation. -/
def reducedRankedBodyPresentation
    (X : BodyPresentation A n)
    (S : PrimitiveKernelStep X.seminorm X.map T)
    (hcard : 1 < A.card)
    (hfull : AdmitsIndependent
      (S.coordinateProjectedSeminorm X.definite)
      S.quotient.complementRank 1) :
    RankedBodyPresentation A :=
  ⟨S.quotient.complementRank,
    reducedBodyPresentation X S hcard hfull⟩

@[simp] theorem rank_reducedRankedBodyPresentation
    (X : BodyPresentation A n)
    (S : PrimitiveKernelStep X.seminorm X.map T)
    (hcard : 1 < A.card)
    (hfull : AdmitsIndependent
      (S.coordinateProjectedSeminorm X.definite)
      S.quotient.complementRank 1) :
    (reducedRankedBodyPresentation X S hcard hfull).1 =
      S.quotient.complementRank :=
  rfl

/-- The common candidate's real volume is exactly the volume of the
coordinate-normalized projected body. -/
theorem bodyVolume_reducedRankedBodyPresentation
    (X : BodyPresentation A n)
    (S : PrimitiveKernelStep X.seminorm X.map T)
    (hcard : 1 < A.card)
    (hfull : AdmitsIndependent
      (S.coordinateProjectedSeminorm X.definite)
      S.quotient.complementRank 1) :
    bodyVolume (reducedRankedBodyPresentation X S hcard hfull) =
      volume.real S.coordinateProjectedBody := by
  change volume.real
      {x | S.coordinateProjectedSeminorm X.definite x ≤ 1} = _
  rw [S.unitBall_coordinateProjectedSeminorm X.definite]

/-- A failed enlarged-injectivity test produces the complete algebraic
primitive quotient step at the exact dilation used by the stopping
condition. -/
theorem exists_primitiveKernelStep_of_not_enlargedInjective
    (X : BodyPresentation A n)
    (hbad : ¬ EnlargedInjective s ⟨n, X⟩) :
    Nonempty (PrimitiveKernelStep X.seminorm X.map
      (outerDilationBound n (2 * s))) := by
  exact exists_primitiveKernelStep_of_not_injOn_ball
    X.seminorm X.map (outerDilationBound n (2 * s)) hbad

/-- Complete nonanalytic one-step rank descent.  Once the analytic
projected-body argument provides the independent family, every failed
stopping test has a strictly smaller common presentation. -/
theorem exists_rankDecrease_of_not_enlargedInjective
    (X : BodyPresentation A n) (hcard : 1 < A.card)
    (hfull : ∀ S : PrimitiveKernelStep X.seminorm X.map
        (outerDilationBound n (2 * s)),
      AdmitsIndependent (S.coordinateProjectedSeminorm X.definite)
        S.quotient.complementRank 1)
    (hbad : ¬ EnlargedInjective s ⟨n, X⟩) :
    ∃ Y : RankedBodyPresentation A, Y.1 < n := by
  obtain ⟨S⟩ :=
    exists_primitiveKernelStep_of_not_enlargedInjective X hbad
  exact ⟨reducedRankedBodyPresentation X S hcard (hfull S),
    complementRank_lt X S⟩

/-! ## Canonical closure using the projected independent family -/

/-- The fully assembled analytic quotient, bundled as a rank-unspecified
common candidate. -/
def quotientRankedBodyPresentation
    (X : BodyPresentation A n)
    (S : PrimitiveKernelStep X.seminorm X.map T)
    (hcard : 1 < A.card) :
    RankedBodyPresentation A :=
  ⟨S.quotient.complementRank, quotientBodyPresentation X S hcard⟩

@[simp] theorem rank_quotientRankedBodyPresentation
    (X : BodyPresentation A n)
    (S : PrimitiveKernelStep X.seminorm X.map T)
    (hcard : 1 < A.card) :
    (quotientRankedBodyPresentation X S hcard).1 =
      S.quotient.complementRank :=
  rfl

/-- Exact identification of the common candidate volume after the
canonical primitive quotient. -/
theorem bodyVolume_quotientRankedBodyPresentation
    (X : BodyPresentation A n)
    (S : PrimitiveKernelStep X.seminorm X.map T)
    (hcard : 1 < A.card) :
    bodyVolume (quotientRankedBodyPresentation X S hcard) =
      volume.real S.coordinateProjectedBody := by
  change volume.real
      {x | S.coordinateProjectedSeminorm X.definite x ≤ 1} = _
  rw [S.unitBall_coordinateProjectedSeminorm X.definite]

/-- Every failed stopping test has a canonical strictly smaller common
presentation.  No analytic premise remains at this boundary. -/
theorem exists_canonicalRankDecrease_of_not_enlargedInjective
    (X : BodyPresentation A n) (hcard : 1 < A.card)
    (hbad : ¬ EnlargedInjective s ⟨n, X⟩) :
    ∃ Y : RankedBodyPresentation A, Y.1 < n := by
  obtain ⟨S⟩ :=
    exists_primitiveKernelStep_of_not_enlargedInjective X hbad
  exact ⟨quotientRankedBodyPresentation X S hcard,
    quotientBodyPresentation_rank_lt X S⟩

end

end Erdos186.CFP.Bilu.Section92PresentationQuotientAssembly

#print axioms
  Erdos186.CFP.Bilu.Section92PresentationQuotientAssembly.reducedBodyPresentation
#print axioms
  Erdos186.CFP.Bilu.Section92PresentationQuotientAssembly.exists_rankDecrease_of_not_enlargedInjective
#print axioms
  Erdos186.CFP.Bilu.Section92PresentationQuotientAssembly.exists_canonicalRankDecrease_of_not_enlargedInjective
