/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.Section93HomogeneousProductBody
import ErdosProblems.Erdos186.CFP.Bilu.Section93LatticeSectionFullness

/-!
# Bilu Section 9.3: body presentation on the homogeneous affine lattice

This file packages all discrete and finite-dimensional fields of the
affine-span restriction.  The sole quantitative input left downstream is
the volume of the resulting coordinate section.
-/

namespace Erdos186.CFP.Bilu.Section93AffineBodyPresentation

open scoped Pointwise
open Set Module Submodule MeasureTheory
open CFP.BiluFreiman
open Mahler MinkowskiSecond MinkowskiUpper
open Proposition75Case2Construction SubspaceLattice
open Section4PresentationLiftSet Section92PresentationDescent
open Section93HomogeneousAffineSpan Section93HomogeneousProductBody
open Section93LatticeSectionCoordinates Section93LatticeSectionFullness

noncomputable section

set_option autoImplicit false

variable {A : Finset ℤ} {n : ℕ}

/-- Homogeneous integral versions of the selected presentation lifts. -/
def homogeneousPresentationLiftSet (X : BodyPresentation A n) :
    Finset (IntegralPoint (n + 1)) :=
  (presentationLiftSet ⟨n, X⟩).image homogeneousIntegralPoint

@[simp] theorem homogeneousPresentationLiftSet_image_integralReal
    (X : BodyPresentation A n) :
    (homogeneousPresentationLiftSet X).image integralReal =
      homogeneousLiftSet (presentationLiftSet ⟨n, X⟩) := by
  ext x
  simp [homogeneousPresentationLiftSet, homogeneousLiftSet,
    homogeneousRealPoint]

theorem homogeneousSubspace_ne_bot
    (X : BodyPresentation A n) (hA : A.Nonempty) :
    homogeneousSubspace (presentationLiftSet ⟨n, X⟩) ≠ ⊥ := by
  obtain ⟨a, ha⟩ := hA
  let aA : A := ⟨a, ha⟩
  let z := presentationLift ⟨n, X⟩ aA
  have hzK : z ∈ presentationLiftSet ⟨n, X⟩ :=
    (mem_presentationLiftSet_iff ⟨n, X⟩ z).mpr ⟨aA, rfl⟩
  have hzL : homogeneousRealPoint z ∈
      homogeneousSubspace (presentationLiftSet ⟨n, X⟩) :=
    Submodule.subset_span (Finset.mem_image.mpr ⟨z, hzK, rfl⟩)
  intro hbot
  have hz0 : homogeneousRealPoint z = 0 := by
    rw [hbot] at hzL
    exact hzL
  have hlast := congrArg (homogeneousLastReal (n := n)) hz0
  rw [homogeneousLastReal_homogeneousRealPoint, map_zero] at hlast
  norm_num at hlast

theorem homogeneousSubspace_rank_pos
    (X : BodyPresentation A n) (hA : A.Nonempty) :
    0 < finrank ℝ (homogeneousSubspace
      (presentationLiftSet ⟨n, X⟩)) := by
  rw [Module.finrank_pos_iff]
  exact Submodule.nontrivial_iff_ne_bot.mpr (homogeneousSubspace_ne_bot X hA)

/-- The old map after saturated lattice coordinates on the homogeneous
affine span. -/
def affineSectionIntegerMap
    (X : BodyPresentation A n)
    (hproper : homogeneousSubspace (presentationLiftSet ⟨n, X⟩) ≠ ⊤) :
    IntegralPoint (finrank ℝ
      (homogeneousSubspace (presentationLiftSet ⟨n, X⟩))) →+ ℤ :=
  (homogeneousIntegerMap X).comp
    (coordinateIntegralEmbedding
      (homogeneousSubspace (presentationLiftSet ⟨n, X⟩)) hproper
      (span_integralPoints_homogeneousSubspace
        (presentationLiftSet ⟨n, X⟩))).toAddHom

/-- The coordinate seminorm on the homogeneous affine section. -/
def affineSectionSeminorm
    (X : BodyPresentation A n)
    (hproper : homogeneousSubspace (presentationLiftSet ⟨n, X⟩) ≠ ⊤) :
    Seminorm ℝ (Fin (finrank ℝ
      (homogeneousSubspace (presentationLiftSet ⟨n, X⟩))) → ℝ) :=
  coordinateSeminorm
    (homogeneousSubspace (presentationLiftSet ⟨n, X⟩)) hproper
    (span_integralPoints_homogeneousSubspace
      (presentationLiftSet ⟨n, X⟩))
    (homogeneousProductSeminorm X)

theorem affineSectionSeminorm_definite
    (X : BodyPresentation A n)
    (hproper : homogeneousSubspace (presentationLiftSet ⟨n, X⟩) ≠ ⊤) :
    IsDefinite (affineSectionSeminorm X hproper) := by
  exact coordinateSeminorm_definite
    (homogeneousSubspace (presentationLiftSet ⟨n, X⟩)) hproper
    (span_integralPoints_homogeneousSubspace
      (presentationLiftSet ⟨n, X⟩))
    (homogeneousProductSeminorm X)
    (homogeneousProductSeminorm_definite X)

theorem affineSectionSeminorm_admitsIndependent
    (X : BodyPresentation A n)
    (hproper : homogeneousSubspace (presentationLiftSet ⟨n, X⟩) ≠ ⊤) :
    AdmitsIndependent (affineSectionSeminorm X hproper)
      (finrank ℝ (homogeneousSubspace
        (presentationLiftSet ⟨n, X⟩))) 1 := by
  apply coordinateSeminorm_admitsIndependent_of_span
    (homogeneousSubspace (presentationLiftSet ⟨n, X⟩)) hproper
    (span_integralPoints_homogeneousSubspace
      (presentationLiftSet ⟨n, X⟩))
    (homogeneousProductSeminorm X)
    (homogeneousPresentationLiftSet X)
  · rw [homogeneousPresentationLiftSet_image_integralReal]
    rfl
  · intro z hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    apply homogeneousProductSeminorm_homogeneousRealPoint_le_one
    exact presentationLiftSet_subset_unitBall ⟨n, X⟩ hw

/-- Coordinate lift of a source element in the affine section. -/
def affineSectionLift
    (X : BodyPresentation A n)
    (hproper : homogeneousSubspace (presentationLiftSet ⟨n, X⟩) ≠ ⊤)
    (a : ℤ) (ha : a ∈ A) :
    IntegralPoint (finrank ℝ
      (homogeneousSubspace (presentationLiftSet ⟨n, X⟩))) :=
  integralCoordinatesOfMem
    (homogeneousSubspace (presentationLiftSet ⟨n, X⟩)) hproper
    (span_integralPoints_homogeneousSubspace
      (presentationLiftSet ⟨n, X⟩))
    (homogeneousIntegralPoint
      (presentationLift ⟨n, X⟩ ⟨a, ha⟩))
    (show integralReal (homogeneousIntegralPoint
          (presentationLift ⟨n, X⟩ ⟨a, ha⟩)) ∈
        homogeneousSubspace (presentationLiftSet ⟨n, X⟩) from
      Submodule.subset_span <| Finset.mem_image.mpr
        ⟨presentationLift ⟨n, X⟩ ⟨a, ha⟩,
          (mem_presentationLiftSet_iff ⟨n, X⟩
            (presentationLift ⟨n, X⟩ ⟨a, ha⟩)).mpr
              ⟨⟨a, ha⟩, rfl⟩,
          rfl⟩)

theorem affineSectionLift_mem_unitBall
    (X : BodyPresentation A n)
    (hproper : homogeneousSubspace (presentationLiftSet ⟨n, X⟩) ≠ ⊤)
    (a : ℤ) (ha : a ∈ A) :
    affineSectionSeminorm X hproper
      (integralEmbed (affineSectionLift X hproper a ha)) ≤ 1 := by
  change homogeneousProductSeminorm X
    (coordinateEmbedding
      (homogeneousSubspace (presentationLiftSet ⟨n, X⟩)) hproper
      (span_integralPoints_homogeneousSubspace
        (presentationLiftSet ⟨n, X⟩))
      (integralEmbed (affineSectionLift X hproper a ha))) ≤ 1
  dsimp only [affineSectionLift]
  rw [coordinateEmbedding_integralCoordinatesOfMem]
  exact homogeneousPresentationLift_mem_unitBall X a ha

@[simp] theorem affineSectionIntegerMap_affineSectionLift
    (X : BodyPresentation A n)
    (hproper : homogeneousSubspace (presentationLiftSet ⟨n, X⟩) ≠ ⊤)
    (a : ℤ) (ha : a ∈ A) :
    affineSectionIntegerMap X hproper
      (affineSectionLift X hproper a ha) = a := by
  change homogeneousIntegerMap X
    (coordinateIntegralEmbedding
      (homogeneousSubspace (presentationLiftSet ⟨n, X⟩)) hproper
      (span_integralPoints_homogeneousSubspace
        (presentationLiftSet ⟨n, X⟩))
      (affineSectionLift X hproper a ha)) = a
  dsimp only [affineSectionLift]
  rw [coordinateIntegralEmbedding_integralCoordinatesOfMem]
  exact homogeneousIntegerMap_presentationLift X a ha

/-- All non-quantitative fields of the proper affine-section body. -/
def properAffineBodyPresentation
    (X : BodyPresentation A n) (hA : A.Nonempty)
    (hproper : homogeneousSubspace (presentationLiftSet ⟨n, X⟩) ≠ ⊤) :
    BodyPresentation A
      (finrank ℝ (homogeneousSubspace
        (presentationLiftSet ⟨n, X⟩))) where
  rank_pos := homogeneousSubspace_rank_pos X hA
  seminorm := affineSectionSeminorm X hproper
  definite := affineSectionSeminorm_definite X hproper
  full := affineSectionSeminorm_admitsIndependent X hproper
  map := affineSectionIntegerMap X hproper
  lifts := by
    intro a ha
    exact ⟨affineSectionLift X hproper a ha,
      affineSectionLift_mem_unitBall X hproper a ha,
      affineSectionIntegerMap_affineSectionLift X hproper a ha⟩
  bodyVolume_pos :=
    unitBall_volumeReal_pos_of_definite
      (homogeneousSubspace_rank_pos X hA)
      (affineSectionSeminorm X hproper)
      (affineSectionSeminorm_definite X hproper)

/-- Rank-unspecified proper affine-section presentation. -/
def rankedProperAffineBodyPresentation
    (X : RankedBodyPresentation A) (hA : A.Nonempty)
    (hproper : homogeneousSubspace (presentationLiftSet X) ≠ ⊤) :
    RankedBodyPresentation A :=
  ⟨finrank ℝ (homogeneousSubspace (presentationLiftSet X)),
    properAffineBodyPresentation X.2 hA hproper⟩

@[simp] theorem rank_rankedProperAffineBodyPresentation
    (X : RankedBodyPresentation A) (hA : A.Nonempty)
    (hproper : homogeneousSubspace (presentationLiftSet X) ≠ ⊤) :
    (rankedProperAffineBodyPresentation X hA hproper).1 =
      finrank ℝ (homogeneousSubspace (presentationLiftSet X)) := rfl

end

end Erdos186.CFP.Bilu.Section93AffineBodyPresentation

#print axioms
  Erdos186.CFP.Bilu.Section93AffineBodyPresentation.properAffineBodyPresentation
#print axioms
  Erdos186.CFP.Bilu.Section93AffineBodyPresentation.affineSectionIntegerMap_affineSectionLift
