/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.Section91GenericSharpProduct
import ErdosProblems.Erdos186.CFP.Bilu.Section93AffineBodyPresentation

/-!
# Bilu Section 9.3: affine restriction after Mahler normalization

Before restricting to the affine span, we put the stopped presentation in
the normalized Mahler coordinates of Section 8.  This gives a uniform
Euclidean inball and costs only the familiar rank power in volume.  This
file packages the integral maps, retained source lifts, fullness, and rank
bound; the quantitative section-volume comparison is kept downstream.
-/

namespace Erdos186.CFP.Bilu.Section93NormalizedAffineBodyPresentation

open scoped Pointwise
open Set Module Submodule MeasureTheory
open CFP.BiluFreiman
open Mahler MinkowskiSecond MinkowskiUpper
open Proposition75Case2Construction SubspaceLattice
open Section4PresentationLiftSet Section8PresentationNormalization
open Section91GenericSharpProduct Section92PresentationDescent
open Section93HomogeneousAffineSpan Section93HomogeneousProductBody
open Section93LatticeSectionCoordinates Section93LatticeSectionFullness

noncomputable section

set_option autoImplicit false

variable {A : Finset ℤ}

/-- The current presentation expressed in normalized Mahler coordinates.
Its displayed lifts are the canonical normalized source lifts. -/
def normalizedBodyPresentation (X : RankedBodyPresentation A) :
    BodyPresentation A X.1 where
  rank_pos := X.2.rank_pos
  seminorm := normalizedMahlerSeminorm X
  definite := normalizedMahlerSeminorm_definite X
  full := by
    refine ⟨fun i ↦ standardIntegralPoint i, ?_, ?_⟩
    · exact linearIndependent_integralEmbed_standard
    · exact normalizedMahlerSeminorm_standard_le_one X
  map := normalizedBackMap X
  lifts := by
    intro a ha
    let aA : A := ⟨a, ha⟩
    refine ⟨sourceNormalizedLift X aA, ?_, ?_⟩
    · exact normalizedLiftSet_subset_unitBall X
        (sourceNormalizedLift_mem X aA)
    · exact normalizedBackMap_sourceNormalizedLift X aA
  bodyVolume_pos := by
    exact unitBall_volumeReal_pos_of_definite X.2.rank_pos
      (normalizedMahlerSeminorm X)
      (normalizedMahlerSeminorm_definite X)

/-- Homogeneous normalized source lattice. -/
abbrev normalizedHomogeneousSubspace (X : RankedBodyPresentation A) :
    Submodule ℝ (EuclideanSpace ℝ (Fin (X.1 + 1))) :=
  homogeneousSubspace (normalizedLiftSet X)

/-- The normalized product seminorm used for the affine restriction. -/
abbrev normalizedHomogeneousProductSeminorm (X : RankedBodyPresentation A) :
    Seminorm ℝ (EuclideanSpace ℝ (Fin (X.1 + 1))) :=
  homogeneousProductSeminorm (normalizedBodyPresentation X)

/-- The normalized map after homogenization. -/
abbrev normalizedHomogeneousIntegerMap (X : RankedBodyPresentation A) :
    IntegralPoint (X.1 + 1) →+ ℤ :=
  homogeneousIntegerMap (normalizedBodyPresentation X)

/-- Homogeneous normalized integral lifts. -/
def normalizedHomogeneousLiftSet (X : RankedBodyPresentation A) :
    Finset (IntegralPoint (X.1 + 1)) :=
  (normalizedLiftSet X).image homogeneousIntegralPoint

@[simp] theorem normalizedHomogeneousLiftSet_image_integralReal
    (X : RankedBodyPresentation A) :
    (normalizedHomogeneousLiftSet X).image integralReal =
      homogeneousLiftSet (normalizedLiftSet X) := by
  ext x
  simp [normalizedHomogeneousLiftSet, homogeneousLiftSet,
    homogeneousRealPoint]

theorem normalizedHomogeneousSubspace_ne_bot
    (X : RankedBodyPresentation A) (hA : A.Nonempty) :
    normalizedHomogeneousSubspace X ≠ ⊥ := by
  obtain ⟨a, ha⟩ := hA
  let aA : A := ⟨a, ha⟩
  let z := sourceNormalizedLift X aA
  have hzK : z ∈ normalizedLiftSet X := sourceNormalizedLift_mem X aA
  have hzL : homogeneousRealPoint z ∈ normalizedHomogeneousSubspace X :=
    Submodule.subset_span (Finset.mem_image.mpr ⟨z, hzK, rfl⟩)
  intro hbot
  have hz0 : homogeneousRealPoint z = 0 := by
    rw [hbot] at hzL
    exact hzL
  have hlast := congrArg
    (homogeneousLastReal (n := X.1)) hz0
  rw [homogeneousLastReal_homogeneousRealPoint, map_zero] at hlast
  norm_num at hlast

theorem normalizedHomogeneousSubspace_rank_pos
    (X : RankedBodyPresentation A) (hA : A.Nonempty) :
    0 < finrank ℝ (normalizedHomogeneousSubspace X) := by
  rw [Module.finrank_pos_iff]
  exact Submodule.nontrivial_iff_ne_bot.mpr
    (normalizedHomogeneousSubspace_ne_bot X hA)

/-- Coordinate seminorm on a proper normalized affine section. -/
def normalizedAffineSectionSeminorm
    (X : RankedBodyPresentation A)
    (hproper : normalizedHomogeneousSubspace X ≠ ⊤) :
    Seminorm ℝ (Fin (finrank ℝ (normalizedHomogeneousSubspace X)) → ℝ) :=
  coordinateSeminorm (normalizedHomogeneousSubspace X) hproper
    (span_integralPoints_homogeneousSubspace (normalizedLiftSet X))
    (normalizedHomogeneousProductSeminorm X)

theorem normalizedAffineSectionSeminorm_definite
    (X : RankedBodyPresentation A)
    (hproper : normalizedHomogeneousSubspace X ≠ ⊤) :
    IsDefinite (normalizedAffineSectionSeminorm X hproper) := by
  exact coordinateSeminorm_definite
    (normalizedHomogeneousSubspace X) hproper
    (span_integralPoints_homogeneousSubspace (normalizedLiftSet X))
    (normalizedHomogeneousProductSeminorm X)
    (homogeneousProductSeminorm_definite (normalizedBodyPresentation X))

theorem normalizedAffineSectionSeminorm_admitsIndependent
    (X : RankedBodyPresentation A)
    (hproper : normalizedHomogeneousSubspace X ≠ ⊤) :
    AdmitsIndependent (normalizedAffineSectionSeminorm X hproper)
      (finrank ℝ (normalizedHomogeneousSubspace X)) 1 := by
  apply coordinateSeminorm_admitsIndependent_of_span
    (normalizedHomogeneousSubspace X) hproper
    (span_integralPoints_homogeneousSubspace (normalizedLiftSet X))
    (normalizedHomogeneousProductSeminorm X)
    (normalizedHomogeneousLiftSet X)
  · rw [normalizedHomogeneousLiftSet_image_integralReal]
    rfl
  · intro z hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    apply homogeneousProductSeminorm_homogeneousRealPoint_le_one
    exact normalizedLiftSet_subset_unitBall X hw

/-- Integer map in saturated coordinates of the proper affine section. -/
def normalizedAffineSectionIntegerMap
    (X : RankedBodyPresentation A)
    (hproper : normalizedHomogeneousSubspace X ≠ ⊤) :
    IntegralPoint (finrank ℝ (normalizedHomogeneousSubspace X)) →+ ℤ :=
  (normalizedHomogeneousIntegerMap X).comp
    (coordinateIntegralEmbedding (normalizedHomogeneousSubspace X) hproper
      (span_integralPoints_homogeneousSubspace
        (normalizedLiftSet X))).toAddHom

/-- Retained normalized source lift in saturated affine coordinates. -/
def normalizedAffineSectionLift
    (X : RankedBodyPresentation A)
    (hproper : normalizedHomogeneousSubspace X ≠ ⊤)
    (a : ℤ) (ha : a ∈ A) :
    IntegralPoint (finrank ℝ (normalizedHomogeneousSubspace X)) :=
  let aA : A := ⟨a, ha⟩
  integralCoordinatesOfMem (normalizedHomogeneousSubspace X) hproper
    (span_integralPoints_homogeneousSubspace (normalizedLiftSet X))
    (homogeneousIntegralPoint (sourceNormalizedLift X aA))
    (show integralReal
        (homogeneousIntegralPoint (sourceNormalizedLift X aA)) ∈
        normalizedHomogeneousSubspace X from
      Submodule.subset_span (Finset.mem_image.mpr
        ⟨sourceNormalizedLift X aA, sourceNormalizedLift_mem X aA, rfl⟩))

theorem normalizedAffineSectionLift_mem_unitBall
    (X : RankedBodyPresentation A)
    (hproper : normalizedHomogeneousSubspace X ≠ ⊤)
    (a : ℤ) (ha : a ∈ A) :
    normalizedAffineSectionSeminorm X hproper
      (integralEmbed (normalizedAffineSectionLift X hproper a ha)) ≤ 1 := by
  change normalizedHomogeneousProductSeminorm X
    (coordinateEmbedding (normalizedHomogeneousSubspace X) hproper
      (span_integralPoints_homogeneousSubspace (normalizedLiftSet X))
      (integralEmbed (normalizedAffineSectionLift X hproper a ha))) ≤ 1
  dsimp only [normalizedAffineSectionLift]
  rw [coordinateEmbedding_integralCoordinatesOfMem]
  apply homogeneousProductSeminorm_homogeneousRealPoint_le_one
  exact normalizedLiftSet_subset_unitBall X
    (sourceNormalizedLift_mem X ⟨a, ha⟩)

@[simp] theorem normalizedAffineSectionIntegerMap_lift
    (X : RankedBodyPresentation A)
    (hproper : normalizedHomogeneousSubspace X ≠ ⊤)
    (a : ℤ) (ha : a ∈ A) :
    normalizedAffineSectionIntegerMap X hproper
      (normalizedAffineSectionLift X hproper a ha) = a := by
  change normalizedHomogeneousIntegerMap X
    (coordinateIntegralEmbedding (normalizedHomogeneousSubspace X) hproper
      (span_integralPoints_homogeneousSubspace (normalizedLiftSet X))
      (normalizedAffineSectionLift X hproper a ha)) = a
  dsimp only [normalizedAffineSectionLift]
  rw [coordinateIntegralEmbedding_integralCoordinatesOfMem]
  rw [homogeneousIntegerMap_homogeneousIntegralPoint]
  exact normalizedBackMap_sourceNormalizedLift X ⟨a, ha⟩

/-- Proper affine-section presentation after Mahler normalization. -/
def normalizedProperAffineBodyPresentation
    (X : RankedBodyPresentation A) (hA : A.Nonempty)
    (hproper : normalizedHomogeneousSubspace X ≠ ⊤) :
    BodyPresentation A (finrank ℝ (normalizedHomogeneousSubspace X)) where
  rank_pos := normalizedHomogeneousSubspace_rank_pos X hA
  seminorm := normalizedAffineSectionSeminorm X hproper
  definite := normalizedAffineSectionSeminorm_definite X hproper
  full := normalizedAffineSectionSeminorm_admitsIndependent X hproper
  map := normalizedAffineSectionIntegerMap X hproper
  lifts := by
    intro a ha
    exact ⟨normalizedAffineSectionLift X hproper a ha,
      normalizedAffineSectionLift_mem_unitBall X hproper a ha,
      normalizedAffineSectionIntegerMap_lift X hproper a ha⟩
  bodyVolume_pos := unitBall_volumeReal_pos_of_definite
    (normalizedHomogeneousSubspace_rank_pos X hA)
    (normalizedAffineSectionSeminorm X hproper)
    (normalizedAffineSectionSeminorm_definite X hproper)

/-- Rank-unspecified proper normalized affine-section presentation. -/
def rankedNormalizedProperAffineBodyPresentation
    (X : RankedBodyPresentation A) (hA : A.Nonempty)
    (hproper : normalizedHomogeneousSubspace X ≠ ⊤) :
    RankedBodyPresentation A :=
  ⟨finrank ℝ (normalizedHomogeneousSubspace X),
    normalizedProperAffineBodyPresentation X hA hproper⟩

theorem rank_rankedNormalizedProperAffineBodyPresentation_le
    (s : ℕ) (hs : 0 < s) (X : RankedBodyPresentation A)
    (hX : EnlargedInjective s X) (hA : A.Nonempty)
    (sigma : ℝ) (hsigma : 0 ≤ sigma)
    (hdouble : ((twoA A).card : ℝ) ≤ sigma * A.card)
    (hproper : normalizedHomogeneousSubspace X ≠ ⊤) :
    (rankedNormalizedProperAffineBodyPresentation X hA hproper).1 ≤
      2 * Nat.ceil sigma := by
  exact normalizedLiftSet_homogeneous_rank_le_two_mul_ceil
    s hs X hX hA sigma hsigma hdouble

/-! ## The codimension-zero branch -/

/-- The normalized homogeneous product pulled back from Euclidean space to
the raw coordinate type used by `BodyPresentation`. -/
def normalizedTopProductSeminorm (X : RankedBodyPresentation A) :
    Seminorm ℝ (Fin (X.1 + 1) → ℝ) :=
  (normalizedHomogeneousProductSeminorm X).comp
    (EuclideanSpace.equiv (Fin (X.1 + 1)) ℝ).symm.toLinearMap

theorem normalizedTopProductSeminorm_definite
    (X : RankedBodyPresentation A) :
    IsDefinite (normalizedTopProductSeminorm X) := by
  intro x hx
  apply (EuclideanSpace.equiv (Fin (X.1 + 1)) ℝ).symm.injective
  simpa using
    (homogeneousProductSeminorm_definite (normalizedBodyPresentation X)
      _ hx)

theorem euclidean_symm_integralEmbed
    (X : RankedBodyPresentation A) (z : IntegralPoint (X.1 + 1)) :
    (EuclideanSpace.equiv (Fin (X.1 + 1)) ℝ).symm (integralEmbed z) =
      integralReal z := by
  ext i
  rfl

theorem normalizedHomogeneousProductSeminorm_standard_le_one
    (X : RankedBodyPresentation A) (j : Fin (X.1 + 1)) :
    normalizedTopProductSeminorm X
      (integralEmbed (standardIntegralPoint j)) ≤ 1 := by
  change normalizedHomogeneousProductSeminorm X
    ((EuclideanSpace.equiv (Fin (X.1 + 1)) ℝ).symm
      (integralEmbed (standardIntegralPoint j))) ≤ 1
  rw [euclidean_symm_integralEmbed X]
  generalize hq : finSumFinEquiv.symm j = q
  cases q with
  | inl i =>
      have hj : j = Fin.castAdd 1 i := by
        apply finSumFinEquiv.symm.injective
        rw [hq, finSumFinEquiv_symm_apply_castAdd]
      subst j
      have hhead : homogeneousHeadReal
          (integralReal (standardIntegralPoint (Fin.castAdd 1 i) :
            IntegralPoint (X.1 + 1))) =
          integralEmbed (standardIntegralPoint i) := by
        ext k
        change ((standardIntegralPoint (Fin.castAdd 1 i) :
          IntegralPoint (X.1 + 1)) (Fin.castAdd 1 k) : ℝ) =
            ((standardIntegralPoint i) k : ℝ)
        by_cases hik : i = k
        · subst k
          simp [standardIntegralPoint, Pi.basisFun]
        · have hcast : Fin.castAdd 1 i ≠ Fin.castAdd 1 k := by
            exact fun h ↦ hik ((Fin.castAddEmb 1).injective h)
          simp [standardIntegralPoint, Pi.basisFun, Pi.single_apply,
            hik, hcast]
      have hlast : homogeneousLastReal
          (integralReal (standardIntegralPoint (Fin.castAdd 1 i) :
            IntegralPoint (X.1 + 1))) = 0 := by
        change ((standardIntegralPoint (Fin.castAdd 1 i) :
          IntegralPoint (X.1 + 1)) (Fin.natAdd X.1 0) : ℝ) = 0
        have hne : Fin.castAdd 1 i ≠ Fin.natAdd X.1 0 := by
          intro h
          have hh := congrArg finSumFinEquiv.symm h
          simpa [finSumFinEquiv_symm_apply_castAdd,
            finSumFinEquiv_symm_apply_natAdd] using hh
        simp [standardIntegralPoint, Pi.basisFun, Pi.single_apply, hne]
      rw [homogeneousProductSeminorm_apply, hhead, hlast, norm_zero]
      change max
        (normalizedMahlerSeminorm X
          (integralEmbed (standardIntegralPoint i))) 0 ≤ 1
      rw [max_eq_left (apply_nonneg _ _)]
      · exact normalizedMahlerSeminorm_standard_le_one X i
  | inr i =>
      have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
      subst i
      have hj : j = Fin.natAdd X.1 0 := by
        apply finSumFinEquiv.symm.injective
        rw [hq, finSumFinEquiv_symm_apply_natAdd]
      subst j
      have hhead : homogeneousHeadReal
          (integralReal (standardIntegralPoint (Fin.natAdd X.1 0) :
            IntegralPoint (X.1 + 1))) = 0 := by
        ext k
        change ((standardIntegralPoint (Fin.natAdd X.1 0) :
          IntegralPoint (X.1 + 1)) (Fin.castAdd 1 k) : ℝ) = 0
        have hne : Fin.natAdd X.1 0 ≠ Fin.castAdd 1 k := by
          intro h
          have hh := congrArg finSumFinEquiv.symm h
          simpa [finSumFinEquiv_symm_apply_castAdd,
            finSumFinEquiv_symm_apply_natAdd] using hh
        simp [standardIntegralPoint, Pi.basisFun, Pi.single_apply, hne]
      have hlast : homogeneousLastReal
          (integralReal (standardIntegralPoint (Fin.natAdd X.1 0) :
            IntegralPoint (X.1 + 1))) = 1 := by
        change ((standardIntegralPoint (Fin.natAdd X.1 0) :
          IntegralPoint (X.1 + 1)) (Fin.natAdd X.1 0) : ℝ) = 1
        simp [standardIntegralPoint, Pi.basisFun]
      rw [homogeneousProductSeminorm_apply, hhead, hlast, norm_one]
      change max (normalizedMahlerSeminorm X 0) 1 ≤ 1
      rw [map_zero, max_eq_right]
      norm_num

/-- If the homogeneous affine span is already the whole ambient space,
the normalized product body itself is the desired presentation. -/
def normalizedTopAffineBodyPresentation
    (X : RankedBodyPresentation A) : BodyPresentation A (X.1 + 1) where
  rank_pos := Nat.succ_pos X.1
  seminorm := normalizedTopProductSeminorm X
  definite := normalizedTopProductSeminorm_definite X
  full := by
    refine ⟨fun i ↦ standardIntegralPoint i,
      linearIndependent_integralEmbed_standard, ?_⟩
    exact normalizedHomogeneousProductSeminorm_standard_le_one X
  map := normalizedHomogeneousIntegerMap X
  lifts := by
    intro a ha
    let aA : A := ⟨a, ha⟩
    refine ⟨homogeneousIntegralPoint (sourceNormalizedLift X aA), ?_, ?_⟩
    · change normalizedHomogeneousProductSeminorm X
        ((EuclideanSpace.equiv (Fin (X.1 + 1)) ℝ).symm
          (integralEmbed (homogeneousIntegralPoint
            (sourceNormalizedLift X aA)))) ≤ 1
      rw [euclidean_symm_integralEmbed X]
      apply homogeneousProductSeminorm_homogeneousRealPoint_le_one
      exact normalizedLiftSet_subset_unitBall X
        (sourceNormalizedLift_mem X aA)
    · rw [homogeneousIntegerMap_homogeneousIntegralPoint]
      exact normalizedBackMap_sourceNormalizedLift X aA
  bodyVolume_pos := unitBall_volumeReal_pos_of_definite
    (Nat.succ_pos X.1) (normalizedTopProductSeminorm X)
    (normalizedTopProductSeminorm_definite X)

def rankedNormalizedTopAffineBodyPresentation
    (X : RankedBodyPresentation A) : RankedBodyPresentation A :=
  ⟨X.1 + 1, normalizedTopAffineBodyPresentation X⟩

theorem rank_rankedNormalizedTopAffineBodyPresentation_le
    (s : ℕ) (hs : 0 < s) (X : RankedBodyPresentation A)
    (hX : EnlargedInjective s X) (hA : A.Nonempty)
    (sigma : ℝ) (hsigma : 0 ≤ sigma)
    (hdouble : ((twoA A).card : ℝ) ≤ sigma * A.card)
    (htop : normalizedHomogeneousSubspace X = ⊤) :
    (rankedNormalizedTopAffineBodyPresentation X).1 ≤
      2 * Nat.ceil sigma := by
  have h := normalizedLiftSet_homogeneous_rank_le_two_mul_ceil
    s hs X hX hA sigma hsigma hdouble
  change finrank ℝ (normalizedHomogeneousSubspace X) ≤
    2 * Nat.ceil sigma at h
  rw [htop, finrank_top, finrank_euclideanSpace_fin] at h
  exact h

end

end Erdos186.CFP.Bilu.Section93NormalizedAffineBodyPresentation

#print axioms
  Erdos186.CFP.Bilu.Section93NormalizedAffineBodyPresentation.normalizedProperAffineBodyPresentation
#print axioms
  Erdos186.CFP.Bilu.Section93NormalizedAffineBodyPresentation.rank_rankedNormalizedProperAffineBodyPresentation_le
