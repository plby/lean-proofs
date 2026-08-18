/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.Section91IntegerPresentation
import ErdosProblems.Erdos186.CFP.Bilu.Section4PresentationLiftSet
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The sharp Section 9.1 product presentation

This module performs the algebraic product assembly after the normalized
section body has been put in coordinates of its literal lattice.  The
section gauge is kept as one sharply quantified input record; all centre
coordinates, the integer presentation map, source lifts, full-rank
thickness, and product-volume bookkeeping are constructed here.
-/

namespace Erdos186.CFP.Bilu.Section91SharpProductPresentation

open scoped Pointwise NNReal
open MeasureTheory Set Module
open Mahler MinkowskiSecond
open Proposition75Data Proposition75Case2 Proposition75Case2Construction
  SubspaceLattice
open Section9NormalizedReplacement Section91InitialPresentation
open Section91CoveringEnlargement
open Section91InitialPresentation.InitialPresentation
open Section91InitialCoordinates.InitialPresentation
open Section91IntegerPresentation
open Section92PresentationDescent

noncomputable section

set_option autoImplicit false

variable {r : ℕ} {B : Set (EuclideanSpace ℝ (Fin 1))}
  {a : Fin r → EuclideanSpace ℝ (Fin 1)}
  {D : GeometricData B a}
  {A : Finset ℤ} {coverConstant sigma : ℕ}
  {constant scale : ENNReal}

abbrev SectionRank (D : GeometricData B a) := finrank ℝ D.C0

/-- The explicit decomposition of the initial rank into section-lattice
coordinates and adjoined covering-centre coordinates. -/
def initialIndexEquiv
    (N : CoveredNormalizedReplacement (D := D)
      (K := Section90IntegerInitialization.integerSet A)
      (coverConstant := coverConstant) constant scale sigma) :
    Fin (initialRank N) ≃
      Fin (SectionRank D) ⊕ N.cover.centers :=
  Fintype.equivOfCardEq (by
    rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_coe,
      Fintype.card_fin]
    rfl)

/-- Split standard coordinates into the section and centre blocks. -/
def splitLinearEquiv (R : Type*) [Semiring R]
    (N : CoveredNormalizedReplacement (D := D)
      (K := Section90IntegerInitialization.integerSet A)
      (coverConstant := coverConstant) constant scale sigma) :
    (Fin (initialRank N) → R) ≃ₗ[R]
      (Fin (SectionRank D) → R) × (N.cover.centers → R) :=
  (LinearEquiv.piCongrLeft' (R := R) (φ := fun _ ↦ R)
      (initialIndexEquiv N)).trans
    (LinearEquiv.sumArrowLequivProdArrow
      (Fin (SectionRank D)) N.cover.centers R R)

@[simp] theorem splitLinearEquiv_apply_fst
    (R : Type*) [Semiring R]
    (N : CoveredNormalizedReplacement (D := D)
      (K := Section90IntegerInitialization.integerSet A)
      (coverConstant := coverConstant) constant scale sigma)
    (x : Fin (initialRank N) → R) (i : Fin (SectionRank D)) :
    (splitLinearEquiv R N x).1 i =
      x ((initialIndexEquiv N).symm (Sum.inl i)) := rfl

@[simp] theorem splitLinearEquiv_apply_snd
    (R : Type*) [Semiring R]
    (N : CoveredNormalizedReplacement (D := D)
      (K := Section90IntegerInitialization.integerSet A)
      (coverConstant := coverConstant) constant scale sigma)
    (x : Fin (initialRank N) → R) (c : N.cover.centers) :
    (splitLinearEquiv R N x).2 c =
      x ((initialIndexEquiv N).symm (Sum.inr c)) := rfl

theorem splitLinearEquiv_integralEmbed
    (N : CoveredNormalizedReplacement (D := D)
      (K := Section90IntegerInitialization.integerSet A)
      (coverConstant := coverConstant) constant scale sigma)
    (z : IntegralPoint (initialRank N)) :
    splitLinearEquiv ℝ N (integralEmbed z) =
      (integralEmbed (splitLinearEquiv ℤ N z).1,
        fun c ↦ ((splitLinearEquiv ℤ N z).2 c : ℝ)) := by
  ext i <;> rfl

/-- Exact sharp input needed from the normalized section body.  Its
volume is already divided by the covolume of the literal section lattice.
The `difference_mem` field is exactly what the Ruzsa-cover lifts use. -/
structure SharpSectionData
    (N : CoveredNormalizedReplacement (D := D)
      (K := Section90IntegerInitialization.integerSet A)
      (coverConstant := coverConstant) constant scale sigma) where
  seminorm : Seminorm ℝ (Fin (SectionRank D) → ℝ)
  definite : IsDefinite seminorm
  full : AdmitsIndependent seminorm (SectionRank D) 1
  difference_mem : ∀
    (x : {x // x ∈ N.normalized.seed.sourceSlice})
    (y : {y // y ∈ N.normalized.seed.sourceSlice}),
      seminorm (integralEmbed
        ((coordinateIntegralBasis (D := D)).equivFun
          (coordinateLatticeEquiv D
            (Section91CoveringEnlargement.Lemma45SectionSeed.differenceLift
              N.normalized.seed x y)))) ≤ 1
  volume_le :
    volume {x | seminorm x ≤ 1} ≤
      (2 : ENNReal) ^ SectionRank D *
        (volume (coordinateB0 D) /
          ENNReal.ofReal
            (ZLattice.covolume (integralPoints (coordinateC0 D))))

/-- The sup gauge on the adjoined centre coordinates. -/
def centerSeminorm
    (N : CoveredNormalizedReplacement (D := D)
      (K := Section90IntegerInitialization.integerSet A)
      (coverConstant := coverConstant) constant scale sigma) :
    Seminorm ℝ (N.cover.centers → ℝ) :=
  normSeminorm ℝ (N.cover.centers → ℝ)

/-- Maximum of the section gauge and the centre cube gauge, pulled back to
the standard coordinates of the initial presentation. -/
def sharpProductSeminorm
    (N : CoveredNormalizedReplacement (D := D)
      (K := Section90IntegerInitialization.integerSet A)
      (coverConstant := coverConstant) constant scale sigma)
    (S : SharpSectionData N) :
    Seminorm ℝ (Fin (initialRank N) → ℝ) :=
  (S.seminorm.comp ((LinearMap.fst ℝ _ _).comp
      (splitLinearEquiv ℝ N).toLinearMap)) ⊔
    ((centerSeminorm N).comp ((LinearMap.snd ℝ _ _).comp
      (splitLinearEquiv ℝ N).toLinearMap))

@[simp] theorem sharpProductSeminorm_apply
    (N : CoveredNormalizedReplacement (D := D)
      (K := Section90IntegerInitialization.integerSet A)
      (coverConstant := coverConstant) constant scale sigma)
    (S : SharpSectionData N) (x : Fin (initialRank N) → ℝ) :
    sharpProductSeminorm N S x =
      max (S.seminorm (splitLinearEquiv ℝ N x).1)
        ‖(splitLinearEquiv ℝ N x).2‖ := by
  rfl

theorem sharpProductSeminorm_definite
    (N : CoveredNormalizedReplacement (D := D)
      (K := Section90IntegerInitialization.integerSet A)
      (coverConstant := coverConstant) constant scale sigma)
    (S : SharpSectionData N) :
    IsDefinite (sharpProductSeminorm N S) := by
  intro x hx
  rw [sharpProductSeminorm_apply] at hx
  have hmax :
      max (S.seminorm (splitLinearEquiv ℝ N x).1)
          ‖(splitLinearEquiv ℝ N x).2‖ ≤ 0 := hx.le
  have hparts := max_le_iff.mp hmax
  have hfirstZero : S.seminorm (splitLinearEquiv ℝ N x).1 = 0 :=
    le_antisymm hparts.1 (apply_nonneg S.seminorm _)
  have hsecondZero : ‖(splitLinearEquiv ℝ N x).2‖ = 0 :=
    le_antisymm hparts.2 (norm_nonneg _)
  have hfirst : (splitLinearEquiv ℝ N x).1 = 0 :=
    S.definite _ hfirstZero
  have hsecond : (splitLinearEquiv ℝ N x).2 = 0 :=
    norm_eq_zero.mp hsecondZero
  apply (splitLinearEquiv ℝ N).injective
  calc
    splitLinearEquiv ℝ N x = (0, 0) := Prod.ext hfirst hsecond
    _ = splitLinearEquiv ℝ N 0 := (map_zero (splitLinearEquiv ℝ N)).symm

/-- Integer coordinates of one source lift furnished by the covering
certificate. -/
def sharpLift
    (N : CoveredNormalizedReplacement (D := D)
      (K := Section90IntegerInitialization.integerSet A)
      (coverConstant := coverConstant) constant scale sigma)
    (c : N.cover.centers) (z : D.latticePoints) :
    IntegralPoint (initialRank N) :=
  (splitLinearEquiv ℤ N).symm
    ((coordinateIntegralBasis (D := D)).equivFun
      (coordinateLatticeEquiv D z), Pi.single c 1)

/-- The literal integral map in the same product coordinates as the sharp
seminorm. -/
noncomputable def sharpIntegralMap
    (N : CoveredNormalizedReplacement (D := D)
      (K := Section90IntegerInitialization.integerSet A)
      (coverConstant := coverConstant) constant scale sigma) :
    IntegralPoint (initialRank N) →+ IntegralPoint 1 where
  toFun z :=
    oldLatticeMap (D := D)
        ((coordinateIntegralBasis (D := D)).equivFun.symm
          (splitLinearEquiv ℤ N z).1) +
      centersLinearCombination N (splitLinearEquiv ℤ N z).2
  map_zero' := by simp
  map_add' x y := by
    change oldLatticeMap (D := D)
          ((coordinateIntegralBasis (D := D)).equivFun.symm
            ((splitLinearEquiv ℤ N x).1 + (splitLinearEquiv ℤ N y).1)) +
        centersLinearCombination N
          ((splitLinearEquiv ℤ N x).2 + (splitLinearEquiv ℤ N y).2) = _
    rw [map_add, map_add, map_add]
    abel

/-- Integer-valued map obtained by evaluating the one-dimensional target
of `sharpIntegralMap`. -/
noncomputable def sharpIntegerMap
    (N : CoveredNormalizedReplacement (D := D)
      (K := Section90IntegerInitialization.integerSet A)
      (coverConstant := coverConstant) constant scale sigma) :
    IntegralPoint (initialRank N) →+ ℤ :=
  singletonValue.comp (sharpIntegralMap N)

@[simp] theorem sharpIntegralMap_sharpLift
    (N : CoveredNormalizedReplacement (D := D)
      (K := Section90IntegerInitialization.integerSet A)
      (coverConstant := coverConstant) constant scale sigma)
    (c : N.cover.centers) (z : D.latticePoints) :
    sharpIntegralMap N (sharpLift N c z) =
      latticeHead D z + (c : IntegralPoint 1) := by
  change oldLatticeMap (D := D)
        ((coordinateIntegralBasis (D := D)).equivFun.symm
          (splitLinearEquiv ℤ N (sharpLift N c z)).1) +
      centersLinearCombination N
        (splitLinearEquiv ℤ N (sharpLift N c z)).2 = _
  rw [show splitLinearEquiv ℤ N (sharpLift N c z) =
      ((coordinateIntegralBasis (D := D)).equivFun
        (coordinateLatticeEquiv D z), Pi.single c 1) by
    exact (splitLinearEquiv ℤ N).apply_symm_apply _]
  change oldLatticeMap (D := D)
        ((coordinateIntegralBasis (D := D)).equivFun.symm
          ((coordinateIntegralBasis (D := D)).equivFun
            (coordinateLatticeEquiv D z))) +
      centersLinearCombination N (Pi.single c 1) = _
  rw [LinearEquiv.symm_apply_apply,
    oldLatticeMap_coordinateLatticeEquiv,
    centersLinearCombination_single]

@[simp] theorem sharpIntegerMap_sharpLift
    (N : CoveredNormalizedReplacement (D := D)
      (K := Section90IntegerInitialization.integerSet A)
      (coverConstant := coverConstant) constant scale sigma)
    (c : N.cover.centers) (z : D.latticePoints) :
    sharpIntegerMap N (sharpLift N c z) =
      singletonValue (latticeHead D z + (c : IntegralPoint 1)) := by
  change singletonValue (sharpIntegralMap N (sharpLift N c z)) = _
  rw [sharpIntegralMap_sharpLift]

theorem exists_sharpLift
    (N : CoveredNormalizedReplacement (D := D)
      (K := Section90IntegerInitialization.integerSet A)
      (coverConstant := coverConstant) constant scale sigma)
    (S : SharpSectionData N) (x : ℤ) (hx : x ∈ A) :
    ∃ z : IntegralPoint (initialRank N),
      sharpProductSeminorm N S (integralEmbed z) ≤ 1 ∧
        sharpIntegerMap N z = x := by
  have hxK : Section90IntegerInitialization.singletonPoint x ∈
      Section90IntegerInitialization.integerSet A :=
    Finset.mem_image.mpr ⟨x, hx, rfl⟩
  obtain ⟨c, hc, u, v, hcover⟩ := N.cover_lift _ hxK
  let c' : N.cover.centers := ⟨c, hc⟩
  let z : D.latticePoints :=
    Section91CoveringEnlargement.Lemma45SectionSeed.differenceLift
      N.normalized.seed u v
  refine ⟨sharpLift N c' z, ?_, ?_⟩
  · rw [sharpProductSeminorm_apply, splitLinearEquiv_integralEmbed]
    simp only [sharpLift, LinearEquiv.apply_symm_apply, max_le_iff]
    refine ⟨S.difference_mem u v, ?_⟩
    rw [show (fun c => ((Pi.single c' 1 :
      N.cover.centers → ℤ) c : ℝ)) = Pi.single c' (1 : ℝ) by
        ext c
        simp only [Pi.single_apply]
        split <;> simp_all]
    rw [Pi.norm_single]
    norm_num
  · rw [sharpIntegerMap_sharpLift]
    change singletonValue (latticeHead D z + (c : IntegralPoint 1)) = x
    rw [add_comm, ← hcover, singletonValue_singletonPoint]

end

end Erdos186.CFP.Bilu.Section91SharpProductPresentation
