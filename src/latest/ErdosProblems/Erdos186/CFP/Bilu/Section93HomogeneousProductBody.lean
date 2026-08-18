/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.Section93HomogeneousAffineSpan
import ErdosProblems.Erdos186.CFP.Bilu.Section93LatticeSectionCoordinates

/-!
# Bilu Section 9.3: the homogeneous product body

To restrict a presentation to the affine span of its selected lifts without
translating the target map, we homogenize both its lattice and its body.  The
body is the product of the old unit ball and `[-1,1]`; every `(z,1)` lift is
therefore retained and the additive presentation map simply forgets the
last coordinate.
-/

namespace Erdos186.CFP.Bilu.Section93HomogeneousProductBody

open Set Module Submodule MeasureTheory
open Mahler MinkowskiSecond MinkowskiUpper
open Proposition75Case2Construction SubspaceLattice
open Section4PresentationLiftSet Section92PresentationDescent
open Section93HomogeneousAffineSpan Section93LatticeSectionCoordinates

noncomputable section

set_option autoImplicit false

variable {A : Finset ℤ} {n : ℕ}

/-- First block of a homogeneous real coordinate vector. -/
def homogeneousHeadReal :
    EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] (Fin n → ℝ) where
  toFun x i := x (Fin.castAdd 1 i)
  map_add' x y := by ext i; rfl
  map_smul' c x := by ext i; rfl

/-- Last coordinate of a homogeneous real coordinate vector. -/
def homogeneousLastReal :
    EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] ℝ where
  toFun x := x (Fin.natAdd n 0)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Product of the old seminorm with the absolute-value seminorm on the
homogeneous coordinate. -/
def homogeneousProductSeminorm (X : BodyPresentation A n) :
    Seminorm ℝ (EuclideanSpace ℝ (Fin (n + 1))) :=
  X.seminorm.comp homogeneousHeadReal ⊔
    (normSeminorm ℝ ℝ).comp homogeneousLastReal

@[simp] theorem homogeneousProductSeminorm_apply
    (X : BodyPresentation A n) (x : EuclideanSpace ℝ (Fin (n + 1))) :
    homogeneousProductSeminorm X x =
      max (X.seminorm (homogeneousHeadReal x))
        ‖homogeneousLastReal x‖ := rfl

theorem homogeneousHeadReal_homogeneousRealPoint
    (z : IntegralPoint n) :
    homogeneousHeadReal (homogeneousRealPoint z) = integralEmbed z := by
  ext i
  simp [homogeneousHeadReal, homogeneousRealPoint,
    homogeneousIntegralPoint, joinIntegralCoordinates, integralEmbed,
    integralReal]

@[simp] theorem homogeneousLastReal_homogeneousRealPoint
    (z : IntegralPoint n) :
    homogeneousLastReal (homogeneousRealPoint z) = 1 := by
  change (homogeneousRealPoint z) (Fin.natAdd n 0) = 1
  simp [homogeneousLastReal, homogeneousRealPoint,
    homogeneousIntegralPoint, joinIntegralCoordinates, integralReal,
    finSumFinEquiv_symm_apply_natAdd]

theorem homogeneousProductSeminorm_homogeneousRealPoint_le_one
    (X : BodyPresentation A n) {z : IntegralPoint n}
    (hz : X.seminorm (integralEmbed z) ≤ 1) :
    homogeneousProductSeminorm X (homogeneousRealPoint z) ≤ 1 := by
  rw [homogeneousProductSeminorm_apply,
    homogeneousHeadReal_homogeneousRealPoint,
    homogeneousLastReal_homogeneousRealPoint, norm_one, max_le_iff]
  exact ⟨hz, le_rfl⟩

theorem homogeneousProductSeminorm_definite
    (X : BodyPresentation A n) :
    ∀ x, homogeneousProductSeminorm X x = 0 → x = 0 := by
  intro x hx
  rw [homogeneousProductSeminorm_apply] at hx
  have hparts := max_le_iff.mp hx.le
  have hheadZero : homogeneousHeadReal x = 0 := by
    apply X.definite
    exact le_antisymm hparts.1 (apply_nonneg X.seminorm _)
  have hlastZero : homogeneousLastReal x = 0 := by
    exact norm_eq_zero.mp <| le_antisymm hparts.2 (norm_nonneg _)
  ext j
  generalize hs : finSumFinEquiv.symm j = s
  cases s with
  | inl i =>
      have hi := congrFun hheadZero i
      have hj : j = Fin.castAdd 1 i := by
        apply finSumFinEquiv.symm.injective
        rw [hs, finSumFinEquiv_symm_apply_castAdd]
      rw [hj]
      exact hi
  | inr i =>
      have hi := hlastZero
      have hi0 : i = (0 : Fin 1) := Subsingleton.elim _ _
      subst i
      have hj : j = Fin.natAdd n 0 := by
        apply finSumFinEquiv.symm.injective
        rw [hs, finSumFinEquiv_symm_apply_natAdd]
      rw [hj]
      exact hi

/-- First block of a homogeneous integral vector. -/
def homogeneousHeadIntegral : IntegralPoint (n + 1) →+ IntegralPoint n where
  toFun := integralHeadCoordinates
  map_zero' := by ext i; rfl
  map_add' _ _ := by ext i; rfl

@[simp] theorem homogeneousHeadIntegral_homogeneousIntegralPoint
    (z : IntegralPoint n) :
    homogeneousHeadIntegral (homogeneousIntegralPoint z) = z := by
  ext i
  simp [homogeneousHeadIntegral, homogeneousIntegralPoint,
    integralHeadCoordinates, joinIntegralCoordinates]

/-- The homogeneous presentation map forgets the last coordinate. -/
def homogeneousIntegerMap (X : BodyPresentation A n) :
    IntegralPoint (n + 1) →+ ℤ :=
  X.map.comp homogeneousHeadIntegral

@[simp] theorem homogeneousIntegerMap_homogeneousIntegralPoint
    (X : BodyPresentation A n) (z : IntegralPoint n) :
    homogeneousIntegerMap X (homogeneousIntegralPoint z) = X.map z := by
  simp [homogeneousIntegerMap]

/-- Every chosen source lift is retained by the homogeneous product body. -/
theorem homogeneousPresentationLift_mem_unitBall
    (X : BodyPresentation A n) (a : ℤ) (ha : a ∈ A) :
    homogeneousProductSeminorm X
      (homogeneousRealPoint
        (presentationLift ⟨n, X⟩ ⟨a, ha⟩)) ≤ 1 := by
  apply homogeneousProductSeminorm_homogeneousRealPoint_le_one
  exact presentationLift_mem_unitBall ⟨n, X⟩ ⟨a, ha⟩

@[simp] theorem homogeneousIntegerMap_presentationLift
    (X : BodyPresentation A n) (a : ℤ) (ha : a ∈ A) :
    homogeneousIntegerMap X
      (homogeneousIntegralPoint
        (presentationLift ⟨n, X⟩ ⟨a, ha⟩)) = a := by
  rw [homogeneousIntegerMap_homogeneousIntegralPoint]
  exact map_presentationLift ⟨n, X⟩ ⟨a, ha⟩

/-! ## Positive volume for definite finite-dimensional seminorm balls -/

theorem standardRadius_pos_of_definite
    {d : ℕ} (hd : 0 < d) (p : Seminorm ℝ (Fin d → ℝ))
    (hp : IsDefinite p) :
    0 < standardRadius p := by
  apply lt_of_le_of_ne (standardRadius_nonneg p)
  intro hzero
  have hC : standardRadius p = 0 := hzero.symm
  let i : Fin d := ⟨0, hd⟩
  let e : Fin d → ℝ := Pi.single i 1
  have hpe : p e = 0 := by
    apply le_antisymm ?_ (apply_nonneg p _)
    calc
      p e ≤ standardRadius p * ‖e‖ :=
        apply_le_standardRadius_mul_norm p e
      _ = 0 := by rw [hC, zero_mul]
  have he := hp e hpe
  have hi := congrFun he i
  simp [e, i] at hi

theorem unitBall_volumeReal_pos_of_definite
    {d : ℕ} (hd : 0 < d) (p : Seminorm ℝ (Fin d → ℝ))
    (hp : IsDefinite p) :
    0 < volume.real {x : Fin d → ℝ | p x ≤ 1} := by
  let r : ℝ := (standardRadius p)⁻¹
  have hC : 0 < standardRadius p :=
    standardRadius_pos_of_definite hd p hp
  have hr : 0 < r := inv_pos.mpr hC
  have hball : Metric.closedBall (0 : Fin d → ℝ) r ⊆
      {x : Fin d → ℝ | p x ≤ 1} := by
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right] at hx
    calc
      p x ≤ standardRadius p * ‖x‖ :=
        apply_le_standardRadius_mul_norm p x
      _ ≤ standardRadius p * r :=
        mul_le_mul_of_nonneg_left hx hC.le
      _ = 1 := by simp [r, hC.ne']
  apply ENNReal.toReal_pos
  · exact ne_of_gt ((Metric.measure_closedBall_pos volume 0 hr).trans_le
      (measure_mono hball))
  · exact ((isBounded_unitBall p hp).measure_lt_top).ne

end

end Erdos186.CFP.Bilu.Section93HomogeneousProductBody

#print axioms
  Erdos186.CFP.Bilu.Section93HomogeneousProductBody.homogeneousProductSeminorm_definite
#print axioms
  Erdos186.CFP.Bilu.Section93HomogeneousProductBody.homogeneousPresentationLift_mem_unitBall
