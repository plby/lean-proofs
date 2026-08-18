/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.Section4PresentationLiftSet
import ErdosProblems.Erdos186.CFP.Bilu.Section8PolarVolumeProduct
import ErdosProblems.Erdos186.CFP.Bilu.Section7AffineSlice

/-!
# Mahler coordinates for a body presentation

Proposition 7.5 is stated with a fixed Euclidean inball.  An arbitrary
appropriate presentation need not contain such an inball in the standard
coordinates.  We therefore pass to an integral Mahler basis and enlarge the
body by the rank.  This is a unimodular change of lattice coordinates and
costs only the dimension factor `rank ^ rank` in volume.
-/

namespace Erdos186.CFP.Bilu.Section8PresentationNormalization

open scoped Pointwise BigOperators NNReal
open MeasureTheory
open CFP.BiluFreiman
open Module Mahler MahlerOuterContainer MinkowskiSecond
  MinkowskiSecond.Direct MinkowskiUpper
open Section4PresentationLiftSet Section92PresentationDescent
open Section7FreimanMap Section7AffineSlice
open SubspaceLattice

noncomputable section

set_option autoImplicit false

variable {A : Finset ℤ}

/-- A chosen Mahler basis for the seminorm of a body presentation. -/
def presentationMahlerBasis (X : RankedBodyPresentation A) :
    Basis (Fin X.1) ℤ (IntegralPoint X.1) :=
  (exists_isMahlerBasis X.2.seminorm X.2.definite).choose

theorem presentationMahlerBasis_isMahler
    (X : RankedBodyPresentation A) :
    IsMahlerBasis X.2.seminorm (presentationMahlerBasis X) :=
  (exists_isMahlerBasis X.2.seminorm X.2.definite).choose_spec

/-- The rank-dilated pullback of the current seminorm to Mahler
coordinates. -/
def normalizedMahlerSeminorm (X : RankedBodyPresentation A) :
    Seminorm ℝ (Fin X.1 → ℝ) :=
  diagonalPullbackSeminorm
    (inBasisSeminorm X.2.seminorm (presentationMahlerBasis X))
    (fun _ ↦ (X.1 : ℝ))

@[simp] theorem normalizedMahlerSeminorm_apply
    (X : RankedBodyPresentation A) (x : Fin X.1 → ℝ) :
    normalizedMahlerSeminorm X x =
      inBasisSeminorm X.2.seminorm (presentationMahlerBasis X)
        (fun i ↦ (X.1 : ℝ)⁻¹ * x i) := by
  rw [normalizedMahlerSeminorm, diagonalPullbackSeminorm_apply]

theorem normalizedMahlerSeminorm_definite
    (X : RankedBodyPresentation A) :
    IsDefinite (normalizedMahlerSeminorm X) := by
  apply isDefinite_diagonalPullbackSeminorm
    (inBasisSeminorm X.2.seminorm (presentationMahlerBasis X))
    (isDefinite_inBasisSeminorm X.2.seminorm X.2.definite
      (presentationMahlerBasis X))
  intro i
  exact_mod_cast X.2.rank_pos

/-- Integral Mahler coordinates. -/
def mahlerCoordinates (X : RankedBodyPresentation A) :
    IntegralPoint X.1 ≃+ IntegralPoint X.1 :=
  (presentationMahlerBasis X).equivFun.toAddEquiv

@[simp] theorem normalizedMahlerSeminorm_integralCoordinates
    (X : RankedBodyPresentation A) (z : IntegralPoint X.1) :
    normalizedMahlerSeminorm X
        (integralEmbed (mahlerCoordinates X z)) =
      (X.1 : ℝ)⁻¹ * X.2.seminorm (integralEmbed z) := by
  rw [normalizedMahlerSeminorm_apply]
  have hn : (X.1 : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt X.2.rank_pos)
  have hcoords :
      (fun i ↦ (X.1 : ℝ)⁻¹ * integralEmbed (mahlerCoordinates X z) i) =
        (X.1 : ℝ)⁻¹ • integralEmbed (mahlerCoordinates X z) := by
    rfl
  rw [hcoords, map_smul_eq_mul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (by exact_mod_cast X.2.rank_pos))]
  rw [inBasisSeminorm_integral_coords]
  change (X.1 : ℝ)⁻¹ * X.2.seminorm
    (integralEmbed ((presentationMahlerBasis X).equivFun.symm
      ((presentationMahlerBasis X).equivFun z))) = _
  rw [(presentationMahlerBasis X).equivFun.symm_apply_apply]

/-- Every standard basis vector lies in the normalized unit ball. -/
theorem normalizedMahlerSeminorm_standard_le_one
    (X : RankedBodyPresentation A) (i : Fin X.1) :
    normalizedMahlerSeminorm X
        (integralEmbed (standardIntegralPoint i)) ≤ 1 := by
  have hmin : successiveMinimum X.2.seminorm i ≤ 1 :=
    successiveMinimum_le_one_of_admitsIndependent_full
      X.2.seminorm X.2.full i
  have hbasis : X.2.seminorm
      (integralEmbed (presentationMahlerBasis X i)) ≤ (X.1 : ℝ) := by
    exact (presentationMahlerBasis_isMahler X).le_rank_mul_successiveMinimum i
      |>.trans (by
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hmin (by positivity : (0 : ℝ) ≤ X.1))
  rw [normalizedMahlerSeminorm_apply]
  have heq :
      (fun j ↦ (X.1 : ℝ)⁻¹ * integralEmbed (standardIntegralPoint i) j) =
        (X.1 : ℝ)⁻¹ • integralEmbed (standardIntegralPoint i) := by
    rfl
  rw [heq, map_smul_eq_mul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (by exact_mod_cast X.2.rank_pos)),
    inBasisSeminorm_integral_coords]
  have hinv : (0 : ℝ) ≤ (X.1 : ℝ)⁻¹ := (inv_pos.mpr (by
    exact_mod_cast X.2.rank_pos)).le
  calc
    (X.1 : ℝ)⁻¹ * X.2.seminorm
        (integralEmbed ((presentationMahlerBasis X).equivFun.symm
          (standardIntegralPoint i))) =
        (X.1 : ℝ)⁻¹ * X.2.seminorm
          (integralEmbed (presentationMahlerBasis X i)) := by
            congr 2
            have hz :
                (presentationMahlerBasis X).equivFun.symm
                    (standardIntegralPoint i) =
                  presentationMahlerBasis X i := by
              apply (presentationMahlerBasis X).equivFun.injective
              rw [(presentationMahlerBasis X).equivFun.apply_symm_apply]
              ext j
              simp [standardIntegralPoint, Pi.single, Function.update,
                eq_comm]
            exact congrArg integralEmbed hz
    _ ≤ (X.1 : ℝ)⁻¹ * (X.1 : ℝ) :=
      mul_le_mul_of_nonneg_left hbasis hinv
    _ = 1 := inv_mul_cancel₀ (by exact_mod_cast (ne_of_gt X.2.rank_pos))

/-- The standard-radius bound which supplies Proposition 7.5's fixed
Euclidean inball. -/
theorem standardRadius_normalizedMahlerSeminorm_le_rank
    (X : RankedBodyPresentation A) :
    standardRadius (normalizedMahlerSeminorm X) ≤ (X.1 : ℝ) := by
  unfold standardRadius
  calc
    (∑ i : Fin X.1, normalizedMahlerSeminorm X
        (integralEmbed (standardIntegralPoint i))) ≤
        ∑ _i : Fin X.1, (1 : ℝ) :=
      Finset.sum_le_sum fun i _ ↦ normalizedMahlerSeminorm_standard_le_one X i
    _ = (X.1 : ℝ) := by simp

/-- Exact volume cost of the rank dilation and unimodular change of
coordinates. -/
theorem volume_normalizedMahlerUnitBall
    (X : RankedBodyPresentation A) :
    volume (unitBall (normalizedMahlerSeminorm X)) =
      ENNReal.ofReal ((X.1 : ℝ) ^ X.1) *
        volume (unitBall X.2.seminorm) := by
  rw [normalizedMahlerSeminorm,
    volume_unitBall_diagonalPullback _ (fun _ ↦ (X.1 : ℝ))
      (fun _ ↦ by exact_mod_cast X.2.rank_pos),
    volume_unitBall_inBasisSeminorm]
  congr 2
  simp

/-- The selected source lifts, written in normalized Mahler coordinates. -/
def normalizedLiftSet (X : RankedBodyPresentation A) :
    Finset (IntegralPoint X.1) :=
  (presentationLiftSet X).image (mahlerCoordinates X)

@[simp] theorem card_normalizedLiftSet
    (X : RankedBodyPresentation A) :
    (normalizedLiftSet X).card = A.card := by
  rw [normalizedLiftSet,
    Finset.card_image_of_injective _ (mahlerCoordinates X).injective,
    card_presentationLiftSet]

theorem card_pairSumset_normalizedLiftSet_eq_twoA
    (s : ℕ) (hs : 0 < s) (X : RankedBodyPresentation A)
    (hX : EnlargedInjective s X) :
    (normalizedLiftSet X + normalizedLiftSet X).card = (twoA A).card := by
  change (pairSumset (normalizedLiftSet X)).card = (twoA A).card
  rw [normalizedLiftSet,
    card_pairSumset_image_eq (mahlerCoordinates X)
      (mahlerCoordinates X).injective (mahlerCoordinates X).map_add]
  change (presentationLiftSet X + presentationLiftSet X).card =
    (twoA A).card
  exact card_pairSumset_presentationLiftSet_eq_twoA s hs X hX

theorem normalizedLiftSet_subset_unitBall
    (X : RankedBodyPresentation A) :
    ↑(normalizedLiftSet X) ⊆
      {z : IntegralPoint X.1 |
        normalizedMahlerSeminorm X (integralEmbed z) ≤ 1} := by
  intro z hz
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
  change normalizedMahlerSeminorm X
    (integralEmbed (mahlerCoordinates X w)) ≤ 1
  rw [normalizedMahlerSeminorm_integralCoordinates]
  have hw' := presentationLiftSet_subset_unitBall X hw
  have hn : (1 : ℝ) ≤ X.1 := by exact_mod_cast X.2.rank_pos
  calc
    (X.1 : ℝ)⁻¹ * X.2.seminorm (integralEmbed w) ≤
        (X.1 : ℝ)⁻¹ * 1 :=
      mul_le_mul_of_nonneg_left hw'
        (inv_nonneg.mpr (by positivity : (0 : ℝ) ≤ X.1))
    _ ≤ 1 := by
      simpa only [mul_one] using
        (inv_le_one₀ (by positivity : (0 : ℝ) < X.1)).mpr hn

/-- The normalized seminorm transported to Euclidean space. -/
def euclideanNormalizedSeminorm (X : RankedBodyPresentation A) :
    Seminorm ℝ (EuclideanSpace ℝ (Fin X.1)) :=
  (normalizedMahlerSeminorm X).comp
    (EuclideanSpace.equiv (Fin X.1) ℝ).toLinearMap

/-- The symmetric convex Euclidean body supplied to Proposition 7.5. -/
def normalizedEuclideanBody (X : RankedBodyPresentation A) :
    Set (EuclideanSpace ℝ (Fin X.1)) :=
  (euclideanNormalizedSeminorm X).closedBall 0 1

theorem normalizedEuclideanBody_preimage
    (X : RankedBodyPresentation A) :
    normalizedEuclideanBody X =
      (EuclideanSpace.equiv (Fin X.1) ℝ) ⁻¹'
        unitBall (normalizedMahlerSeminorm X) := by
  ext x
  simp [normalizedEuclideanBody, euclideanNormalizedSeminorm,
    unitBall, Seminorm.mem_closedBall]

theorem balanced_normalizedEuclideanBody
    (X : RankedBodyPresentation A) :
    Balanced ℝ (normalizedEuclideanBody X) :=
  (euclideanNormalizedSeminorm X).balanced_closedBall_zero 1

theorem convex_normalizedEuclideanBody
    (X : RankedBodyPresentation A) :
    Convex ℝ (normalizedEuclideanBody X) :=
  (euclideanNormalizedSeminorm X).convex_closedBall 0 1

theorem measurableSet_normalizedEuclideanBody
    (X : RankedBodyPresentation A) :
    MeasurableSet (normalizedEuclideanBody X) := by
  rw [normalizedEuclideanBody_preimage]
  exact (measurableSet_unitBall (normalizedMahlerSeminorm X)).preimage
    (EuclideanSpace.equiv (Fin X.1) ℝ).continuous.measurable

theorem isCompact_normalizedEuclideanBody
    (X : RankedBodyPresentation A) :
    IsCompact (normalizedEuclideanBody X) := by
  rw [normalizedEuclideanBody_preimage]
  exact (EuclideanSpace.equiv (Fin X.1) ℝ).toHomeomorph.isCompact_preimage.mpr
    (Metric.isCompact_iff_isClosed_bounded.mpr
      ⟨isClosed_unitBall (normalizedMahlerSeminorm X),
        isBounded_unitBall (normalizedMahlerSeminorm X)
          (normalizedMahlerSeminorm_definite X)⟩)

theorem ofLp_image_normalizedEuclideanBody
    (X : RankedBodyPresentation A) :
    WithLp.ofLp '' normalizedEuclideanBody X =
      unitBall (normalizedMahlerSeminorm X) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [normalizedEuclideanBody_preimage] at hx
    exact hx
  · intro hy
    refine ⟨WithLp.toLp 2 y, ?_, WithLp.ofLp_toLp (p := 2) y⟩
    rw [normalizedEuclideanBody_preimage]
    simpa using hy

theorem volume_normalizedEuclideanBody
    (X : RankedBodyPresentation A) :
    volume (normalizedEuclideanBody X) =
      volume (unitBall (normalizedMahlerSeminorm X)) := by
  rw [normalizedEuclideanBody_preimage]
  exact (PiLp.volume_preserving_ofLp (Fin X.1)).measure_preimage
    (isClosed_unitBall (normalizedMahlerSeminorm X)).measurableSet.nullMeasurableSet

/-- Every normalized source lift lies in the transported Euclidean body. -/
theorem integralReal_mem_normalizedEuclideanBody
    (X : RankedBodyPresentation A) {z : IntegralPoint X.1}
    (hz : z ∈ normalizedLiftSet X) :
    integralReal z ∈ normalizedEuclideanBody X := by
  rw [normalizedEuclideanBody_preimage]
  change normalizedMahlerSeminorm X (integralEmbed z) ≤ 1
  exact normalizedLiftSet_subset_unitBall X hz

/-- The body contains the fixed inball required by Proposition 7.5. -/
theorem closedBall_subset_two_smul_normalizedEuclideanBody
    (X : RankedBodyPresentation A) :
    Metric.closedBall (0 : EuclideanSpace ℝ (Fin X.1))
        (((X.1 : ℝ) + 1)⁻¹) ⊆
      (2 : ℝ) • normalizedEuclideanBody X := by
  intro x hx
  apply (balanced_normalizedEuclideanBody X).subset_smul (by norm_num)
  rw [normalizedEuclideanBody_preimage]
  change normalizedMahlerSeminorm X (WithLp.ofLp x) ≤ 1
  have hnormx : ‖x‖ ≤ ((X.1 : ℝ) + 1)⁻¹ := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hx
  haveI : Nonempty (Fin X.1) := ⟨⟨0, X.2.rank_pos⟩⟩
  have hofLp : ‖WithLp.ofLp x‖ ≤ ‖x‖ := by
    rw [pi_norm_le_iff_of_nonempty]
    intro i
    exact PiLp.norm_apply_le x i
  have hstd := apply_le_standardRadius_mul_norm
    (normalizedMahlerSeminorm X) (WithLp.ofLp x)
  have hrank := standardRadius_normalizedMahlerSeminorm_le_rank X
  have hnonneg : 0 ≤ standardRadius (normalizedMahlerSeminorm X) :=
    standardRadius_nonneg _
  have hn : (0 : ℝ) ≤ X.1 := by positivity
  calc
    normalizedMahlerSeminorm X (WithLp.ofLp x) ≤
        standardRadius (normalizedMahlerSeminorm X) * ‖WithLp.ofLp x‖ := hstd
    _ ≤ (X.1 : ℝ) * ‖x‖ :=
      mul_le_mul hrank hofLp (norm_nonneg _) hn
    _ ≤ (X.1 : ℝ) * ((X.1 : ℝ) + 1)⁻¹ :=
      mul_le_mul_of_nonneg_left hnormx hn
    _ ≤ 1 := by
      rw [← div_eq_mul_inv]
      exact (div_le_one (by positivity : (0 : ℝ) < X.1 + 1)).2 (by linarith)

end

end Erdos186.CFP.Bilu.Section8PresentationNormalization

#print axioms
  Erdos186.CFP.Bilu.Section8PresentationNormalization.standardRadius_normalizedMahlerSeminorm_le_rank
#print axioms
  Erdos186.CFP.Bilu.Section8PresentationNormalization.volume_normalizedMahlerUnitBall
