/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.Section93NormalizedAffineBodyPresentation
import ErdosProblems.Erdos186.CFP.Bilu.Section93LatticeSectionVolume
import ErdosProblems.Erdos186.CFP.Bilu.Section93CentralSectionVolume

/-!
# Volume of the normalized affine restriction

This file supplies the exact product-volume formula in the codimension-zero
branch and the exact covolume formula in the proper affine-section branch.
The remaining inequality is the central-section estimate applied to the
normalized product body.
-/

namespace Erdos186.CFP.Bilu.Section93NormalizedAffineVolume

open scoped Pointwise
open Set MeasureTheory Module Submodule
open CFP.BiluFreiman
open Mahler MinkowskiSecond MinkowskiUpper
open Section8PresentationNormalization Section92PresentationDescent
open Section93HomogeneousAffineSpan Section93HomogeneousProductBody
open Section93LatticeSectionCoordinates Section93LatticeSectionVolume
open Section93NormalizedAffineBodyPresentation SubspaceLattice
open VolumeSections

noncomputable section

set_option autoImplicit false

variable {A : Finset ℤ}

/-- The normalized Mahler unit ball with one homogeneous coordinate. -/
def normalizedHomogeneousUnitBall (X : RankedBodyPresentation A) :
    Set (EuclideanSpace ℝ (Fin (X.1 + 1))) :=
  {x | normalizedHomogeneousProductSeminorm X x ≤ 1}

theorem normalizedHomogeneousUnitBall_preimage
    (X : RankedBodyPresentation A) :
    normalizedHomogeneousUnitBall X =
      (EuclideanSpace.equiv (Fin (X.1 + 1)) ℝ) ⁻¹'
        unitBall (normalizedTopProductSeminorm X) := by
  rfl

theorem convex_normalizedHomogeneousUnitBall
    (X : RankedBodyPresentation A) :
    Convex ℝ (normalizedHomogeneousUnitBall X) := by
  have heq : normalizedHomogeneousUnitBall X =
      (normalizedHomogeneousProductSeminorm X).closedBall 0 1 := by
    ext x
    exact (normalizedHomogeneousProductSeminorm X).mem_closedBall_zero.symm
  rw [heq]
  exact (normalizedHomogeneousProductSeminorm X).convex_closedBall 0 1

theorem isCompact_normalizedHomogeneousUnitBall
    (X : RankedBodyPresentation A) :
    IsCompact (normalizedHomogeneousUnitBall X) := by
  rw [normalizedHomogeneousUnitBall_preimage]
  apply (EuclideanSpace.equiv (Fin (X.1 + 1)) ℝ).toHomeomorph.isCompact_preimage.mpr
  exact Metric.isCompact_iff_isClosed_bounded.mpr
    ⟨isClosed_unitBall (normalizedTopProductSeminorm X),
      isBounded_unitBall (normalizedTopProductSeminorm X)
        (normalizedTopProductSeminorm_definite X)⟩

theorem measurableSet_normalizedHomogeneousUnitBall
    (X : RankedBodyPresentation A) :
    MeasurableSet (normalizedHomogeneousUnitBall X) :=
  (isCompact_normalizedHomogeneousUnitBall X).isClosed.measurableSet

theorem volume_normalizedHomogeneousUnitBall
    (X : RankedBodyPresentation A) :
    volume (normalizedHomogeneousUnitBall X) =
      volume (unitBall (normalizedTopProductSeminorm X)) := by
  rw [normalizedHomogeneousUnitBall_preimage]
  exact (PiLp.volume_preserving_ofLp (Fin (X.1 + 1))).measure_preimage
    (measurableSet_unitBall (normalizedTopProductSeminorm X)).nullMeasurableSet

/-- The normalized homogeneous product contains a centered Euclidean ball
of radius `(rank+1)⁻¹`. -/
theorem closedBall_subset_normalizedHomogeneousUnitBall
    (X : RankedBodyPresentation A) :
    Metric.closedBall (0 : EuclideanSpace ℝ (Fin (X.1 + 1)))
        (((X.1 : ℝ) + 1)⁻¹) ⊆
      normalizedHomogeneousUnitBall X := by
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right] at hx
  have hrank : (0 : ℝ) < X.1 := by exact_mod_cast X.2.rank_pos
  have hradius : (0 : ℝ) < ((X.1 : ℝ) + 1)⁻¹ := by positivity
  haveI : Nonempty (Fin X.1) := ⟨⟨0, X.2.rank_pos⟩⟩
  have hheadNorm : ‖homogeneousHeadReal x‖ ≤ ‖x‖ := by
    rw [pi_norm_le_iff_of_nonempty]
    intro i
    change |x (Fin.castAdd 1 i)| ≤ ‖x‖
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le x (Fin.castAdd 1 i)
  have hlastNorm : ‖homogeneousLastReal x‖ ≤ ‖x‖ := by
    change |x (Fin.natAdd X.1 0)| ≤ ‖x‖
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le x (Fin.natAdd X.1 0)
  have hhead := apply_le_standardRadius_mul_norm
    (normalizedMahlerSeminorm X) (homogeneousHeadReal x)
  have hstd := standardRadius_normalizedMahlerSeminorm_le_rank X
  have hstdNonneg : 0 ≤ standardRadius (normalizedMahlerSeminorm X) :=
    standardRadius_nonneg _
  have hheadOne : normalizedMahlerSeminorm X (homogeneousHeadReal x) ≤ 1 := by
    calc
      normalizedMahlerSeminorm X (homogeneousHeadReal x) ≤
          standardRadius (normalizedMahlerSeminorm X) *
            ‖homogeneousHeadReal x‖ := hhead
      _ ≤ (X.1 : ℝ) * ‖x‖ :=
        mul_le_mul hstd hheadNorm (norm_nonneg _) hrank.le
      _ ≤ (X.1 : ℝ) * (((X.1 : ℝ) + 1)⁻¹) :=
        mul_le_mul_of_nonneg_left hx hrank.le
      _ ≤ 1 := by
        rw [← div_eq_mul_inv]
        exact (div_le_one (by positivity : (0 : ℝ) < X.1 + 1)).2 (by linarith)
  have hlastOne : ‖homogeneousLastReal x‖ ≤ 1 :=
    hlastNorm.trans <| hx.trans <| by
      exact (inv_le_one₀ (by positivity : (0 : ℝ) < X.1 + 1)).mpr (by linarith)
  exact max_le hheadOne hlastOne

/-- The standard coordinate splitting of the homogeneous raw coordinate
space into its old block and its final coordinate. -/
def homogeneousTopSplitMeasurableEquiv (n : ℕ) :
    (Fin (n + 1) → ℝ) ≃ᵐ (Fin n → ℝ) × (Fin 1 → ℝ) :=
  (MeasurableEquiv.piCongrLeft
      (fun _ : Fin n ⊕ Fin 1 ↦ ℝ) finSumFinEquiv.symm).trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ ↦ ℝ))

@[simp] theorem homogeneousTopSplitMeasurableEquiv_fst
    (n : ℕ) (x : Fin (n + 1) → ℝ) (i : Fin n) :
    (homogeneousTopSplitMeasurableEquiv n x).1 i =
      x (Fin.castAdd 1 i) := by
  change (MeasurableEquiv.piCongrLeft
      (fun _ : Fin n ⊕ Fin 1 ↦ ℝ) finSumFinEquiv.symm x) (Sum.inl i) = _
  nth_rewrite 1 [← finSumFinEquiv.symm.apply_symm_apply (Sum.inl i)]
  rw [MeasurableEquiv.piCongrLeft_apply_apply]
  rfl

@[simp] theorem homogeneousTopSplitMeasurableEquiv_snd
    (n : ℕ) (x : Fin (n + 1) → ℝ) (i : Fin 1) :
    (homogeneousTopSplitMeasurableEquiv n x).2 i =
      x (Fin.natAdd n i) := by
  change (MeasurableEquiv.piCongrLeft
      (fun _ : Fin n ⊕ Fin 1 ↦ ℝ) finSumFinEquiv.symm x) (Sum.inr i) = _
  nth_rewrite 1 [← finSumFinEquiv.symm.apply_symm_apply (Sum.inr i)]
  rw [MeasurableEquiv.piCongrLeft_apply_apply]
  rfl

theorem homogeneousTopSplitMeasurableEquiv_measurePreserving (n : ℕ) :
    MeasurePreserving (homogeneousTopSplitMeasurableEquiv n) volume volume := by
  exact
    (volume_measurePreserving_piCongrLeft
      (fun _ : Fin n ⊕ Fin 1 ↦ ℝ) finSumFinEquiv.symm).trans
      (volume_measurePreserving_sumPiEquivProdPi (fun _ ↦ ℝ))

theorem normalizedTopProduct_unitBall_eq_preimage
    (X : RankedBodyPresentation A) :
    {x | normalizedTopProductSeminorm X x ≤ 1} =
      homogeneousTopSplitMeasurableEquiv X.1 ⁻¹'
        ({u | normalizedMahlerSeminorm X u ≤ 1} ×ˢ
          {v : Fin 1 → ℝ | ‖v‖ ≤ 1}) := by
  ext x
  change normalizedHomogeneousProductSeminorm X
      ((EuclideanSpace.equiv (Fin (X.1 + 1)) ℝ).symm x) ≤ 1 ↔ _
  rw [homogeneousProductSeminorm_apply, max_le_iff]
  change normalizedMahlerSeminorm X
      (homogeneousHeadReal
        ((EuclideanSpace.equiv (Fin (X.1 + 1)) ℝ).symm x)) ≤ 1 ∧
    ‖homogeneousLastReal
      ((EuclideanSpace.equiv (Fin (X.1 + 1)) ℝ).symm x)‖ ≤ 1 ↔ _
  simp only [Set.mem_preimage, Set.mem_prod, Set.mem_setOf_eq]
  have hhead : (homogeneousTopSplitMeasurableEquiv X.1 x).1 =
      homogeneousHeadReal
        ((EuclideanSpace.equiv (Fin (X.1 + 1)) ℝ).symm x) := by
    ext i
    rw [homogeneousTopSplitMeasurableEquiv_fst]
    rfl
  have hsnd : (homogeneousTopSplitMeasurableEquiv X.1 x).2 =
      fun _ : Fin 1 ↦ homogeneousLastReal
        ((EuclideanSpace.equiv (Fin (X.1 + 1)) ℝ).symm x) := by
    ext i
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    rw [homogeneousTopSplitMeasurableEquiv_snd]
    rfl
  have hsndnorm : ‖(homogeneousTopSplitMeasurableEquiv X.1 x).2‖ =
      ‖homogeneousLastReal
        ((EuclideanSpace.equiv (Fin (X.1 + 1)) ℝ).symm x)‖ := by
    rw [hsnd]
    simp
  constructor
  · rintro ⟨hh, hl⟩
    rw [hhead, hsndnorm]
    exact ⟨hh, hl⟩
  · rintro ⟨hh, hl⟩
    rw [← hhead, ← hsndnorm]
    exact ⟨hh, hl⟩

theorem volume_singletonCoordinate_unitBall :
    volume {v : Fin 1 → ℝ | ‖v‖ ≤ 1} = 2 := by
  have hset : {v : Fin 1 → ℝ | ‖v‖ ≤ 1} =
      Set.Icc (fun _ ↦ (-1 : ℝ)) (fun _ ↦ (1 : ℝ)) := by
    ext v
    simp only [Set.mem_setOf_eq, Set.mem_Icc]
    rw [pi_norm_le_iff_of_nonneg (by norm_num), Pi.le_def, Pi.le_def]
    simp only [Real.norm_eq_abs, abs_le, forall_and]
  rw [hset, Real.volume_Icc_pi]
  norm_num [ENNReal.ofReal_ofNat]

/-- Exact product formula in the codimension-zero affine branch. -/
theorem volume_normalizedTopProduct_unitBall
    (X : RankedBodyPresentation A) :
    volume {x | normalizedTopProductSeminorm X x ≤ 1} =
      2 * volume {u | normalizedMahlerSeminorm X u ≤ 1} := by
  rw [normalizedTopProduct_unitBall_eq_preimage X,
    (homogeneousTopSplitMeasurableEquiv_measurePreserving X.1).measure_preimage_emb
      (homogeneousTopSplitMeasurableEquiv X.1).measurableEmbedding]
  change (volume.prod volume)
      ({u | normalizedMahlerSeminorm X u ≤ 1} ×ˢ
        {v : Fin 1 → ℝ | ‖v‖ ≤ 1}) = _
  rw [Measure.prod_prod, volume_singletonCoordinate_unitBall]
  ac_rfl

/-- Real-volume form of the normalized codimension-zero product formula. -/
theorem bodyVolume_rankedNormalizedTopAffineBodyPresentation
    (X : RankedBodyPresentation A) :
    bodyVolume (rankedNormalizedTopAffineBodyPresentation X) =
      2 * ((X.1 : ℝ) ^ X.1 * bodyVolume X) := by
  change (volume {x | normalizedTopProductSeminorm X x ≤ 1}).toReal = _
  rw [volume_normalizedTopProduct_unitBall X,
    show {u | normalizedMahlerSeminorm X u ≤ 1} =
      unitBall (normalizedMahlerSeminorm X) by rfl,
    volume_normalizedMahlerUnitBall, ENNReal.toReal_mul,
    ENNReal.toReal_ofNat, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg (by positivity) _)]
  rfl

/-- Exact covolume formula for the proper normalized affine branch. -/
theorem volume_normalizedProperAffine_unitBall
    (X : RankedBodyPresentation A)
    (hproper : normalizedHomogeneousSubspace X ≠ ⊤) :
    volume {x | normalizedAffineSectionSeminorm X hproper x ≤ 1} =
      volume {x : normalizedHomogeneousSubspace X |
        subspaceSeminorm (normalizedHomogeneousSubspace X)
          (normalizedHomogeneousProductSeminorm X) x ≤ 1} /
        ENNReal.ofReal
          (ZLattice.covolume
            (integralPoints (normalizedHomogeneousSubspace X))) := by
  exact volume_unitBall_coordinateSeminorm
    (normalizedHomogeneousSubspace X) hproper
    (span_integralPoints_homogeneousSubspace (normalizedLiftSet X))
    (normalizedHomogeneousProductSeminorm X)

theorem one_le_normalizedAffine_covolume
    (X : RankedBodyPresentation A)
    (hproper : normalizedHomogeneousSubspace X ≠ ⊤) :
    (1 : ℝ) ≤ ZLattice.covolume
      (integralPoints (normalizedHomogeneousSubspace X)) := by
  exact Section93LatticeSectionVolume.one_le_covolume_integralPoints
    (normalizedHomogeneousSubspace X) hproper
    (span_integralPoints_homogeneousSubspace (normalizedLiftSet X))

/-- Haar volume on a subspace equals the ambient intrinsic Hausdorff
volume of the corresponding central section. -/
theorem volume_subspaceSeminorm_unitBall_eq_intrinsicVolume
    {n d : ℕ}
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (hL : finrank ℝ L = d)
    (p : Seminorm ℝ (EuclideanSpace ℝ (Fin n))) :
    volume {x : L | subspaceSeminorm L p x ≤ 1} =
      intrinsicVolume d ({x | p x ≤ 1} ∩
        (L : Set (EuclideanSpace ℝ (Fin n)))) := by
  let S : Set L := {x : L | subspaceSeminorm L p x ≤ 1}
  have himage : ((fun x : L ↦ (x : EuclideanSpace ℝ (Fin n))) '' S) =
      {x | p x ≤ 1} ∩ (L : Set (EuclideanSpace ℝ (Fin n))) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨hy, y.property⟩
    · rintro ⟨hx, hxL⟩
      exact ⟨⟨x, hxL⟩, hx, rfl⟩
  have hm := isometry_subtype_coe.euclideanHausdorffMeasure_image
    (d := d) S
  change μHE[d] ((fun x : L ↦
      (x : EuclideanSpace ℝ (Fin n))) '' S) = μHE[d] S at hm
  rw [himage] at hm
  have hsub : (μHE[d] : Measure L) = volume := by
    simpa [hL] using
      (InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := L))
  symm
  calc
    intrinsicVolume d
        ({x | p x ≤ 1} ∩ (L : Set (EuclideanSpace ℝ (Fin n)))) =
        intrinsicVolume d S := hm
    _ = volume S := by
      unfold intrinsicVolume
      rw [hsub]

/-- Exact factorial central-section estimate for the proper normalized
affine restriction, after discarding the intersection-lattice denominator
using its lower bound one. -/
theorem volume_normalizedProperAffine_unitBall_le
    (X : RankedBodyPresentation A)
    (hproper : normalizedHomogeneousSubspace X ≠ ⊤) :
    let d := finrank ℝ (normalizedHomogeneousSubspace X)
    let k := finrank ℝ (normalizedHomogeneousSubspace X)ᗮ
    volume {x | normalizedAffineSectionSeminorm X hproper x ≤ 1} ≤
      (((d.factorial : ENNReal) *
          ENNReal.ofReal ((((X.1 : ℝ) + 1)⁻¹) ^ k))⁻¹ *
        ((d + k).factorial : ENNReal)) *
          volume (normalizedHomogeneousUnitBall X) := by
  dsimp
  let L := normalizedHomogeneousSubspace X
  let p := normalizedHomogeneousProductSeminorm X
  let d := finrank ℝ L
  let k := finrank ℝ (Lᗮ)
  let rho : ℝ := ((X.1 : ℝ) + 1)⁻¹
  let sectionVolume : ENNReal :=
    volume {x : L | subspaceSeminorm L p x ≤ 1}
  let covol : ENNReal := ENNReal.ofReal
    (ZLattice.covolume (integralPoints L))
  have hrho : 0 < rho := by
    dsimp only [rho]
    positivity
  have hcentral := intrinsicVolume_centralSubspace_section_le
    L (show finrank ℝ L = d by rfl)
      (show finrank ℝ (Lᗮ) = k by rfl)
    hrho (measurableSet_normalizedHomogeneousUnitBall X)
    (convex_normalizedHomogeneousUnitBall X)
    (closedBall_subset_normalizedHomogeneousUnitBall X)
  have hsectionEq : sectionVolume = intrinsicVolume d
      (normalizedHomogeneousUnitBall X ∩
        (L : Set (EuclideanSpace ℝ (Fin (X.1 + 1)))) ) := by
    exact volume_subspaceSeminorm_unitBall_eq_intrinsicVolume L rfl p
  have hsum : d + k = X.1 + 1 := by
    dsimp only [d, k, L]
    simpa only [finrank_euclideanSpace_fin] using
      (Submodule.finrank_add_finrank_orthogonal
        (normalizedHomogeneousSubspace X))
  have hambient : intrinsicVolume (d + k)
      (normalizedHomogeneousUnitBall X) =
      volume (normalizedHomogeneousUnitBall X) := by
    rw [hsum]
    unfold intrinsicVolume
    have hm : (μHE[X.1 + 1] :
        Measure (EuclideanSpace ℝ (Fin (X.1 + 1)))) = volume := by
      simpa using
        (InnerProductSpace.euclideanHausdorffMeasure_eq_volume
          (V := EuclideanSpace ℝ (Fin (X.1 + 1))))
    rw [hm]
  have hsection : sectionVolume ≤
      (((d.factorial : ENNReal) * ENNReal.ofReal (rho ^ k))⁻¹ *
        ((d + k).factorial : ENNReal)) *
          volume (normalizedHomogeneousUnitBall X) := by
    rw [hsectionEq]
    exact hcentral.trans_eq (by rw [hambient])
  have hcovolReal : (1 : ℝ) ≤
      ZLattice.covolume (integralPoints L) := by
    exact one_le_normalizedAffine_covolume X hproper
  have hcovol : (1 : ENNReal) ≤ covol := by
    dsimp only [covol]
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hcovolReal
  have hcovolPos : covol ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hcovol)
  have hcovolTop : covol ≠ ⊤ := by
    dsimp only [covol]
    exact ENNReal.ofReal_ne_top
  have hdiv : sectionVolume / covol ≤ sectionVolume := by
    rw [ENNReal.div_le_iff hcovolPos hcovolTop]
    simpa only [mul_one] using
      (mul_le_mul_of_nonneg_left hcovol bot_le)
  rw [volume_normalizedProperAffine_unitBall X hproper]
  exact hdiv.trans hsection

end

end Erdos186.CFP.Bilu.Section93NormalizedAffineVolume

#print axioms
  Erdos186.CFP.Bilu.Section93NormalizedAffineVolume.bodyVolume_rankedNormalizedTopAffineBodyPresentation
#print axioms
  Erdos186.CFP.Bilu.Section93NormalizedAffineVolume.volume_normalizedProperAffine_unitBall
