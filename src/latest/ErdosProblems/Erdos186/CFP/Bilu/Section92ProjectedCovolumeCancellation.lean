/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.Section92NormalizedProjectedGauge
import ErdosProblems.Erdos186.CFP.Bilu.MinkowskiSecondUpper

/-!
# Covolume cancellation for a primitive kernel quotient

The primitive generator together with the chosen integral complement is a
unimodular basis of the old standard lattice.  Orthogonally projecting the
complement onto the perpendicular hyperplane therefore gives a lattice of
covolume exactly the reciprocal of the primitive generator's Euclidean norm.
This removes the last lattice-dependent scalar from the Section 9.2 projected
volume estimate.
-/

namespace Erdos186.CFP.Bilu.Section92ShortKernel.PrimitiveKernelStep

open scoped RealInnerProductSpace
open Module Submodule Set MeasureTheory
open Mahler MinkowskiUpper SubspaceLattice MinkowskiSecond

noncomputable section

variable {n : ℕ} {p : Seminorm ℝ (Fin n → ℝ)}
  {phi : IntegralPoint n →+ ℤ} {T : ℝ}

variable (S : PrimitiveKernelStep p phi T)

private def fullIndexEquiv :
    (Fin 1 ⊕ Fin S.quotient.complementRank) ≃ Fin n :=
  finSumFinEquiv.trans (finCongr (by
    have h := S.quotient.rank_eq
    omega))

/-- The primitive/complement integral basis, reindexed by the old ambient
coordinate type. -/
def fullIntegralBasisFin : Basis (Fin n) ℤ (IntegralPoint n) :=
  S.fullIntegralBasis.reindex S.fullIndexEquiv

/-- Put the primitive vector first and the orthogonally projected complement
vectors after it. -/
private def projectedFullReal
    (i : Fin 1 ⊕ Fin S.quotient.complementRank) :
    EuclideanSpace ℝ (Fin n) :=
  Sum.elim (fun _ ↦ S.primitiveReal)
    (fun j ↦ (S.projectedComplementFamily j :
      EuclideanSpace ℝ (Fin n))) i

private def projectedFullRealFin (i : Fin n) :
    EuclideanSpace ℝ (Fin n) :=
  S.projectedFullReal (S.fullIndexEquiv.symm i)

private def projectedFullMatrix : Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦ S.projectedFullRealFin j i

private theorem fullIntegralBasisFin_apply (i : Fin n) :
    S.fullIntegralBasisFin i =
      S.fullIntegralBasis (S.fullIndexEquiv.symm i) := by
  simp [fullIntegralBasisFin]

private theorem fullRealFamilyFin_apply (i : Fin n) :
    (EuclideanSpace.equiv (Fin n) ℝ).symm
        (integralEmbed (S.fullIntegralBasisFin i)) =
      S.fullRealFamily (S.fullIndexEquiv.symm i) := by
  rw [S.fullIntegralBasisFin_apply]
  rfl

private theorem exists_projectedFullReal_eq_add_smul
    (i : Fin 1 ⊕ Fin S.quotient.complementRank) :
    ∃ c : ℝ, S.projectedFullReal i =
      S.fullRealFamily i + c • S.primitiveReal := by
  rcases i with i | i
  · fin_cases i
    refine ⟨0, ?_⟩
    simp [projectedFullReal]
  · have hmem :
        (Submodule.span ℝ ({S.primitiveReal} : Set _)).starProjection
            (S.complementReal i) ∈
          Submodule.span ℝ ({S.primitiveReal} : Set _) :=
      Submodule.starProjection_apply_mem _ _
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem
    refine ⟨-a, ?_⟩
    simp only [projectedFullReal, fullRealFamily_inr]
    change
      (S.projectedSpace.orthogonalProjectionOnto (S.complementReal i) :
        EuclideanSpace ℝ (Fin n)) =
        S.complementReal i + (-a) • S.primitiveReal
    rw [Submodule.coe_orthogonalProjectionOnto_apply]
    change
      (Submodule.orthogonal (ℝ ∙ S.primitiveReal)).starProjection
          (S.complementReal i) =
        S.complementReal i + (-a) • S.primitiveReal
    rw [Submodule.starProjection_orthogonal_val]
    rw [← ha]
    module

private theorem projectedFullMatrix_det_abs :
    |S.projectedFullMatrix.det| = 1 := by
  classical
  let e := S.fullIndexEquiv
  let k : Fin n := e (Sum.inl 0)
  choose c hc using S.exists_projectedFullReal_eq_add_smul
  let cFin : Fin n → ℝ := fun i ↦ c (e.symm i)
  have hk : cFin k = 0 := by
    have h := hc (Sum.inl 0)
    have h' : S.primitiveReal =
        S.primitiveReal + c (Sum.inl 0) • S.primitiveReal := by
      simpa [projectedFullReal] using h
    have hv :=
      Section92ProjectedGauge.PrimitiveKernelStep.primitiveReal_ne_zero S
    have hc0 : c (Sum.inl 0) = 0 := by
      have hsmul : c (Sum.inl 0) • S.primitiveReal = 0 := by
        apply add_left_cancel (a := S.primitiveReal)
        simpa using h'.symm
      exact (smul_eq_zero.mp hsmul).resolve_right hv
    simpa [cFin, k, e] using hc0
  have hentry (i j : Fin n) :
      S.projectedFullMatrix j i =
        integralBasisMatrix S.fullIntegralBasisFin j i +
          cFin i * integralBasisMatrix S.fullIntegralBasisFin j k := by
    have h := hc (e.symm i)
    have he : e.symm k = Sum.inl 0 := by
      simp [k]
    change S.projectedFullRealFin i j = _
    rw [projectedFullRealFin, h]
    change
      (S.fullRealFamily (e.symm i)) j +
          cFin i * S.primitiveReal j = _
    rw [← S.fullRealFamilyFin_apply i]
    have hkreal :
        (EuclideanSpace.equiv (Fin n) ℝ).symm
            (integralEmbed (S.fullIntegralBasisFin k)) =
          S.primitiveReal := by
      rw [S.fullRealFamilyFin_apply, he]
      exact S.fullRealFamily_inl_zero
    rw [← hkreal]
    rfl
  have hdet : S.projectedFullMatrix.det =
      (integralBasisMatrix S.fullIntegralBasisFin).det := by
    rw [← Matrix.det_transpose S.projectedFullMatrix,
      ← Matrix.det_transpose (integralBasisMatrix S.fullIntegralBasisFin)]
    exact Matrix.det_eq_of_forall_row_eq_smul_add_const cFin k hk hentry
  rw [hdet]
  exact abs_det_integralBasisMatrix S.fullIntegralBasisFin

private theorem det_gram_projectedFullRealFin :
    (Matrix.gram ℝ S.projectedFullRealFin).det = 1 := by
  let o := EuclideanSpace.basisFun (Fin n) ℝ
  have hgram := Matrix.gram_eq_conjTranspose_mul o S.projectedFullRealFin
  let M : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.of fun i j ↦ o.repr (S.projectedFullRealFin j) i
  have hM : M = S.projectedFullMatrix := by
    ext i j
    rfl
  rw [show Matrix.gram ℝ S.projectedFullRealFin = M.conjTranspose * M by
    simpa [M] using hgram]
  rw [Matrix.det_mul, Matrix.det_conjTranspose, hM]
  simp only [starRingEnd_apply, star_trivial]
  have h := S.projectedFullMatrix_det_abs
  nlinarith [sq_abs S.projectedFullMatrix.det]

private theorem det_gram_projectedFullReal :
    (Matrix.gram ℝ S.projectedFullReal).det = 1 := by
  have hsub :
      Matrix.gram ℝ S.projectedFullRealFin =
        (Matrix.gram ℝ S.projectedFullReal).submatrix
          S.fullIndexEquiv.symm S.fullIndexEquiv.symm := by
    rfl
  have hdet := congrArg Matrix.det hsub
  rw [Matrix.det_submatrix_equiv_self] at hdet
  rw [← hdet]
  exact S.det_gram_projectedFullRealFin

private theorem det_gram_projectedFullReal_eq :
    (Matrix.gram ℝ S.projectedFullReal).det =
      ‖S.primitiveReal‖ ^ 2 *
        (Matrix.gram ℝ S.projectedComplementFamily).det := by
  let A : Matrix (Fin 1) (Fin 1) ℝ :=
    Matrix.gram ℝ (fun _ : Fin 1 ↦ S.primitiveReal)
  let D : Matrix (Fin S.quotient.complementRank)
      (Fin S.quotient.complementRank) ℝ :=
    Matrix.gram ℝ S.projectedComplementFamily
  have hblock : Matrix.gram ℝ S.projectedFullReal =
      Matrix.fromBlocks A 0 0 D := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · rfl
    · change inner ℝ S.primitiveReal
          (S.projectedComplementFamily j : EuclideanSpace ℝ (Fin n)) = 0
      exact Submodule.inner_right_of_mem_orthogonal
        (Submodule.mem_span_singleton_self S.primitiveReal)
        (S.projectedComplementFamily j).property
    · change inner ℝ
          (S.projectedComplementFamily i : EuclideanSpace ℝ (Fin n))
          S.primitiveReal = 0
      rw [real_inner_comm]
      exact Submodule.inner_right_of_mem_orthogonal
        (Submodule.mem_span_singleton_self S.primitiveReal)
        (S.projectedComplementFamily i).property
    · rfl
  rw [hblock, Matrix.det_fromBlocks_zero₂₁]
  have hA : A.det = ‖S.primitiveReal‖ ^ 2 := by
    simp [A, Matrix.gram_apply, real_inner_self_eq_norm_sq]
  rw [hA]

private theorem gram_orthonormalProjectedComplementBasis :
    Matrix.gram ℝ S.orthonormalProjectedComplementBasis =
      Matrix.gram ℝ S.projectedComplementFamily := by
  ext i j
  simp [Matrix.gram_apply, orthonormalProjectedComplementBasis,
    projectedComplementBasis_apply]

/-- Exact primitive/covolume cancellation for the projected complement
lattice. -/
theorem norm_primitiveReal_mul_projectedComplementLattice_covolume :
    ‖S.primitiveReal‖ *
        ZLattice.covolume S.projectedComplementLattice = 1 := by
  have hcov := SubspaceLattice.covolume_span_basis_sq_eq_det_gram
    S.orthonormalProjectedComplementBasis
  change
    ZLattice.covolume S.projectedComplementLattice ^ 2 =
      (Matrix.gram ℝ S.orthonormalProjectedComplementBasis).det at hcov
  rw [S.gram_orthonormalProjectedComplementBasis] at hcov
  have hdet := S.det_gram_projectedFullReal
  rw [S.det_gram_projectedFullReal_eq] at hdet
  have hsquare :
      (‖S.primitiveReal‖ *
          ZLattice.covolume S.projectedComplementLattice) ^ 2 = 1 := by
    rw [mul_pow, hcov]
    exact hdet
  have hnonneg : 0 ≤ ‖S.primitiveReal‖ *
      ZLattice.covolume S.projectedComplementLattice :=
    mul_nonneg (norm_nonneg _) (ZLattice.covolume_pos _ _).le
  nlinarith

/-- After unimodular covolume cancellation, the coarse projected-volume
estimate has no lattice-dependent scalar. -/
theorem volume_coordinateProjectedBody_le_rank_mul
    (hn : 0 < n) (hp : IsDefinite p) (hT : 0 ≤ T) :
    volume S.coordinateProjectedBody ≤
      (n : ENNReal) * ENNReal.ofReal T * volume (unitBall p) := by
  have hraw := S.coordinateProjectedBody_volume_bound_two_mul hn hp
  have hfac :
      ENNReal.ofReal ‖S.primitiveReal‖ *
          ENNReal.ofReal
            (ZLattice.covolume S.projectedComplementLattice) = 1 := by
    rw [← ENNReal.ofReal_mul (norm_nonneg _),
      S.norm_primitiveReal_mul_projectedComplementLattice_covolume]
    simp
  rw [mul_assoc (2 : ENNReal), hfac, mul_one] at hraw
  have htwo :
      (2 : ENNReal) * volume S.coordinateProjectedBody ≤
        (2 : ENNReal) *
          ((n : ENNReal) * ENNReal.ofReal T * volume (unitBall p)) := by
    calc
      (2 : ENNReal) * volume S.coordinateProjectedBody ≤
          (n : ENNReal) * ENNReal.ofReal (2 * T) *
            volume (unitBall p) := hraw
      _ = (2 : ENNReal) *
          ((n : ENNReal) * ENNReal.ofReal T * volume (unitBall p)) := by
            rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
            norm_num
            ring
  let Y : ENNReal :=
    (n : ENNReal) * ENNReal.ofReal T * volume (unitBall p)
  change volume S.coordinateProjectedBody ≤ Y
  change (2 : ENNReal) * volume S.coordinateProjectedBody ≤ 2 * Y at htwo
  calc
    volume S.coordinateProjectedBody =
        ((2 : ENNReal) * volume S.coordinateProjectedBody) * 2⁻¹ := by
      rw [show ((2 : ENNReal) * volume S.coordinateProjectedBody) * 2⁻¹ =
          (2 * 2⁻¹) * volume S.coordinateProjectedBody by ac_rfl]
      rw [ENNReal.mul_inv_cancel] <;> norm_num
    _ ≤ ((2 : ENNReal) * Y) * 2⁻¹ :=
      mul_le_mul_left htwo 2⁻¹
    _ = Y := by
      rw [show ((2 : ENNReal) * Y) * 2⁻¹ = (2 * 2⁻¹) * Y by ac_rfl]
      rw [ENNReal.mul_inv_cancel] <;> norm_num

/-- Real-valued rank-times-radius form used by the Section 4 candidate
decay. -/
theorem coordinateProjectedBody_volumeReal_le_rank_mul
    (hn : 0 < n) (hp : IsDefinite p) (hT : 0 ≤ T) :
    volume.real S.coordinateProjectedBody ≤
      (n : ℝ) * T * volume.real (unitBall p) := by
  have h := S.volume_coordinateProjectedBody_le_rank_mul hn hp hT
  have hcompact : IsCompact (unitBall p) :=
    Metric.isCompact_iff_isClosed_bounded.mpr
      ⟨isClosed_unitBall p, isBounded_unitBall p hp⟩
  have hvoltop : volume (unitBall p) ≠ (⊤ : ENNReal) :=
    hcompact.measure_lt_top.ne
  have hrighttop :
      (n : ENNReal) * ENNReal.ofReal T * volume (unitBall p) ≠
        (⊤ : ENNReal) :=
    ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top) hvoltop
  have hreal := ENNReal.toReal_mono
    hrighttop h
  simpa [MeasureTheory.measureReal_def, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hT] using hreal

end

end Erdos186.CFP.Bilu.Section92ShortKernel.PrimitiveKernelStep

#print axioms Erdos186.CFP.Bilu.Section92ShortKernel.PrimitiveKernelStep.norm_primitiveReal_mul_projectedComplementLattice_covolume
#print axioms Erdos186.CFP.Bilu.Section92ShortKernel.PrimitiveKernelStep.volume_coordinateProjectedBody_le_rank_mul
#print axioms Erdos186.CFP.Bilu.Section92ShortKernel.PrimitiveKernelStep.coordinateProjectedBody_volumeReal_le_rank_mul
