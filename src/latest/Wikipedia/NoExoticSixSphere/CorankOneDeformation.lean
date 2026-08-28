import Wikipedia.NoExoticSixSphere.CorankOneShears
import Wikipedia.NoExoticSixSphere.CorankOneResidual

/-!
# Deforming the actual block operator to its Schur-residual model

Scale both genuine shears in the exact factorization to zero. The leading
block and residual diagonal are retained, so every stage is injective when
the residual is nonzero. The deformation is smooth on the leading-block chart.
-/

noncomputable section

open Function
open scoped ContDiff

namespace NoExoticSixSphere.CorankOne

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem sourceShear_eq (u : E) :
    sourceShear u = ContinuousLinearMap.id ℝ (E × ℝ) +
      (ContinuousLinearMap.inl ℝ E ℝ).comp ((ContinuousLinearMap.snd ℝ E ℝ).smulRight u) := by
  apply ContinuousLinearMap.ext
  intro q
  apply Prod.ext
  · rfl
  · exact (add_zero q.2).symm

theorem targetShear_eq (C : E →L[ℝ] F) :
    targetShear C = ContinuousLinearMap.id ℝ (E × F) +
      (ContinuousLinearMap.inr ℝ E F).comp (C.comp (ContinuousLinearMap.fst ℝ E F)) := by
  apply ContinuousLinearMap.ext
  intro q
  apply Prod.ext
  · exact (add_zero q.1).symm
  · rfl

theorem diagonal_eq (A : E →L[ℝ] E) (z : F) :
    diagonal A z = (ContinuousLinearMap.inl ℝ E F).comp
      (A.comp (ContinuousLinearMap.fst ℝ E ℝ)) +
      (ContinuousLinearMap.inr ℝ E F).comp ((ContinuousLinearMap.snd ℝ E ℝ).smulRight z) := by
  apply ContinuousLinearMap.ext
  intro q
  apply Prod.ext
  · exact (add_zero (A q.1)).symm
  · exact (zero_add (q.2 • z)).symm

theorem contDiff_sourceShear : ContDiff ℝ ∞ (sourceShear (E := E)) := by
  have he : sourceShear (E := E) = fun u ↦ ContinuousLinearMap.id ℝ (E × ℝ) +
      (ContinuousLinearMap.inl ℝ E ℝ).comp ((ContinuousLinearMap.snd ℝ E ℝ).smulRight u) :=
    funext sourceShear_eq
  rw [he]
  exact contDiff_const.add
    (contDiff_const.clm_comp (contDiff_const.smulRight contDiff_id))

theorem contDiff_targetShear : ContDiff ℝ ∞ (targetShear (E := E) (F := F)) := by
  have he : targetShear (E := E) (F := F) = fun C ↦ ContinuousLinearMap.id ℝ (E × F) +
      (ContinuousLinearMap.inr ℝ E F).comp (C.comp (ContinuousLinearMap.fst ℝ E F)) :=
    funext targetShear_eq
  rw [he]
  exact contDiff_const.add
    (contDiff_const.clm_comp (contDiff_id.clm_comp contDiff_const))

theorem contDiff_diagonal :
    ContDiff ℝ ∞ (fun p : (E →L[ℝ] E) × F ↦ diagonal p.1 p.2) := by
  simp_rw [diagonal_eq]
  exact (contDiff_const.clm_comp (contDiff_fst.clm_comp contDiff_const)).add
    (contDiff_const.clm_comp (contDiff_const.smulRight contDiff_snd))

def deformation (s : ℝ) (L : BlockMap E F) : BlockMap E F :=
  (targetShear ((1 - s) • ((bottom L).comp (leading L).inverse))).comp
    ((diagonal (leading L) (residual L)).comp
      (sourceShear ((1 - s) • (leading L).inverse (column L).1)))

theorem deformation_zero (L : BlockMap E F) (hL : (leading L).IsInvertible) :
    deformation 0 L = L := by
  simp only [deformation, sub_zero, one_smul]
  exact (shear_factorization L hL).symm

theorem deformation_one (L : BlockMap E F) :
    deformation 1 L = diagonal (leading L) (residual L) := by
  apply ContinuousLinearMap.ext
  intro q
  simp [deformation, sourceShear_apply, targetShear_apply, diagonal_apply]

theorem injective_deformation (s : ℝ) (L : BlockMap E F)
    (hL : (leading L).IsInvertible) (hr : residual L ≠ 0) : Injective (deformation s L) :=
  (injective_targetShear _).comp
    ((injective_diagonal (leading L) hL.injective (residual L) hr).comp
      (injective_sourceShear _))

variable [CompleteSpace E]

theorem contDiffAt_deformation (s : ℝ) (L : BlockMap E F)
    (hL : (leading L).IsInvertible) :
    ContDiffAt ℝ ∞ (fun p : ℝ × BlockMap E F ↦ deformation p.1 p.2) (s, L) := by
  have hA := (contDiff_leading (E := E) (F := F)).contDiffAt.comp (s, L) contDiffAt_snd
  have hC := (contDiff_bottom (E := E) (F := F)).contDiffAt.comp (s, L) contDiffAt_snd
  have hB := (contDiff_column (E := E) (F := F)).contDiffAt.comp (s, L) contDiffAt_snd
  have hR := (contDiffAt_residual L hL).comp (s, L) contDiffAt_snd
  have hI := hL.contDiffAt_map_inverse.comp (s, L) hA
  have ht : ContDiffAt ℝ ∞ (fun p : ℝ × BlockMap E F ↦ 1 - p.1) (s, L) :=
    contDiffAt_const.sub contDiffAt_fst
  have hleft := (contDiff_targetShear (E := E) (F := F)).contDiffAt.comp
    (s, L) (ht.smul (hC.clm_comp hI))
  have hmiddle := (contDiff_diagonal (E := E) (F := F)).contDiffAt.comp
    (s, L) (hA.prodMk hR)
  have hright := (contDiff_sourceShear (E := E)).contDiffAt.comp
    (s, L) (ht.smul (hI.clm_apply hB.fst))
  exact hleft.clm_comp (hmiddle.clm_comp hright)

end NoExoticSixSphere.CorankOne
