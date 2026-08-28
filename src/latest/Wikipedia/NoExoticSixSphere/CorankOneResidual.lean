import Wikipedia.NoExoticSixSphere.CorankOneBlocks

/-!
# The actual corank-one residual is a smooth submersion

Changing only the last source column's lower target component translates
the residual by exactly that component. Differentiating this identity gives
a right inverse of the residual differential on every invertible-block chart.
-/

noncomputable section

open Function
open scoped ContDiff

namespace NoExoticSixSphere.CorankOne

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem contDiff_leading : ContDiff ℝ ∞ (leading (E := E) (F := F)) :=
  contDiff_const.clm_comp (contDiff_id.clm_comp contDiff_const)

theorem contDiff_bottom : ContDiff ℝ ∞ (bottom (E := E) (F := F)) :=
  contDiff_const.clm_comp (contDiff_id.clm_comp contDiff_const)

theorem contDiff_column : ContDiff ℝ ∞ (column (E := E) (F := F)) :=
  contDiff_id.clm_apply contDiff_const

def tailPerturbation : F →L[ℝ] BlockMap E F :=
  ((ContinuousLinearMap.smulRightL ℝ (E × ℝ) (E × F))
    (ContinuousLinearMap.snd ℝ E ℝ)).comp (ContinuousLinearMap.inr ℝ E F)

theorem tailPerturbation_apply (y : F) (x : E) (t : ℝ) :
    tailPerturbation y (x, t) = (0, t • y) := by
  change t • ((0 : E), y) = ((0 : E), t • y)
  simp

theorem leading_add_tail (L : BlockMap E F) (y : F) :
    leading (L + tailPerturbation y) = leading L := by
  apply ContinuousLinearMap.ext
  intro x
  change (L (x, 0) + tailPerturbation y (x, 0)).1 = (L (x, 0)).1
  rw [tailPerturbation_apply]
  simp

theorem bottom_add_tail (L : BlockMap E F) (y : F) :
    bottom (L + tailPerturbation y) = bottom L := by
  apply ContinuousLinearMap.ext
  intro x
  change (L (x, 0) + tailPerturbation y (x, 0)).2 = (L (x, 0)).2
  rw [tailPerturbation_apply]
  simp

theorem column_add_tail (L : BlockMap E F) (y : F) :
    column (L + tailPerturbation y) = column L + (0, y) := by
  change L (0, 1) + tailPerturbation y (0, 1) = _
  rw [tailPerturbation_apply, one_smul]
  rfl

theorem residual_add_tail (L : BlockMap E F) (y : F) :
    residual (L + tailPerturbation y) = residual L + y := by
  rw [residual, leading_add_tail, bottom_add_tail, column_add_tail]
  change (column L).2 + y - bottom L ((leading L).inverse ((column L).1 + 0)) = _
  rw [add_zero]
  dsimp [residual]
  abel

variable [CompleteSpace E]

theorem contDiffAt_residual (L : BlockMap E F) (hL : (leading L).IsInvertible) :
    ContDiffAt ℝ ∞ residual L := by
  have hi : ContDiffAt ℝ ∞ (fun A : BlockMap E F ↦ (leading A).inverse) L :=
    hL.contDiffAt_map_inverse.comp L (contDiff_leading (E := E) (F := F)).contDiffAt
  have hc := (contDiff_column (E := E) (F := F)).contDiffAt (x := L)
  have hb := (contDiff_bottom (E := E) (F := F)).contDiffAt (x := L)
  exact hc.snd.sub (hb.clm_apply (hi.clm_apply hc.fst))

theorem fderiv_residual_comp_tail (L : BlockMap E F) (hL : (leading L).IsInvertible) :
    (fderiv ℝ (residual (E := E) (F := F)) L).comp
      (tailPerturbation (E := E) (F := F)) = ContinuousLinearMap.id ℝ F := by
  let R : BlockMap E F → F := residual
  let T : F →L[ℝ] BlockMap E F := tailPerturbation
  have hr : DifferentiableAt ℝ R L :=
    (contDiffAt_residual L hL).differentiableAt (by simp)
  have ha : HasFDerivAt (fun y : F ↦ L + T y) T 0 := T.hasFDerivAt.const_add L
  have hr' : HasFDerivAt R (fderiv ℝ R L) (L + T (0 : F)) := by
    simpa only [map_zero, add_zero] using hr.hasFDerivAt
  have h : HasFDerivAt (R ∘ fun y : F ↦ L + T y) ((fderiv ℝ R L).comp T) 0 :=
    hr'.comp 0 ha
  have he : (R ∘ fun y : F ↦ L + T y) = fun y ↦ R L + y :=
    funext (residual_add_tail L)
  rw [he] at h
  exact h.unique ((hasFDerivAt_id (0 : F)).const_add (R L))

theorem surjective_fderiv_residual (L : BlockMap E F) (hL : (leading L).IsInvertible) :
    Surjective (fderiv ℝ residual L) := by
  intro y
  exact ⟨tailPerturbation y,
    congrArg (fun A : F →L[ℝ] F ↦ A y) (fderiv_residual_comp_tail L hL)⟩

end NoExoticSixSphere.CorankOne
