import Wikipedia.NoExoticSixSphere.CorankOneBlocks

/-!
# Actual shear factorization of a corank-one block operator

An operator with invertible leading block is exactly a source shear,
followed by its diagonal leading-block/residual operator, followed by a
target shear. Both shears are invertible for every shear parameter.
-/

noncomputable section

open Function

namespace NoExoticSixSphere.CorankOne

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def sourceShear (u : E) : (E × ℝ) →L[ℝ] E × ℝ :=
  ((ContinuousLinearMap.fst ℝ E ℝ) + (ContinuousLinearMap.snd ℝ E ℝ).smulRight u).prod
    (ContinuousLinearMap.snd ℝ E ℝ)

def targetShear (C : E →L[ℝ] F) : (E × F) →L[ℝ] E × F :=
  (ContinuousLinearMap.fst ℝ E F).prod
    ((ContinuousLinearMap.snd ℝ E F) + C.comp (ContinuousLinearMap.fst ℝ E F))

def diagonal (A : E →L[ℝ] E) (z : F) : BlockMap E F :=
  (A.comp (ContinuousLinearMap.fst ℝ E ℝ)).prod
    ((ContinuousLinearMap.snd ℝ E ℝ).smulRight z)

theorem sourceShear_apply (u : E) (q : E × ℝ) : sourceShear u q = (q.1 + q.2 • u, q.2) := rfl

theorem targetShear_apply (C : E →L[ℝ] F) (q : E × F) :
    targetShear C q = (q.1, q.2 + C q.1) := rfl

theorem diagonal_apply (A : E →L[ℝ] E) (z : F) (q : E × ℝ) :
    diagonal A z q = (A q.1, q.2 • z) := rfl

theorem sourceShear_neg_apply (u : E) (q : E × ℝ) : sourceShear (-u) (sourceShear u q) = q := by
  apply Prod.ext
  · change q.1 + q.2 • u + q.2 • (-u) = q.1
    rw [smul_neg, add_neg_cancel_right]
  · rfl

theorem targetShear_neg_apply (C : E →L[ℝ] F) (q : E × F) :
    targetShear (-C) (targetShear C q) = q := by
  apply Prod.ext
  · rfl
  · change q.2 + C q.1 + -(C q.1) = q.2
    exact add_neg_cancel_right _ _

theorem injective_sourceShear (u : E) : Injective (sourceShear u) :=
  (show LeftInverse (sourceShear (-u)) (sourceShear u) from sourceShear_neg_apply u).injective

theorem injective_targetShear (C : E →L[ℝ] F) : Injective (targetShear C) :=
  (show LeftInverse (targetShear (-C)) (targetShear C) from targetShear_neg_apply C).injective

theorem injective_diagonal (A : E →L[ℝ] E) (hA : Injective A) (z : F) (hz : z ≠ 0) :
    Injective (diagonal A z) := by
  apply (injective_iff_map_eq_zero _).mpr
  rintro ⟨x, t⟩ he
  have hx : A x = 0 := congrArg (fun q : E × F ↦ q.1) he
  have ht : t • z = 0 := congrArg (fun q : E × F ↦ q.2) he
  exact Prod.ext (hA (hx.trans A.map_zero.symm)) ((smul_eq_zero.mp ht).resolve_right hz)

theorem shear_factorization (L : BlockMap E F) (hL : (leading L).IsInvertible) :
    L = (targetShear ((bottom L).comp (leading L).inverse)).comp
      ((diagonal (leading L) (residual L)).comp
        (sourceShear ((leading L).inverse (column L).1))) := by
  apply ContinuousLinearMap.ext
  rintro ⟨x, t⟩
  rw [block_apply]
  apply Prod.ext
  · change leading L x + t • (column L).1 =
      leading L (x + t • (leading L).inverse (column L).1)
    rw [map_add, map_smul, hL.self_apply_inverse]
  · change bottom L x + t • (column L).2 =
      t • residual L + bottom L ((leading L).inverse
        (leading L (x + t • (leading L).inverse (column L).1)))
    rw [hL.inverse_apply_self, map_add, map_smul]
    dsimp only [residual]
    rw [smul_sub]
    abel

end NoExoticSixSphere.CorankOne
