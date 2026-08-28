import Wikipedia.NoExoticSixSphere.RectangularSmoothNormalization

/-!
# Gram--Schmidt commutes with actual ambient linear isometries

The ordered source columns are unchanged. Both the recursive orthogonal
columns and their normalization commute with an isometric embedding of
the ambient space. No assertion about arbitrary source-column changes is
made: those generally do not commute with ordered Gram--Schmidt.
-/

noncomputable section

open InnerProductSpace

namespace NoExoticSixSphere

variable {E F ι : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [LinearOrder ι] [LocallyFiniteOrderBot ι] [WellFoundedLT ι]

theorem gramSchmidt_linearIsometry (J : E →ₗᵢ[ℝ] F) (v : ι → E) (i : ι) :
    gramSchmidt ℝ (fun j ↦ J (v j)) i = J (gramSchmidt ℝ v i) := by
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    have hL := eq_sub_of_add_eq (gramSchmidt_def'' ℝ (fun j ↦ J (v j)) i).symm
    have hR := eq_sub_of_add_eq (gramSchmidt_def'' ℝ v i).symm
    rw [hL, hR, map_sub, map_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [ih j (Finset.mem_Iio.mp hj), J.inner_map_map, J.norm_map, map_smul]

theorem gramSchmidtNormed_linearIsometry (J : E →ₗᵢ[ℝ] F) (v : ι → E) (i : ι) :
    gramSchmidtNormed ℝ (fun j ↦ J (v j)) i = J (gramSchmidtNormed ℝ v i) := by
  simp only [gramSchmidtNormed, gramSchmidt_linearIsometry, J.norm_map, map_smul]

namespace Stiefel.Orthonormalization

open GLOrthonormalization

def dimensionChange {k k' : ℕ} (h : k' = k) : Vector k' ≃ₗᵢ[ℝ] Vector k :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (finCongr h)

theorem operator_comp_dimensionChange {X : Type*} {N k k' : ℕ} (h : k' = k)
    (A : X → Vector k →L[ℝ] Vector N) (x : X) :
    operator (fun y ↦ (A y).comp (dimensionChange h).toContinuousLinearMap) x =
      (operator A x).comp (dimensionChange h).toContinuousLinearMap := by
  subst k'
  have hi : (dimensionChange (rfl : k = k)).toContinuousLinearMap =
      ContinuousLinearMap.id ℝ (Vector k) := by
    ext v i
    rfl
  simp only [hi, ContinuousLinearMap.comp_id]

theorem operator_comp_linearIsometry {X : Type*} {N N' k : ℕ}
    (J : Vector N →ₗᵢ[ℝ] Vector N') (A : X → Vector k →L[ℝ] Vector N) (x : X) :
    operator (fun y ↦ J.toContinuousLinearMap.comp (A y)) x =
      J.toContinuousLinearMap.comp (operator A x) := by
  have he : (operator (fun y ↦ J.toContinuousLinearMap.comp (A y)) x).toLinearMap =
      (J.toContinuousLinearMap.comp (operator A x)).toLinearMap := by
    apply (EuclideanSpace.basisFun (Fin k) ℝ).toBasis.ext
    intro i
    change linearMap (fun y ↦ J.toContinuousLinearMap.comp (A y)) x
        (EuclideanSpace.basisFun (Fin k) ℝ i) =
      J (linearMap A x (EuclideanSpace.basisFun (Fin k) ℝ i))
    rw [linearMap_basis, linearMap_basis]
    exact gramSchmidtNormed_linearIsometry J (columns A x) i
  exact ContinuousLinearMap.ext (fun v ↦
    congrArg (fun L : Vector k →ₗ[ℝ] Vector N' ↦ L v) he)

end Stiefel.Orthonormalization
end NoExoticSixSphere
