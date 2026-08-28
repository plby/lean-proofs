import Wikipedia.NoExoticSixSphere.GLOrthonormalization
import Mathlib.LinearAlgebra.Determinant

/-!
# A genuine general-linear homotopy to orthogonal operators

The straight interpolation from an invertible operator to its Gram--Schmidt
orthogonalization stays invertible. In the constructed orthonormal coordinates,
its matrix is upper triangular with strictly positive diagonal.
-/

open unitInterval Module

namespace NoExoticSixSphere.GLOrthonormalization

variable (n : ℕ)

/-- Straight interpolation to the orthogonalized operator. -/
noncomputable def interpolation (p : I × InvertibleOperators (Vector n)) :
    Vector n →L[ℝ] Vector n := (1 - (p.1 : ℝ)) • p.2.1 + (p.1 : ℝ) • operator n p.2

/-- The interpolation varies continuously in both time and the original operator. -/
theorem continuous_interpolation : Continuous (interpolation n) := by
  have ht : Continuous (fun p : I × InvertibleOperators (Vector n) ↦ (p.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  exact ((continuous_const.sub ht).smul (continuous_subtype_val.comp continuous_snd)).add
    (ht.smul ((continuous_operator n).comp continuous_snd))

/-- Matrix coordinates in the fixed domain basis and the Gram--Schmidt codomain basis. -/
noncomputable def interpolationMatrix (p : I × InvertibleOperators (Vector n)) :
    Matrix (Fin n) (Fin n) ℝ :=
  LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis (basis n p.2).toBasis
    (interpolation n p).toLinearMap

/-- The matrix entries split into the triangular original operator and the identity. -/
theorem interpolationMatrix_entry (p : I × InvertibleOperators (Vector n)) (i j : Fin n) :
    interpolationMatrix n p i j =
      (1 - (p.1 : ℝ)) * inner ℝ (basis n p.2 i) (columns n p.2 j) +
        (p.1 : ℝ) * (if i = j then 1 else 0) := by
  rw [interpolationMatrix, LinearMap.toMatrix_apply,
    OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply]
  change inner ℝ (basis n p.2 i)
    ((1 - (p.1 : ℝ)) • columns n p.2 j +
      (p.1 : ℝ) • operator n p.2 (EuclideanSpace.basisFun (Fin n) ℝ j)) = _
  rw [inner_add_right, real_inner_smul_right,
    real_inner_smul_right, operator_basis, OrthonormalBasis.inner_eq_ite]

/-- No entries appear below the diagonal during the interpolation. -/
theorem interpolationMatrix_upper (p : I × InvertibleOperators (Vector n)) :
    (interpolationMatrix n p).IsUpperTriangular := by
  intro i j hji
  change j < i at hji
  have hh : inner ℝ (basis n p.2 i) (columns n p.2 j) = 0 :=
    InnerProductSpace.gramSchmidtOrthonormalBasis_inv_triangular _ _ hji
  rw [interpolationMatrix_entry, hh, if_neg (ne_of_gt hji)]
  ring

/-- The diagonal remains strictly positive, including at both endpoints. -/
theorem interpolationMatrix_diagonal_pos (p : I × InvertibleOperators (Vector n)) (i : Fin n) :
    0 < interpolationMatrix n p i i := by
  rw [interpolationMatrix_entry, if_pos rfl, mul_one]
  have hd := inner_basis_columns_pos n p.2 i
  by_cases ht : (p.1 : ℝ) = 1
  · simp only [ht, sub_self, zero_mul, zero_add, zero_lt_one]
  · have hlt : (p.1 : ℝ) < 1 := lt_of_le_of_ne p.1.2.2 ht
    exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr hlt) hd) p.1.2.1

/-- The triangular determinant is nonzero throughout the homotopy. -/
theorem interpolationMatrix_det_pos (p : I × InvertibleOperators (Vector n)) :
    0 < (interpolationMatrix n p).det := by
  rw [Matrix.det_of_isUpperTriangular (interpolationMatrix_upper n p)]
  exact Finset.prod_pos (fun i _ ↦ interpolationMatrix_diagonal_pos n p i)

/-- Every interpolating operator is genuinely invertible. -/
theorem interpolation_isInvertible (p : I × InvertibleOperators (Vector n)) :
    (interpolation n p).IsInvertible := by
  have hdet : IsUnit (interpolationMatrix n p).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt (interpolationMatrix_det_pos n p))
  refine ⟨(LinearEquiv.ofIsUnitDet hdet).toContinuousLinearEquiv, ?_⟩
  apply ContinuousLinearMap.ext
  intro w
  rfl

/-- Orthonormalization as a continuous map into the actual general linear space. -/
noncomputable def map : C(InvertibleOperators (Vector n), InvertibleOperators (Vector n)) where
  toFun a := ⟨operator n a, ⟨(orthogonalEquiv n a).toContinuousLinearEquiv, rfl⟩⟩
  continuous_toFun := (continuous_operator n).subtype_mk _

/-- The interpolation is an actual continuous homotopy through invertible operators. -/
noncomputable def homotopy :
    (ContinuousMap.id (InvertibleOperators (Vector n))).Homotopy (map n) where
  toFun p := ⟨interpolation n p, interpolation_isInvertible n p⟩
  continuous_toFun := (continuous_interpolation n).subtype_mk _
  map_zero_left a := by
    apply Subtype.ext
    simp [interpolation]
  map_one_left a := by
    apply Subtype.ext
    change interpolation n (1, a) = operator n a
    simp [interpolation]

/-- Every terminal operator preserves the Euclidean norm. -/
theorem map_norm (a : InvertibleOperators (Vector n)) (w : Vector n) :
    ‖(map n a).1 w‖ = ‖w‖ := (orthogonalEquiv n a).norm_map w

/-- Orthonormalization fixes an operator that already preserves norms. -/
theorem operator_eq_self_of_norm (a : InvertibleOperators (Vector n))
    (ha : ∀ w, ‖a.1 w‖ = ‖w‖) : operator n a = a.1 := by
  let L : Vector n →ₗᵢ[ℝ] Vector n := { a.1.toLinearMap with norm_map' := ha }
  have hf : Orthonormal ℝ (columns n a) :=
    (EuclideanSpace.basisFun (Fin n) ℝ).orthonormal.comp_linearIsometry L
  have hb (i : Fin n) : basis n a i = columns n a i := by
    change InnerProductSpace.gramSchmidtOrthonormalBasis _ (columns n a) i = _
    rw [InnerProductSpace.gramSchmidtOrthonormalBasis_apply_of_orthogonal _
      hf.2 (hf.ne_zero i), hf.norm_eq_one i]
    simp only [RCLike.ofReal_real_eq_id, id_eq, inv_one, one_smul]
  have heq : (operator n a).toLinearMap = a.1.toLinearMap := by
    apply (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.ext
    intro i
    exact (operator_basis n a i).trans (hb i)
  exact ContinuousLinearMap.ext (fun w ↦ congrArg (fun L : Vector n →ₗ[ℝ] Vector n ↦ L w) heq)

/-- Every stage fixes an already orthogonal operator. -/
theorem homotopy_fixed (a : InvertibleOperators (Vector n))
    (ha : ∀ w, ‖a.1 w‖ = ‖w‖) (t : I) : homotopy n (t, a) = a := by
  apply Subtype.ext
  change (1 - (t : ℝ)) • a.1 + (t : ℝ) • operator n a = a.1
  rw [operator_eq_self_of_norm n a ha, ← add_smul]
  simp only [sub_add_cancel, one_smul]

/-- The genuine orthogonal subgroup, with the topology inherited from operator norm. -/
abbrev OrthogonalOperators :=
  {a : InvertibleOperators (Vector n) // ∀ w, ‖a.1 w‖ = ‖w‖}

/-- The continuous orthogonalization map with its more precise orthogonal codomain. -/
noncomputable def orthogonalMap : C(InvertibleOperators (Vector n), OrthogonalOperators n) where
  toFun a := ⟨map n a, map_norm n a⟩
  continuous_toFun := (map n).continuous.subtype_mk _

/-- The actual inclusion of orthogonal operators into invertible operators. -/
def orthogonalInclusion : C(OrthogonalOperators n, InvertibleOperators (Vector n)) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- The general-linear nullhomotopy problem reduces to the orthogonal subgroup. -/
theorem nullhomotopic_of_orthogonal_nullhomotopic {X : Type*} [TopologicalSpace X]
    (hO : ∀ g : C(X, OrthogonalOperators n), ∃ c, g.Homotopic (ContinuousMap.const _ c))
    (f : C(X, InvertibleOperators (Vector n))) :
    ∃ c, f.Homotopic (ContinuousMap.const _ c) := by
  obtain ⟨c, ⟨H⟩⟩ := hO ((orthogonalMap n).comp f)
  let H₀ : f.Homotopy ((map n).comp f) := (homotopy n).compContinuousMap f
  let H₁ : ((map n).comp f).Homotopy (ContinuousMap.const _ c.1) :=
    (ContinuousMap.Homotopy.refl (orthogonalInclusion n)).comp H
  exact ⟨c.1, ⟨H₀.trans H₁⟩⟩

end NoExoticSixSphere.GLOrthonormalization
