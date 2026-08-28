import Wikipedia.NoExoticSixSphere.WhitneyCuspFrameHomotopy
import Wikipedia.NoExoticSixSphere.EuclideanTailSplitting

/-!
# Explicit orthonormal coordinates for the cusp's residual column

The residual vector is a signed permutation of the four parameters, hence
parameterizes the actual unit three-sphere homeomorphically. Head splittings
are genuine Euclidean isometries, not ordinary product-norm identifications.
-/

noncomputable section

namespace NoExoticSixSphere.WhitneyCusp

open GLOrthonormalization Stiefel

def residualCoordinates : Vector 4 ≃ₗᵢ[ℝ] Vector 4 where
  toFun q := WithLp.toLp 2 ![q 3, q 1, q 2, -q 0]
  invFun q := WithLp.toLp 2 ![-q 3, q 1, q 2, q 0]
  left_inv q := by ext i; fin_cases i <;> simp
  right_inv q := by ext i; fin_cases i <;> simp
  map_add' q p := by ext i; fin_cases i <;> simp; ring
  map_smul' a q := by ext i; fin_cases i <;> simp
  norm_map' q := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    norm_num [Fin.sum_univ_succ]
    change q 3 ^ 2 + (q 1 ^ 2 + (q 2 ^ 2 + q 0 ^ 2)) =
      q 0 ^ 2 + (q 1 ^ 2 + (q 2 ^ 2 + q 3 ^ 2))
    ring

theorem residualCoordinates_apply (q : Vector 4) :
    residualCoordinates q = WithLp.toLp 2 ![q 3, q 1, q 2, -q 0] := rfl

theorem residualCoordinates_mem (q : Sphere 3) : residualCoordinates q.val ∈ Sphere 3 := by
  simpa only [Metric.mem_sphere, dist_zero_right, residualCoordinates.norm_map] using q.property

theorem residualCoordinates_symm_mem (q : Sphere 3) :
    residualCoordinates.symm q.val ∈ Sphere 3 := by
  simpa only [Metric.mem_sphere, dist_zero_right, residualCoordinates.symm.norm_map]
    using q.property

def residualSphere : Sphere 3 ≃ₜ Sphere 3 where
  toFun q := ⟨residualCoordinates q.val, residualCoordinates_mem q⟩
  invFun q := ⟨residualCoordinates.symm q.val, residualCoordinates_symm_mem q⟩
  left_inv q := Subtype.ext (residualCoordinates.symm_apply_apply q.val)
  right_inv q := Subtype.ext (residualCoordinates.apply_symm_apply q.val)
  continuous_toFun := (residualCoordinates.continuous.comp continuous_subtype_val).subtype_mk
    residualCoordinates_mem
  continuous_invFun :=
    (residualCoordinates.symm.continuous.comp continuous_subtype_val).subtype_mk
      residualCoordinates_symm_mem

def residualFrameHomeomorph : Sphere 3 ≃ₜ Space 4 1 :=
  residualSphere.trans (OneColumn.homeomorph (n := 4) (spherePole 0)).symm

theorem residualFrameHomeomorph_apply (q : Sphere 3) (w : Vector 1) :
    (residualFrameHomeomorph q).val w =
      w 0 • WithLp.toLp 2 ![q.val 3, q.val 1, q.val 2, -q.val 0] := by
  change inner ℝ (spherePole 0).val w • residualCoordinates q.val = _
  simp [spherePole, EuclideanSpace.inner_single_left, residualCoordinates_apply]

def headSplit (n : ℕ) : Vector (1 + n) ≃ₗᵢ[ℝ] WithLp 2 (ℝ × Vector n) :=
  (EuclideanTailCoordinates.finAdd 1 n).trans
    (LinearIsometryEquiv.withLpProdCongr 2 EuclideanTailCoordinates.scalar.symm
      (LinearIsometryEquiv.refl ℝ (Vector n)))

theorem headSplit_apply (n : ℕ) (w : Vector (1 + n)) :
    headSplit n w = WithLp.toLp 2
      (EuclideanTailCoordinates.scalar.symm (EuclideanSpace.finAddEquivProd w).1,
        (EuclideanSpace.finAddEquivProd w).2) := rfl

theorem headSplit_symm_apply (n : ℕ) (z : WithLp 2 (ℝ × Vector n)) :
    (headSplit n).symm z = EuclideanSpace.finAddEquivProd.symm
      (EuclideanTailCoordinates.scalar z.fst, z.snd) := rfl

end NoExoticSixSphere.WhitneyCusp
