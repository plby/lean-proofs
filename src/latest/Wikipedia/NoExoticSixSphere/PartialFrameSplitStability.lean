import Wikipedia.NoExoticSixSphere.PartialFrameCoordinateChange

/-!
# Stabilization in any actual orthonormal splitting

Block reconstruction in arbitrary source and target isometric coordinates
is a fixed coordinate change of the checked canonical column reconstruction.
It therefore preserves the actual frame-sphere parity. No equality of the
independently chosen complement bases is assumed.
-/

noncomputable section

namespace NoExoticSixSphere.Stiefel.SplitReconstruction

open GLOrthonormalization

local instance vectorDimension (d : ℕ) : Fact (Module.finrank ℝ (Vector (d + 1)) = d + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

variable {n k : ℕ}
  (S : Vector (k + 1) ≃ₗᵢ[ℝ] WithLp 2 (ℝ × Vector k))
  (T : Vector (n + 1) ≃ₗᵢ[ℝ] WithLp 2 (ℝ × Vector n))

def reconstruct (q : Space n k) : Space (n + 1) (k + 1) :=
  ofIsometry (T.symm.toLinearIsometry.comp
    ((RectangularColumnBlock.block (toIsometry q)).comp S.toLinearIsometry))

theorem reconstruct_apply (q : Space n k) (w : Vector (k + 1)) :
    (reconstruct S T q).val w = T.symm (RectangularColumnBlock.block (toIsometry q) (S w)) := rfl

theorem reconstruct_operator (q : Space n k) :
    (reconstruct S T q).val = T.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      ((RectangularColumnBlock.block (toIsometry q)).toContinuousLinearMap.comp
        S.toContinuousLinearEquiv.toContinuousLinearMap) := by
  apply ContinuousLinearMap.ext
  intro w
  rfl

theorem continuous_reconstruct : Continuous (reconstruct S T) := by
  have hb := RectangularColumnBlock.continuous_block (fun q : Space n k ↦ toIsometry q)
    (show Continuous (fun q : Space n k ↦ (toIsometry q).toContinuousLinearMap) from
      continuous_subtype_val)
  have hc : Continuous (fun q : Space n k ↦ (reconstruct S T q).val) := by
    simp_rw [reconstruct_operator]
    exact continuous_const.clm_comp (hb.clm_comp continuous_const)
  exact hc.subtype_mk _

def map : C(Space n k, Space (n + 1) (k + 1)) :=
  ⟨reconstruct S T, continuous_reconstruct S T⟩

theorem reconstruct_eq_coordinates (v : UnitSphere (Vector (k + 1)))
    (c : UnitSphere (Vector (n + 1))) (q : Space n k) :
    reconstruct S T q = FrameCoordinates.change
      ((ColumnCoordinates.split c).trans T.symm)
      (S.trans (ColumnCoordinates.split v).symm) (ColumnFiber.reconstruct v c q) := by
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro w
  rw [reconstruct_apply, FrameCoordinates.change_apply, ColumnFiber.reconstruct_apply]
  simp only [LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.apply_symm_apply]

theorem sphere_parity (r : ℕ)
    (S : Vector ((r + 2) + 1) ≃ₗᵢ[ℝ] WithLp 2 (ℝ × Vector (r + 2)))
    (T : Vector ((3 + (r + 2)) + 1) ≃ₗᵢ[ℝ] WithLp 2 (ℝ × Vector (3 + (r + 2))))
    (f : C(Sphere 3, Space (3 + (r + 2)) (r + 2))) :
    sphereThirdObstruction (r + 1) ((map S T).comp f) = sphereThirdObstruction r f := by
  let v := pole (r + 2)
  let c := pole (3 + (r + 2))
  let U := (ColumnCoordinates.split c).trans T.symm
  let V := S.trans (ColumnCoordinates.split v).symm
  let h := FrameCoordinates.homeomorph U V
  have he : (map S T).comp f =
      (h : C(_, _)).comp ((ColumnFiber.reconstructionMap v c).comp f) := by
    apply ContinuousMap.ext
    intro s
    exact reconstruct_eq_coordinates S T v c (f s)
  rw [he, sphereThirdObstruction_homeomorph, sphereThirdObstruction_reconstruction]

end NoExoticSixSphere.Stiefel.SplitReconstruction
