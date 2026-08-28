import Wikipedia.NoExoticSixSphere.PartialFrameSplitStability
import Wikipedia.NoExoticSixSphere.EuclideanTailSplitting

/-!
# Ordinary coordinate-block stabilization of partial frames

Appending identity columns in actual Euclidean coordinates preserves inner
products. For one added column, the operation is exactly block reconstruction
in the standard last-coordinate splitting, so it preserves sphere parity.
-/

noncomputable section

namespace NoExoticSixSphere.Stiefel.BlockSum

open GLOrthonormalization

def operator {N k : ℕ} (m : ℕ) (a : Vector k →L[ℝ] Vector N) :
    Vector (k + m) →L[ℝ] Vector (N + m) :=
  (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := N) (m := m)).symm.toContinuousLinearMap.comp
    ((a.prodMap (ContinuousLinearMap.id ℝ (Vector m))).comp
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := k) (m := m)).toContinuousLinearMap)

theorem operator_apply {N k : ℕ} (m : ℕ) (a : Vector k →L[ℝ] Vector N)
    (w : Vector (k + m)) :
    operator m a w = EuclideanSpace.finAddEquivProd.symm
      (a (EuclideanSpace.finAddEquivProd w).1, (EuclideanSpace.finAddEquivProd w).2) := rfl

theorem inner_operator {N k : ℕ} (m : ℕ) (a : Space N k) (u v : Vector (k + m)) :
    inner ℝ (operator m a.val u) (operator m a.val v) = inner ℝ u v := by
  rw [operator_apply, operator_apply, inner_finAdd_symm]
  have ha := (toIsometry a).inner_map_map
    (EuclideanSpace.finAddEquivProd u).1 (EuclideanSpace.finAddEquivProd v).1
  change inner ℝ (a.val _) (a.val _) = _ at ha
  rw [ha]
  exact (inner_finAdd_split u v).symm

theorem norm_operator {N k : ℕ} (m : ℕ) (a : Space N k) (w : Vector (k + m)) :
    ‖operator m a.val w‖ = ‖w‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simpa only [real_inner_self_eq_norm_sq] using inner_operator m a w w

def frame {N k : ℕ} (m : ℕ) (a : Space N k) : Space (N + m) (k + m) :=
  ⟨operator m a.val, norm_operator m a⟩

theorem continuous_frame {N k : ℕ} (m : ℕ) : Continuous (frame (N := N) (k := k) m) := by
  have hc : Continuous (fun a : Space N k ↦ operator m a.val) := by
    apply continuous_clm_apply.mpr
    intro w
    change Continuous (fun a : Space N k ↦ EuclideanSpace.finAddEquivProd.symm
      (a.val (EuclideanSpace.finAddEquivProd w).1, (EuclideanSpace.finAddEquivProd w).2))
    exact EuclideanSpace.finAddEquivProd.symm.continuous.comp
      ((continuous_subtype_val.clm_apply continuous_const).prodMk continuous_const)
  exact hc.subtype_mk _

def map {N k : ℕ} (m : ℕ) : C(Space N k, Space (N + m) (k + m)) :=
  ⟨frame m, continuous_frame m⟩

theorem frame_one_eq_split {N k : ℕ} (a : Space N k) :
    frame 1 a = SplitReconstruction.reconstruct
      (EuclideanTailCoordinates.split k) (EuclideanTailCoordinates.split N) a := by
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro w
  change operator 1 a.val w = _
  rw [operator_apply, SplitReconstruction.reconstruct_apply, EuclideanTailCoordinates.split_apply,
    RectangularColumnBlock.block_apply, EuclideanTailCoordinates.split_symm_apply]
  change EuclideanSpace.finAddEquivProd.symm
    (a.val (EuclideanSpace.finAddEquivProd w).1, (EuclideanSpace.finAddEquivProd w).2) =
    EuclideanSpace.finAddEquivProd.symm
      (a.val (EuclideanSpace.finAddEquivProd w).1,
        EuclideanTailCoordinates.scalar
          (EuclideanTailCoordinates.scalar.symm (EuclideanSpace.finAddEquivProd w).2))
  rw [LinearIsometryEquiv.apply_symm_apply]

theorem sphere_parity_one (r : ℕ) (f : C(Sphere 3, Space (3 + (r + 2)) (r + 2))) :
    sphereThirdObstruction (r + 1) ((map 1).comp f) = sphereThirdObstruction r f := by
  have he : (map 1).comp f =
      (SplitReconstruction.map (EuclideanTailCoordinates.split (r + 2))
        (EuclideanTailCoordinates.split (3 + (r + 2)))).comp f := by
    apply ContinuousMap.ext
    intro s
    exact frame_one_eq_split (f s)
  rw [he]
  exact SplitReconstruction.sphere_parity r _ _ f

end NoExoticSixSphere.Stiefel.BlockSum
