import Wikipedia.NoExoticSixSphere.PartialFrameBlockSum
import Wikipedia.NoExoticSixSphere.EuclideanBlockCoordinates

/-!
# Exact iteration of ordinary block stabilization

Appending one coordinate after a block of `m` coordinates is exactly the
same operator as appending the combined `m+1` block. The five-column parity
comparison therefore follows from the proved one-column comparison, using
the actual original coordinate inclusions throughout.
-/

noncomputable section

namespace NoExoticSixSphere.Stiefel.BlockSum

open GLOrthonormalization

theorem operator_castAdd {N k : ℕ} (m : ℕ) (a : Vector k →L[ℝ] Vector N)
    (w : Vector (k + m)) (i : Fin N) :
    operator m a w (i.castAdd m) = a (EuclideanSpace.finAddEquivProd w).1 i := by
  rw [operator_apply, EuclideanBlocks.symm_castAdd]

theorem operator_natAdd {N k : ℕ} (m : ℕ) (a : Vector k →L[ℝ] Vector N)
    (w : Vector (k + m)) (i : Fin m) :
    operator m a w (i.natAdd N) = w (i.natAdd k) := by
  rw [operator_apply, EuclideanBlocks.symm_natAdd, EuclideanBlocks.snd_apply]

theorem operator_zero {N k : ℕ} (a : Vector k →L[ℝ] Vector N) : operator 0 a = a := by
  apply ContinuousLinearMap.ext
  intro w
  ext i
  change operator 0 a w (i.castAdd 0) = a w i
  rw [operator_castAdd]
  have he : (EuclideanSpace.finAddEquivProd (n := k) (m := 0) w).1 = w := by
    ext j
    rfl
  rw [he]

theorem operator_succ {N k : ℕ} (m : ℕ) (a : Vector k →L[ℝ] Vector N) :
    operator 1 (operator m a) = operator (m + 1) a := by
  apply ContinuousLinearMap.ext
  intro w
  ext i
  refine Fin.addCases (m := N) (n := m + 1) (fun j ↦ ?_) (fun j ↦ ?_) i
  · change operator 1 (operator m a) w ((j.castAdd m).castAdd 1) =
      operator (m + 1) a w (j.castAdd (m + 1))
    rw [operator_castAdd, operator_castAdd, operator_castAdd, EuclideanBlocks.fst_fst]
  · refine Fin.lastCases ?_ (fun j ↦ ?_) j
    · change operator 1 (operator m a) w ((0 : Fin 1).natAdd (N + m)) =
        operator (m + 1) a w ((Fin.last m).natAdd N)
      rw [operator_natAdd, operator_natAdd]
      rfl
    · change operator 1 (operator m a) w ((j.natAdd N).castAdd 1) =
        operator (m + 1) a w (j.castSucc.natAdd N)
      rw [operator_castAdd, operator_natAdd, EuclideanBlocks.fst_apply, operator_natAdd]
      rfl

theorem frame_zero {N k : ℕ} (a : Space N k) : frame 0 a = a :=
  Subtype.ext (operator_zero a.val)

theorem frame_succ {N k : ℕ} (m : ℕ) (a : Space N k) :
    frame 1 (frame m a) = frame (m + 1) a :=
  Subtype.ext (operator_succ m a.val)

theorem map_succ_comp {X : Type*} [TopologicalSpace X] {N k : ℕ} (m : ℕ)
    (f : C(X, Space N k)) : (map (m + 1)).comp f = (map 1).comp ((map m).comp f) := by
  apply ContinuousMap.ext
  intro x
  exact (frame_succ m (f x)).symm

theorem sphere_parity_five (r : ℕ) (f : C(Sphere 3, Space (3 + (r + 2)) (r + 2))) :
    sphereThirdObstruction (r + 5) ((map 5).comp f) = sphereThirdObstruction r f := by
  rw [map_succ_comp 4, sphere_parity_one (r + 4),
    map_succ_comp 3, sphere_parity_one (r + 3),
    map_succ_comp 2, sphere_parity_one (r + 2),
    map_succ_comp 1, sphere_parity_one (r + 1),
    map_succ_comp 0, sphere_parity_one r]
  have he : (map 0).comp f = f := by
    apply ContinuousMap.ext
    intro s
    exact frame_zero (f s)
  rw [he]

end NoExoticSixSphere.Stiefel.BlockSum
