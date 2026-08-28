import Wikipedia.NoExoticSixSphere.PartialFrameBlockIteration
import Wikipedia.NoExoticSixSphere.PartialFrameRangeCoordinates

/-!
# Ranges and extracted coordinates under block stabilization

Block stabilization commutes with frame composition. Its range condition is
exactly the original range condition on the first coordinate block, and
extracting coordinates in a stabilized full frame gives the stabilized
original coordinates.
-/

noncomputable section

namespace NoExoticSixSphere.Stiefel.BlockSum

open GLOrthonormalization

theorem frame_comp {N n k : ℕ} (m : ℕ) (t : Space N n) (a : Space n k) :
    Stiefel.comp (frame m t) (frame m a) = frame m (Stiefel.comp t a) := by
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro w
  change operator m t.val (operator m a.val w) = operator m (t.val.comp a.val) w
  rw [operator_apply, operator_apply, ContinuousLinearEquiv.apply_symm_apply, operator_apply]
  rfl

theorem mem_range_frame {N k : ℕ} (m : ℕ) (a : Space N k) (y : Vector (N + m)) :
    y ∈ (frame m a).val.range ↔ (EuclideanSpace.finAddEquivProd y).1 ∈ a.val.range := by
  constructor
  · rintro ⟨w, rfl⟩
    change (EuclideanSpace.finAddEquivProd (operator m a.val w)).1 ∈ a.val.range
    rw [operator_apply, ContinuousLinearEquiv.apply_symm_apply]
    exact ⟨_, rfl⟩
  · rintro ⟨w, hw⟩
    refine ⟨EuclideanSpace.finAddEquivProd.symm (w, (EuclideanSpace.finAddEquivProd y).2), ?_⟩
    change operator m a.val _ = y
    rw [operator_apply, ContinuousLinearEquiv.apply_symm_apply]
    change a.val w = (EuclideanSpace.finAddEquivProd y).1 at hw
    change EuclideanSpace.finAddEquivProd.symm
      (a.val w, (EuclideanSpace.finAddEquivProd y).2) = y
    rw [hw]
    exact EuclideanSpace.finAddEquivProd.symm_apply_apply y

theorem range_frame_mono {N n k : ℕ} (m : ℕ) (t : Space N n) (a : Space N k)
    (ha : a.val.range ≤ t.val.range) : (frame m a).val.range ≤ (frame m t).val.range := by
  intro y hy
  exact (mem_range_frame m t y).mpr (ha ((mem_range_frame m a y).mp hy))

theorem extract_frame {N n k : ℕ} (m : ℕ) (t : Space N n) (a : Space N k)
    (ha : a.val.range ≤ t.val.range) :
    RangeCoordinates.extract (frame m t) (frame m a) (range_frame_mono m t a ha) =
      frame m (RangeCoordinates.extract t a ha) := by
  have he : Stiefel.comp (frame m t) (frame m (RangeCoordinates.extract t a ha)) = frame m a := by
    rw [frame_comp, RangeCoordinates.comp_extract]
  have h := RangeCoordinates.extract_comp (frame m t) (frame m (RangeCoordinates.extract t a ha))
  simpa only [he] using h

end NoExoticSixSphere.Stiefel.BlockSum
