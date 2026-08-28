import Wikipedia.NoExoticSixSphere.PartialFrameBlockIteration
import Wikipedia.NoExoticSixSphere.SphereDiskExtension

/-!
# Any finite identity block preserves the exact four-ball extension obstruction

The proof iterates the checked one-column parity theorem on the actual
coordinate-block maps. The number of added columns is arbitrary, and the
extension statement does not require a chosen arithmetic presentation of
the dimensions.
-/

noncomputable section

namespace NoExoticSixSphere.Stiefel.BlockSum

open GLOrthonormalization DiskBoundary

theorem extends_one_iff {N n : ℕ} (hn : 2 ≤ n) (hN : N = 3 + n)
    (f : C(Sphere 3, Space N n)) : Extends ((map 1).comp f) ↔ Extends f := by
  obtain ⟨r, rfl⟩ : ∃ r, n = r + 2 := ⟨n - 2, by omega⟩
  subst N
  have hleft : Extends ((map 1).comp f) ↔
      sphereThirdObstruction (r + 1) ((map 1).comp f) = 0 :=
    (sphereThirdObstruction_zero_iff_extension (r + 1) ((map 1).comp f)).symm
  have hright : Extends f ↔ sphereThirdObstruction r f = 0 :=
    (sphereThirdObstruction_zero_iff_extension r f).symm
  rw [hleft, hright, sphere_parity_one]

theorem extends_block_iff {N n : ℕ} (hn : 2 ≤ n) (hN : N = 3 + n)
    (m : ℕ) (f : C(Sphere 3, Space N n)) : Extends ((map m).comp f) ↔ Extends f := by
  induction m with
  | zero =>
      have he : (map 0).comp f = f := by
        apply ContinuousMap.ext
        intro s
        exact frame_zero (f s)
      rw [he]
  | succ m ih =>
      rw [map_succ_comp m, extends_one_iff (by omega) (by omega)]
      exact ih

end NoExoticSixSphere.Stiefel.BlockSum
