import Wikipedia.NoExoticSixSphere.CircleCylinderSeamDifferential
import Wikipedia.NoExoticSixSphere.RegularFiberTimeSubmersion

/-!
# The actual seam time is regular on the compact circle-double fiber

At either original endpoint every circle direction lies in the kernel
of the doubled cylinder map. The seam differential supplies a circle
direction with any prescribed real derivative. The native regular-fiber
tangent equality lifts it to the actual fiber, proving regularity there.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.CircleCylinder

variable {m n : ℕ} {b : Sphere n}
  (d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) b 0 1)

theorem regular_time_zero (k : ℕ) (hd : m = n + k) (p : Fiber d) (hp : time d p = 0) :
    letI := fiberAtlas d k hd;
    Surjective (mfderiv (𝓡 (k + 1)) 𝓘(ℝ, ℝ) (time d) p) := by
  let := fiberAtlas d k hd
  apply regularFiber_surjective_mfderiv_time (map d) (contMDiff_map d) b (regular_map d)
    (k + 1) (dimension_eq k hd) (seam ∘ Prod.fst)
    (contMDiff_seam.comp contMDiff_fst) p
  intro z
  obtain ⟨u, hu⟩ := surjective_mfderiv_seam p.val.1 hp z
  refine ⟨(u, 0), mfderiv_map_circle_zero d p.val hp u, ?_⟩
  rw [mfderiv_comp p.val (contMDiff_seam.mdifferentiableAt (by simp))
    mdifferentiableAt_fst, mfderiv_fst]
  exact hu

end NoExoticSixSphere.CircleCylinder
