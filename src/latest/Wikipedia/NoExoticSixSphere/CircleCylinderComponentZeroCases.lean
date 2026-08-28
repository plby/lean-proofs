import Wikipedia.NoExoticSixSphere.CircleCylinderComponentEndpoints
import Wikipedia.NoExoticSixSphere.CircleCylinderClopenEndpoints

/-!
# The native component zero set is either both seams or exactly the left seam

The actual endpoint diffeomorphism converts the component membership
case split into equality of native open subsets of the zero manifold.
No connectedness of the original endpoint sum or the whole double is used.
-/

noncomputable section

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace NoExoticSixSphere.CircleCylinder

open Wikipedia.HopfProblem.DegreeCollapse

variable {m n : ℕ} {b : Sphere n}
  (d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) b 0 1)
  (hd : m = n + 6) (a : Sphere 1 × Sphere m)
  [PreconnectedSpace {x : Sphere m // d.leftMap x = b}]
  (x : {x : Sphere m // d.leftMap x = b})

theorem componentZeroOpen_eq_top_of_right_mem
    [PreconnectedSpace {x : Sphere m // d.rightMap x = b}]
    (y : {x : Sphere m // d.rightMap x = b})
    (hy : rightInclusion d y ∈ connectedComponent (leftInclusion d x)) :
    (lowCollaredState d hd a).zeroOpen (componentOpen d 6 hd (leftInclusion d x)) = ⊤ := by
  let := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left 6 (by simpa using hd)
  let := regularFiberAtlas d.rightMap d.smooth_right b d.regular_right 6 (by simpa using hd)
  let := timeZeroAtlas d 6 hd
  apply Opens.ext
  apply Set.eq_univ_of_forall
  intro p
  obtain ⟨q, rfl⟩ := (endpointsDiffeomorph d 6 hd).surjective p
  change endpointsMap d q ∈ connectedComponent (leftInclusion d x)
  cases q with
  | inl z => exact leftInclusion_mem_component d x z
  | inr z => exact rightInclusion_mem_component_of_mem d (leftInclusion d x) y hy z

theorem componentZeroOpen_eq_left_of_right_not_mem
    (hy : ∀ y, rightInclusion d y ∉ connectedComponent (leftInclusion d x)) :
    (lowCollaredState d hd a).zeroOpen (componentOpen d 6 hd (leftInclusion d x)) =
      leftZeroOpen d 6 hd := by
  let := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left 6 (by simpa using hd)
  let := regularFiberAtlas d.rightMap d.smooth_right b d.regular_right 6 (by simpa using hd)
  let := timeZeroAtlas d 6 hd
  apply Opens.ext
  ext p
  obtain ⟨q, rfl⟩ := (endpointsDiffeomorph d 6 hd).surjective p
  change endpointsMap d q ∈ connectedComponent (leftInclusion d x) ↔
    (endpointsDiffeomorph d 6 hd).symm (endpointsDiffeomorph d 6 hd q) ∈ range Sum.inl
  rw [Diffeomorph.symm_apply_apply]
  cases q with
  | inl z => exact iff_of_true (leftInclusion_mem_component d x z) ⟨z, rfl⟩
  | inr z => exact iff_of_false (hy z) (by simp)

end NoExoticSixSphere.CircleCylinder
