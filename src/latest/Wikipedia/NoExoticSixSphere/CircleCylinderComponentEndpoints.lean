import Wikipedia.NoExoticSixSphere.CircleCylinderComponentState
import Wikipedia.NoExoticSixSphere.DiffeomorphSumClopen

/-!
# The chosen component retains the whole left endpoint and either all or none of the right

A preconnected endpoint maps into a single genuine connected component.
Thus the component through an original left seam point contains every
left seam point, and its restricted boundary is either the full original
endpoint sum or exactly the original left summand. No conclusion about
connectedness of the whole double is imposed.
-/

noncomputable section

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace NoExoticSixSphere.CircleCylinder

variable {m n : ℕ} {b : Sphere n}
  (d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) b 0 1)

theorem leftInclusion_mem_component [PreconnectedSpace {x : Sphere m // d.leftMap x = b}]
    (x y : {x : Sphere m // d.leftMap x = b}) :
    leftInclusion d y ∈ connectedComponent (leftInclusion d x) := by
  apply (leftInclusion d).continuous.mapsTo_connectedComponent x
  rw [PreconnectedSpace.connectedComponent_eq_univ]
  exact mem_univ y

theorem rightInclusion_mem_component_of_mem
    [PreconnectedSpace {x : Sphere m // d.rightMap x = b}] (p : Fiber d)
    (x : {x : Sphere m // d.rightMap x = b})
    (hx : rightInclusion d x ∈ connectedComponent p) (y : {x : Sphere m // d.rightMap x = b}) :
    rightInclusion d y ∈ connectedComponent p := by
  rw [connectedComponent_eq hx]
  apply (rightInclusion d).continuous.mapsTo_connectedComponent x
  rw [PreconnectedSpace.connectedComponent_eq_univ]
  exact mem_univ y

theorem rightInclusion_component_all_or_none
    [PreconnectedSpace {x : Sphere m // d.rightMap x = b}] (p : Fiber d) :
    (∀ y, rightInclusion d y ∉ connectedComponent p) ∨
      (∀ y, rightInclusion d y ∈ connectedComponent p) := by
  classical
  by_cases h : ∃ x, rightInclusion d x ∈ connectedComponent p
  · obtain ⟨x, hx⟩ := h
    exact Or.inr (rightInclusion_mem_component_of_mem d p x hx)
  · exact Or.inl (not_exists.mp h)

theorem componentEndpoints_eq_top_of_right_mem
    [PreconnectedSpace {x : Sphere m // d.leftMap x = b}]
    [PreconnectedSpace {x : Sphere m // d.rightMap x = b}]
    (k : ℕ) (hd : m = n + k) (x : {x : Sphere m // d.leftMap x = b})
    (y : {x : Sphere m // d.rightMap x = b})
    (hy : rightInclusion d y ∈ connectedComponent (leftInclusion d x)) :
    componentEndpoints d k hd (leftInclusion d x) = ⊤ := by
  apply Opens.ext
  apply Set.eq_univ_of_forall
  intro q
  apply (mem_componentEndpoints d k hd (leftInclusion d x) q).mpr
  cases q with
  | inl z => exact leftInclusion_mem_component d x z
  | inr z => exact rightInclusion_mem_component_of_mem d (leftInclusion d x) y hy z

theorem componentEndpoints_eq_left_of_right_not_mem
    [PreconnectedSpace {x : Sphere m // d.leftMap x = b}]
    (k : ℕ) (hd : m = n + k) (x : {x : Sphere m // d.leftMap x = b})
    (hy : ∀ y, rightInclusion d y ∉ connectedComponent (leftInclusion d x)) :
    componentEndpoints d k hd (leftInclusion d x) =
      DiffeomorphSumClopen.leftOpen {x : Sphere m // d.leftMap x = b}
        {x : Sphere m // d.rightMap x = b} := by
  apply Opens.ext
  ext q
  refine (mem_componentEndpoints d k hd (leftInclusion d x) q).trans ?_
  cases q with
  | inl z =>
    exact iff_of_true (leftInclusion_mem_component d x z) ⟨z, rfl⟩
  | inr z =>
    exact iff_of_false (hy z) (by simp [DiffeomorphSumClopen.leftOpen])

end NoExoticSixSphere.CircleCylinder
