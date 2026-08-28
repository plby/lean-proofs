import Wikipedia.NoExoticSixSphere.CubicalSphereSuspension
import Wikipedia.NoExoticSixSphere.ProductSphereSuspensionComparison

/-!
# Exact cube coordinates for the product sphere suspension

The standard smooth-interior cube quotient splits into its first line
coordinate and the quotient on the remaining coordinates. This is an
equality of the existing maps, including every collapsed boundary face.
The ordered product coordinates are also compared to the previously
constructed product-compactification suspension map.
-/

noncomputable section

open Set Function Topology
open scoped unitInterval OnePoint

namespace NoExoticSixSphere.CubicalSphereSuspension

open SmoothCube CubicalProductSuspension

theorem quotient_finite_coordinates (n : ℕ) (u : Fin n → I)
    (hu : u ∉ Cube.boundary (Fin n)) :
    (euclideanOnePointSphere n).symm (SmoothCube.quotient n u) =
      (↑(coordinate n (vectorOfCube n u)) : OnePoint _) := by
  rw [SmoothCube.quotient_interior n ⟨u, hu⟩]
  change (euclideanOnePointSphere n).symm
    ((sphereProjection n).symm (coordinate n (vectorOfCube n u))) = _
  rw [← euclideanOnePointSphere_coe, Homeomorph.symm_apply_apply]

theorem quotient_product (m : ℕ) (u : Fin (m + 1) → I) :
    sphereHomeomorph m (OnePointProduct.map
      (clock (u 0), (euclideanOnePointSphere m).symm (SmoothCube.quotient m (tail u)))) =
      SmoothCube.quotient (m + 1) u := by
  by_cases hu : u ∈ Cube.boundary (Fin (m + 1))
  · rw [SmoothCube.quotient_boundary (m + 1) u hu]
    obtain ⟨i, hi⟩ := hu
    refine Fin.cases ?_ (fun j ↦ ?_) i hi
    · intro h
      rcases h with h | h
      · rw [h, clock_zero, OnePointProduct.map_infty_left, sphereHomeomorph_infty]
      · rw [h, clock_one, OnePointProduct.map_infty_left, sphereHomeomorph_infty]
    · intro h
      rw [SmoothCube.quotient_boundary m (tail u) ⟨j, h⟩,
        inverseSphere_pole, OnePointProduct.map_infty_right, sphereHomeomorph_infty]
  · have ht : tail u ∉ Cube.boundary (Fin m) := by
      rintro ⟨i, hi⟩
      exact hu ⟨i.succ, hi⟩
    have hline : (fun _ : Fin 1 ↦ u 0) ∉ Cube.boundary (Fin 1) := by
      rintro ⟨i, hi⟩
      exact hu ⟨0, hi⟩
    have hc : clock (u 0) =
        (↑(coordinate 1 (vectorOfCube 1 (fun _ ↦ u 0))) : OnePoint Line) :=
      quotient_finite_coordinates 1 _ hline
    rw [hc, quotient_finite_coordinates m (tail u) ht, OnePointProduct.map_coe,
      sphereHomeomorph_coe]
    have hv : productCoordinates m
        (coordinate 1 (vectorOfCube 1 (fun _ ↦ u 0)), coordinate m (vectorOfCube m (tail u))) =
        coordinate (m + 1) (vectorOfCube (m + 1) u) := by
      ext i
      exact Fin.cases rfl (fun _ ↦ rfl) i
    rw [hv]
    exact (congrArg (euclideanOnePointSphere (m + 1))
      (quotient_finite_coordinates (m + 1) u hu)).symm.trans
        ((euclideanOnePointSphere (m + 1)).apply_symm_apply _)

theorem sphereHomeomorph_product_swap (n : ℕ)
    (s : OnePoint Line) (x : OnePoint (EuclideanSpace ℝ (Fin n))) :
    sphereHomeomorph n (OnePointProduct.map (s, x)) =
      SuspensionProductComparison.productSphereHomeomorph n
        (OnePointProduct.map (x, lineHomeomorph.onePointCongr s)) := by
  induction s using OnePoint.rec with
  | infty =>
    change sphereHomeomorph n (OnePointProduct.map (∞, x)) =
      SuspensionProductComparison.productSphereHomeomorph n (OnePointProduct.map (x, ∞))
    rw [OnePointProduct.map_infty_left, OnePointProduct.map_infty_right]
    rfl
  | coe s =>
    induction x using OnePoint.rec with
    | infty =>
      rw [OnePointProduct.map_infty_right, OnePointProduct.map_infty_left]
      rfl
    | coe x =>
      change sphereHomeomorph n (OnePointProduct.map (↑s, ↑x)) =
        SuspensionProductComparison.productSphereHomeomorph n
          (OnePointProduct.map (↑x, ↑(lineHomeomorph s)))
      rw [OnePointProduct.map_coe, OnePointProduct.map_coe]
      rfl

theorem productSphereMap_product_formula {m n : ℕ}
    (f : C(OnePoint (EuclideanSpace ℝ (Fin m)), OnePoint (EuclideanSpace ℝ (Fin n))))
    (hf : f ∞ = ∞) (s : OnePoint Line) (x : OnePoint (EuclideanSpace ℝ (Fin m))) :
    SuspensionProductComparison.productSphereMap f hf
        (sphereHomeomorph m (OnePointProduct.map (s, x))) =
      sphereHomeomorph n (OnePointProduct.map (s, f x)) := by
  rw [sphereHomeomorph_product_swap, sphereHomeomorph_product_swap]
  change SuspensionProductComparison.productSphereHomeomorph n
    (OnePointProduct.productMap f (ContinuousMap.id (OnePoint ℝ)) hf rfl
      ((SuspensionProductComparison.productSphereHomeomorph m).symm
        (SuspensionProductComparison.productSphereHomeomorph m
          (OnePointProduct.map (x, lineHomeomorph.onePointCongr s))))) = _
  rw [Homeomorph.symm_apply_apply]
  exact congrArg (SuspensionProductComparison.productSphereHomeomorph n)
    (OnePointProduct.productMap_apply f (ContinuousMap.id (OnePoint ℝ)) hf rfl
      (x, lineHomeomorph.onePointCongr s))

end NoExoticSixSphere.CubicalSphereSuspension
