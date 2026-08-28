import Wikipedia.NoExoticSixSphere.NativeSphereHalfCoordinates
import Wikipedia.NoExoticSixSphere.NativeSphereCollapseMaps

/-!
# Exact native-chart formulas for the descended sphere concatenation

On each open half-sphere, the original cubical concatenation is exactly
the corresponding input composed with the checked partial diffeomorphism.
These are neighborhood equalities. The remaining coordinate seam maps to
the actual common base value.
-/

noncomputable section

open Set Function Filter Topology
open scoped unitInterval

namespace NoExoticSixSphere.SmoothCube

open GLOrthonormalization

theorem vectorOfCube_update (n : ℕ) (i : Fin n) (b : ℝ) (u : Fin n → I)
    (h : 2 * (u i : ℝ) - b ∈ Icc (0 : ℝ) 1) :
    vectorOfCube n (Function.update u i (projIcc 0 1 zero_le_one (2 * (u i : ℝ) - b))) =
      expand n i b (vectorOfCube n u) := by
  rw [projIcc_of_mem zero_le_one h]
  ext j
  by_cases hj : j = i
  · subst j
    change (Function.update u i ⟨2 * (u i : ℝ) - b, h⟩ i : ℝ) = _
    rw [Function.update_self, expand_apply_self]
    rfl
  · change (Function.update u i ⟨2 * (u i : ℝ) - b, h⟩ j : ℝ) =
      Function.update (fun j ↦ (u j : ℝ)) i _ j
    rw [Function.update_of_ne hj, Function.update_of_ne hj]

theorem quotient_update_half (b : ℝ) (u : Fin 3 → I)
    (hu : vectorOfCube 3 u ∈ halfCube 3 0 b) :
    quotient 3 (Function.update u 0 (projIcc 0 1 zero_le_one (2 * (u 0 : ℝ) - b))) =
      (sphereChart 3).symm (expand 3 0 b (vectorOfCube 3 u)) := by
  have hh : 2 * (u 0 : ℝ) - b ∈ Icc (0 : ℝ) 1 := by
    have ht := (expand_mem_openCube 3 0 b hu) 0
    rw [expand_apply_self] at ht
    exact ⟨ht.1.le, ht.2.le⟩
  have hv := vectorOfCube_update 3 0 b u hh
  have hq : Function.update u 0 (projIcc 0 1 zero_le_one (2 * (u 0 : ℝ) - b)) ∉
      Cube.boundary (Fin 3) := by
    apply (vectorOfCube_mem_openCube 3 _).mp
    rw [hv]
    exact expand_mem_openCube 3 0 b hu
  rw [quotient_interior 3 ⟨_, hq⟩, hv]

variable {X : Type*} [TopologicalSpace X] {x : X}

theorem concatenate_left (f g : BasedMap 3 X x) (y : Sphere 3) (hy : y ∈ halfSphere 0) :
    (concatenate f g).val y = f.val (halfSphereCoordinates 0 (by constructor <;> norm_num) y) := by
  obtain ⟨u, rfl⟩ := quotient_surjective (by decide : 0 < 3) y
  have hnu : u ∉ Cube.boundary (Fin 3) := fun h ↦ hy.1 (quotient_boundary 3 u h)
  have hchart := sphereChart_quotient 3 u hnu
  have hh : vectorOfCube 3 u ∈ halfCube 3 0 0 := hchart ▸ hy.2
  have hhalf : (u 0 : ℝ) ≤ 1 / 2 := by
    have ht := hh.2.2
    change (u 0 : ℝ) < (0 + 1) / 2 at ht
    simpa only [zero_add] using ht.le
  rw [concatenate_formula, if_pos hhalf]
  change f.val (quotient 3 (Function.update u 0 (projIcc 0 1 zero_le_one (2 * (u 0 : ℝ))))) =
    f.val ((sphereChart 3).symm (expand 3 0 0 (sphereChart 3 (quotient 3 u))))
  rw [hchart]
  have hq := quotient_update_half 0 u hh
  simpa only [sub_zero] using congrArg f.val hq

theorem concatenate_right (f g : BasedMap 3 X x) (y : Sphere 3) (hy : y ∈ halfSphere 1) :
    (concatenate f g).val y = g.val (halfSphereCoordinates 1 (by constructor <;> norm_num) y) := by
  obtain ⟨u, rfl⟩ := quotient_surjective (by decide : 0 < 3) y
  have hnu : u ∉ Cube.boundary (Fin 3) := fun h ↦ hy.1 (quotient_boundary 3 u h)
  have hchart := sphereChart_quotient 3 u hnu
  have hh : vectorOfCube 3 u ∈ halfCube 3 0 1 := hchart ▸ hy.2
  have hhalf : ¬(u 0 : ℝ) ≤ 1 / 2 := not_le.mpr hh.2.1
  rw [concatenate_formula, if_neg hhalf]
  change g.val (quotient 3
      (Function.update u 0 (projIcc 0 1 zero_le_one (2 * (u 0 : ℝ) - 1)))) =
    g.val ((sphereChart 3).symm (expand 3 0 1 (sphereChart 3 (quotient 3 u))))
  rw [hchart]
  exact congrArg g.val (quotient_update_half 1 u hh)

theorem concatenate_eventuallyEq_left (f g : BasedMap 3 X x) (y : Sphere 3)
    (hy : y ∈ halfSphere 0) :
    ((concatenate f g).val : Sphere 3 → X) =ᶠ[𝓝 y]
      fun z ↦ f.val (halfSphereCoordinates 0 (by constructor <;> norm_num) z) := by
  filter_upwards [(halfSphereCoordinates 0 (by constructor <;> norm_num)).open_source.mem_nhds hy]
    with z hz
  exact concatenate_left f g z hz

theorem concatenate_eventuallyEq_right (f g : BasedMap 3 X x) (y : Sphere 3)
    (hy : y ∈ halfSphere 1) :
    ((concatenate f g).val : Sphere 3 → X) =ᶠ[𝓝 y]
      fun z ↦ g.val (halfSphereCoordinates 1 (by constructor <;> norm_num) z) := by
  filter_upwards [(halfSphereCoordinates 1 (by constructor <;> norm_num)).open_source.mem_nhds hy]
    with z hz
  exact concatenate_right f g z hz

theorem collapse_coordinate_seam (y : Sphere 3) (hy : y ≠ spherePole 3)
    (ht : sphereChart 3 y 0 = 1 / 2) :
    leftCollapse y = spherePole 3 ∧ rightCollapse y = spherePole 3 := by
  obtain ⟨u, rfl⟩ := quotient_surjective (by decide : 0 < 3) y
  have hnu : u ∉ Cube.boundary (Fin 3) := fun h ↦ hy (quotient_boundary 3 u h)
  rw [sphereChart_quotient 3 u hnu] at ht
  exact ⟨leftCollapse_seam u ht, rightCollapse_seam u ht⟩

theorem concatenate_coordinate_seam (f g : BasedMap 3 X x) (y : Sphere 3)
    (hy : y ≠ spherePole 3) (ht : sphereChart 3 y 0 = 1 / 2) :
    (concatenate f g).val y = x := by
  have hc := collapse_coordinate_seam y hy ht
  rcases concatenate_eq_left_or_right f g y with h | h
  · rw [h, hc.1]
    exact f.property
  · rw [h, hc.2]
    exact g.property

end NoExoticSixSphere.SmoothCube
