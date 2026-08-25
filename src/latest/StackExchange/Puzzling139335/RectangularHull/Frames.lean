import StackExchange.Puzzling139335.Definitions
import Mathlib

/-!
# Rectangle frames and the extreme-vertex bridge

A rectangle is represented by an origin and two nonzero orthogonal edge
vectors.  Its vertices are extreme points of its filled convex hull, so any
set with that convex hull must contain all four vertices.
-/

open Set

namespace Puzzling139335.RectangularHull

structure Frame where
  origin : Plane
  first : Plane
  second : Plane
  first_ne_zero : first ≠ 0
  second_ne_zero : second ≠ 0
  orthogonal : inner ℝ first second = 0

def Frame.vertices (R : Frame) : Set Plane :=
  {R.origin, R.origin + R.first, R.origin + R.first + R.second, R.origin + R.second}

def Frame.carrier (R : Frame) : Set Plane := convexHull ℝ R.vertices

noncomputable def Frame.center (R : Frame) : Plane :=
  R.origin + (1 / 2 : ℝ) • (R.first + R.second)

lemma Frame.vertices_subset_carrier (R : Frame) : R.vertices ⊆ R.carrier :=
  subset_convexHull ℝ R.vertices

lemma Frame.carrier_convex (R : Frame) : Convex ℝ R.carrier :=
  convex_convexHull ℝ R.vertices

lemma Frame.origin_mem_vertices (R : Frame) : R.origin ∈ R.vertices := by
  simp [vertices]

lemma Frame.first_mem_vertices (R : Frame) : R.origin + R.first ∈ R.vertices := by
  simp [vertices]

lemma Frame.both_mem_vertices (R : Frame) : R.origin + R.first + R.second ∈ R.vertices := by
  simp [vertices]

lemma Frame.second_mem_vertices (R : Frame) : R.origin + R.second ∈ R.vertices := by
  simp [vertices]

lemma Frame.vertices_subset_sphere (R : Frame) :
    R.vertices ⊆ Metric.sphere R.center ‖(1 / 2 : ℝ) • (R.first + R.second)‖ := by
  have hnorm : ‖R.first - R.second‖ = ‖R.first + R.second‖ := by
    rw [norm_sub_rev]
    simpa only [add_comm] using norm_sub_eq_norm_add R.orthogonal
  intro x hx
  simp only [vertices, mem_insert_iff, mem_singleton_iff] at hx
  rw [Metric.mem_sphere, dist_eq_norm]
  rcases hx with rfl | rfl | rfl | rfl
  · have hd : R.origin - R.center = -((1 / 2 : ℝ) • (R.first + R.second)) := by
      unfold center
      module
    rw [hd, norm_neg]
  · have hd : R.origin + R.first - R.center = (1 / 2 : ℝ) • (R.first - R.second) := by
      unfold center
      module
    rw [hd, norm_smul, norm_smul, hnorm]
  · have hd : R.origin + R.first + R.second - R.center =
        (1 / 2 : ℝ) • (R.first + R.second) := by
      unfold center
      module
    rw [hd]
  · have hd : R.origin + R.second - R.center =
        -((1 / 2 : ℝ) • (R.first - R.second)) := by
      unfold center
      module
    rw [hd, norm_neg, norm_smul, norm_smul, hnorm]

lemma Frame.carrier_subset_closedBall (R : Frame) :
    R.carrier ⊆ Metric.closedBall R.center ‖(1 / 2 : ℝ) • (R.first + R.second)‖ :=
  convexHull_min (R.vertices_subset_sphere.trans Metric.sphere_subset_closedBall)
    (convex_closedBall _ _)

lemma Frame.vertices_subset_extremePoints (R : Frame) :
    R.vertices ⊆ R.carrier.extremePoints ℝ := by
  intro x hx
  apply inter_extremePoints_subset_extremePoints_of_subset R.carrier_subset_closedBall
  refine ⟨R.vertices_subset_carrier hx, ?_⟩
  rw [StrictConvexSpace.extremePoints_closedBall_eq_sphere]
  exact R.vertices_subset_sphere hx

lemma Frame.extremePoints_carrier (R : Frame) : R.carrier.extremePoints ℝ = R.vertices :=
  Set.Subset.antisymm extremePoints_convexHull_subset R.vertices_subset_extremePoints

lemma Frame.vertices_subset_of_convexHull_eq (R : Frame) {P : Set Plane}
    (hP : convexHull ℝ P = R.carrier) : R.vertices ⊆ P := by
  intro x hx
  apply extremePoints_convexHull_subset (𝕜 := ℝ)
  rw [hP]
  exact R.vertices_subset_extremePoints hx

lemma Frame.subset_carrier_of_convexHull_eq (R : Frame) {P : Set Plane}
    (hP : convexHull ℝ P = R.carrier) : P ⊆ R.carrier := by
  rw [← hP]
  exact subset_convexHull ℝ P

lemma Frame.mem_carrier_iff (R : Frame) {x : Plane} :
    x ∈ R.carrier ↔ ∃ t ∈ Icc (0 : ℝ) 1, ∃ u ∈ Icc (0 : ℝ) 1,
      x = R.origin + t • R.first + u • R.second := by
  constructor
  · intro hx
    have hsub : R.carrier ⊆ {p : Plane | ∃ t ∈ Icc (0 : ℝ) 1,
        ∃ u ∈ Icc (0 : ℝ) 1, p = R.origin + t • R.first + u • R.second} := by
      apply convexHull_min
      · intro p hp
        simp only [vertices, mem_insert_iff, mem_singleton_iff] at hp
        rcases hp with rfl | rfl | rfl | rfl
        · exact ⟨0, by norm_num, 0, by norm_num, by simp⟩
        · exact ⟨1, by norm_num, 0, by norm_num, by simp⟩
        · exact ⟨1, by norm_num, 1, by norm_num, by simp⟩
        · exact ⟨0, by norm_num, 1, by norm_num, by simp⟩
      · rintro p ⟨t, ht, u, hu, rfl⟩ q ⟨v, hv, w, hw, rfl⟩ a b ha hb hab
        refine ⟨a * t + b * v, ?_, a * u + b * w, ?_, ?_⟩
        · exact (convex_Icc (0 : ℝ) 1) ht hv ha hb hab
        · exact (convex_Icc (0 : ℝ) 1) hu hw ha hb hab
        · have horigin : a • R.origin + b • R.origin = R.origin := by
            rw [← add_smul, hab, one_smul]
          calc
            a • (R.origin + t • R.first + u • R.second) +
                b • (R.origin + v • R.first + w • R.second) =
              (a • R.origin + b • R.origin) + (a * t + b * v) • R.first +
                (a * u + b * w) • R.second := by module
            _ = _ := by rw [horigin]
    exact hsub hx
  · rintro ⟨t, ht, u, hu, rfl⟩
    have hlow : R.origin + t • R.first ∈ R.carrier := by
      have h := R.carrier_convex
        (R.vertices_subset_carrier R.origin_mem_vertices)
        (R.vertices_subset_carrier R.first_mem_vertices)
        (show 0 ≤ 1 - t by linarith [ht.2]) ht.1 (show 1 - t + t = 1 by ring)
      convert h using 1
      module
    have hhigh : R.origin + t • R.first + R.second ∈ R.carrier := by
      have h := R.carrier_convex
        (R.vertices_subset_carrier R.second_mem_vertices)
        (R.vertices_subset_carrier R.both_mem_vertices)
        (show 0 ≤ 1 - t by linarith [ht.2]) ht.1 (show 1 - t + t = 1 by ring)
      convert h using 1
      module
    have h := R.carrier_convex hlow hhigh
      (show 0 ≤ 1 - u by linarith [hu.2]) hu.1 (show 1 - u + u = 1 by ring)
    convert h using 1
    module

lemma Frame.carrier_eq_parametrization (R : Frame) :
    R.carrier = {x : Plane | ∃ t ∈ Icc (0 : ℝ) 1, ∃ u ∈ Icc (0 : ℝ) 1,
      x = R.origin + t • R.first + u • R.second} := by
  ext x
  exact R.mem_carrier_iff

end Puzzling139335.RectangularHull
