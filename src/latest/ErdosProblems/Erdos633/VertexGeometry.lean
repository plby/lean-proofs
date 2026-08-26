import ErdosProblems.Erdos633.TriangleAngles
import Mathlib.Analysis.Convex.Extreme

/-!
# Vertices of triangles and their dissections

The three geometric vertices are exactly the extreme points of the closed
carrier. Consequently, a tile containing an outer vertex must have a vertex
there. These statements hold for arbitrary triangular dissections.
-/

namespace Erdos633

def Triangle.vertex (P : Triangle) : Fin 3 → ℂ := ![P.a, P.b, P.c]

theorem Triangle.vertex_injective (P : Triangle) : Function.Injective P.vertex :=
  P.affineIndependent.injective

theorem Triangle.range_vertex (P : Triangle) : Set.range P.vertex = {P.a, P.b, P.c} := by
  ext z
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp [Triangle.vertex]
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩

theorem affineEquiv_image_extremePoints (e : ℂ ≃ᵃ[ℝ] ℂ) (s : Set ℂ) :
    e '' s.extremePoints ℝ = (e '' s).extremePoints ℝ := by
  ext z
  have hseg : ∀ x y, e '' openSegment ℝ x y = openSegment ℝ (e x) (e y) :=
    image_openSegment ℝ e.toAffineMap
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨x, hx.1, rfl⟩, ?_⟩
    rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩ h
    have h' : x ∈ openSegment ℝ y z := by
      apply e.injective.mem_set_image.mp
      rw [hseg]
      exact h
    exact congrArg e (hx.2 hy hz h')
  · intro h
    obtain ⟨x, hx, rfl⟩ := h.1
    refine ⟨x, ⟨hx, ?_⟩, rfl⟩
    intro y hy z hz h'
    apply e.injective
    apply h.2 ⟨y, hy, rfl⟩ ⟨z, hz, rfl⟩
    rw [← hseg]
    exact ⟨x, h', rfl⟩

theorem standardTriangle_zero_extreme :
    (0 : ℂ) ∈ standardTriangle.carrier.extremePoints ℝ := by
  refine ⟨?_, ?_⟩
  · rw [standardTriangle_carrier]
    norm_num
  · intro x hx y hy hxy
    rw [standardTriangle_carrier] at hx hy
    obtain ⟨a, b, ha, hb, _, heq⟩ := hxy
    have hre := congrArg Complex.re heq
    have him := congrArg Complex.im heq
    simp only [Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im,
      Complex.zero_re, Complex.zero_im, smul_eq_mul] at hre him
    have hxr : x.re = 0 := by
      have hby := mul_nonneg hb.le hy.1
      have hax : a * x.re = 0 := by nlinarith only [hre, hby, mul_nonneg ha.le hx.1]
      exact (mul_eq_zero.mp hax).resolve_left (ne_of_gt ha)
    have hxi : x.im = 0 := by
      have hby := mul_nonneg hb.le hy.2.1
      have hax : a * x.im = 0 := by nlinarith only [him, hby, mul_nonneg ha.le hx.2.1]
      exact (mul_eq_zero.mp hax).resolve_left (ne_of_gt ha)
    exact Complex.ext hxr hxi

theorem Triangle.a_extreme (P : Triangle) : P.a ∈ P.carrier.extremePoints ℝ := by
  have hmap : P.coordinateEquiv '' standardTriangle.carrier = P.carrier := by
    rw [← Triangle.mapAffineEquiv_carrier, P.standard_map_coordinateEquiv]
  rw [← hmap, ← affineEquiv_image_extremePoints]
  exact ⟨0, standardTriangle_zero_extreme, P.coordinateEquiv_zero⟩

theorem Triangle.vertex_extreme (P : Triangle) (i : Fin 3) :
    P.vertex i ∈ P.carrier.extremePoints ℝ := by
  fin_cases i
  · exact P.a_extreme
  · have h := P.rotate.a_extreme
    rw [P.rotate_carrier] at h
    exact h
  · have h := P.rotate.rotate.a_extreme
    rw [P.rotate.rotate_carrier, P.rotate_carrier] at h
    exact h

theorem Triangle.extremePoints_carrier (P : Triangle) :
    P.carrier.extremePoints ℝ = Set.range P.vertex := by
  apply Set.Subset.antisymm
  · rw [P.range_vertex]
    exact extremePoints_convexHull_subset
  · rintro _ ⟨i, rfl⟩
    exact P.vertex_extreme i

theorem Triangle.vertex_mem_carrier (P : Triangle) (i : Fin 3) :
    P.vertex i ∈ P.carrier := extremePoints_subset (P.vertex_extreme i)

theorem Triangle.vertex_of_mem_subtriangle (P Q : Triangle) (hsub : Q.carrier ⊆ P.carrier)
    (i : Fin 3) (hi : P.vertex i ∈ Q.carrier) : ∃ j, Q.vertex j = P.vertex i := by
  have hext := inter_extremePoints_subset_extremePoints_of_subset hsub
    ⟨hi, P.vertex_extreme i⟩
  rw [Q.extremePoints_carrier] at hext
  exact hext

theorem TriangleDissection.outer_vertex_incidence {P : Triangle} {N : ℕ}
    (T : TriangleDissection P N) (i : Fin 3) :
    ∃ j : Fin N, ∃ k : Fin 3, (T.tile j).vertex k = P.vertex i := by
  have h := P.vertex_mem_carrier i
  rw [← T.covers, Set.mem_iUnion] at h
  obtain ⟨j, hj⟩ := h
  obtain ⟨k, hk⟩ := P.vertex_of_mem_subtriangle (T.tile j) (T.tile_subset j) i hj
  exact ⟨j, k, hk⟩

theorem TriangleDissection.mem_tile_at_outer_vertex_iff {P : Triangle} {N : ℕ}
    (T : TriangleDissection P N) (i : Fin 3) (j : Fin N) :
    P.vertex i ∈ (T.tile j).carrier ↔ ∃ k : Fin 3, (T.tile j).vertex k = P.vertex i := by
  constructor
  · exact P.vertex_of_mem_subtriangle (T.tile j) (T.tile_subset j) i
  · rintro ⟨k, hk⟩
    rw [← hk]
    exact (T.tile j).vertex_mem_carrier k

end Erdos633
