import ErdosProblems.Erdos633b.SixtyCoordinates
import ErdosProblems.Erdos633b.TriangleMaps

/-! Construct nondegenerate triangles from prescribed coordinates in any triangle's affine basis. -/

namespace Erdos633b.Triangle

noncomputable def ofCoords (T : Triangle) (s₀ t₀ s₁ t₁ s₂ t₂ : ℝ)
    (hdet : (s₁ - s₀) * (t₂ - t₀) - (s₂ - s₀) * (t₁ - t₀) ≠ 0) : Triangle :=
  (Sixty.triangle 1 (by norm_num) s₀ t₀ s₁ t₁ s₂ t₂ hdet).map
    ((Sixty.frame 1 (by norm_num)).vertexMap T)
    ((Sixty.frame 1 (by norm_num)).vertexMap_bijective T).injective

theorem ofCoords_point (T : Triangle) (s₀ t₀ s₁ t₁ s₂ t₂ : ℝ)
    (hdet : (s₁ - s₀) * (t₂ - t₀) - (s₂ - s₀) * (t₁ - t₀) ≠ 0) (i : Fin 3) :
    (T.ofCoords s₀ t₀ s₁ t₁ s₂ t₂ hdet).points i =
      T.latticeShift (![s₀, s₁, s₂] i) (![t₀, t₁, t₂] i) + T.points 0 := by
  have hp : (Sixty.triangle 1 (by norm_num) s₀ t₀ s₁ t₁ s₂ t₂ hdet).points i =
      Sixty.point 1 (![s₀, s₁, s₂] i) (![t₀, t₁, t₂] i) := by fin_cases i <;> rfl
  change (Sixty.frame 1 (by norm_num)).vertexMap T
    ((Sixty.triangle 1 (by norm_num) s₀ t₀ s₁ t₁ s₂ t₂ hdet).points i) = _
  rw [hp, vertexMap_apply, (Sixty.frame_coords 1 (by norm_num) _ _).1,
    (Sixty.frame_coords 1 (by norm_num) _ _).2]

theorem ofCoords_coord_one (T : Triangle) (s₀ t₀ s₁ t₁ s₂ t₂ : ℝ)
    (hdet : (s₁ - s₀) * (t₂ - t₀) - (s₂ - s₀) * (t₁ - t₀) ≠ 0) (i : Fin 3) :
    T.coord 1 ((T.ofCoords s₀ t₀ s₁ t₁ s₂ t₂ hdet).points i) = ![s₀, s₁, s₂] i := by
  rw [ofCoords_point, coord_shift_one]
  simp [coord_vertex]

theorem ofCoords_coord_two (T : Triangle) (s₀ t₀ s₁ t₁ s₂ t₂ : ℝ)
    (hdet : (s₁ - s₀) * (t₂ - t₀) - (s₂ - s₀) * (t₁ - t₀) ≠ 0) (i : Fin 3) :
    T.coord 2 ((T.ofCoords s₀ t₀ s₁ t₁ s₂ t₂ hdet).points i) = ![t₀, t₁, t₂] i := by
  rw [ofCoords_point, coord_shift_two]
  simp [coord_vertex]

end Erdos633b.Triangle
