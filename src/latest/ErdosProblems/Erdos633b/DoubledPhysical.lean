import ErdosProblems.Erdos633b.DoubledCoordinates

/-! Identify the four certified triangular regions with the explicit Euclidean vertices. -/

namespace Erdos633b

theorem Triangle.ofCoords_points_of_coords (T : Triangle) (s₀ t₀ s₁ t₁ s₂ t₂ : ℝ)
    (hdet : (s₁ - s₀) * (t₂ - t₀) - (s₂ - s₀) * (t₁ - t₀) ≠ 0)
    (p : Fin 3 → Plane) (hs : ∀ i, T.coord 1 (p i) = ![s₀, s₁, s₂] i)
    (ht : ∀ i, T.coord 2 (p i) = ![t₀, t₁, t₂] i) :
    (T.ofCoords s₀ t₀ s₁ t₁ s₂ t₂ hdet).points = p := by
  funext i
  exact T.ext_coords ((T.ofCoords_coord_one _ _ _ _ _ _ _ i).trans (hs i).symm)
    ((T.ofCoords_coord_two _ _ _ _ _ _ _ i).trans (ht i).symm)

namespace DoubledPartition.Layout

theorem abdTriangle_points (L : Layout) (T : Triangle) (D : Plane)
    (hD : T.coord 1 D = L.u ∧ T.coord 2 D = L.v) :
    (L.abdTriangle T).points = ![T.points 0, T.points 1, D] := by
  apply T.ofCoords_points_of_coords
  · intro i
    fin_cases i <;> simp_all [Triangle.coord_vertex]
  · intro i
    fin_cases i <;> simp_all [Triangle.coord_vertex]

theorem bdgTriangle_points (L : Layout) (T : Triangle) (D G : Plane)
    (hD : T.coord 1 D = L.u ∧ T.coord 2 D = L.v)
    (hG : T.coord 1 G = 1 - L.r ∧ T.coord 2 G = L.r) :
    (L.bdgTriangle T).points = ![T.points 1, D, G] := by
  apply T.ofCoords_points_of_coords
  · intro i
    fin_cases i <;> simp_all [Triangle.coord_vertex]
  · intro i
    fin_cases i <;> simp_all [Triangle.coord_vertex]

theorem aefTriangle_points (L : Layout) (T : Triangle) (E F : Plane)
    (hE : T.coord 1 E = L.ε * L.u ∧ T.coord 2 E = L.ε * L.v)
    (hF : T.coord 1 F = 0 ∧ T.coord 2 F = L.μ) :
    (L.aefTriangle T).points = ![T.points 0, E, F] := by
  apply T.ofCoords_points_of_coords
  · intro i
    fin_cases i <;> simp_all [Triangle.coord_vertex]
  · intro i
    fin_cases i <;> simp_all [Triangle.coord_vertex]

theorem cfgTriangle_points (L : Layout) (T : Triangle) (F G : Plane)
    (hF : T.coord 1 F = 0 ∧ T.coord 2 F = L.μ)
    (hG : T.coord 1 G = 1 - L.r ∧ T.coord 2 G = L.r) :
    (L.cfgTriangle T).points = ![T.points 2, F, G] := by
  apply T.ofCoords_points_of_coords
  · intro i
    fin_cases i <;> simp_all [Triangle.coord_vertex]
  · intro i
    fin_cases i <;> simp_all [Triangle.coord_vertex]

end DoubledPartition.Layout
end Erdos633b
