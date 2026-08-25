import StackExchange.Puzzling139335.N8.Topology
import StackExchange.Puzzling139335.N8.Triangle.Center
import StackExchange.Puzzling139335.N8.Triangle.Jordan
import StackExchange.Puzzling139335.N8.TriangleModel

/-!
# Packing and filling triangular hulls

Two disjoint Jordan interiors cannot both contain all three vertices of a
common nondegenerate triangular hull.  A Jordan region containing all three
actual triangle sides must fill the triangle.
-/

open Set

namespace Puzzling139335.N8

/-- Two Jordan regions inside one nondegenerate triangle cannot both contain
its three actual vertices while their interiors are disjoint. -/
theorem no_two_triangle_hulls {P Q : Set Plane} {a b c : Plane}
    (hP : IsJordanRegion P) (hQ : IsJordanRegion Q)
    (hnonzero : UnitPairs.sideDet a b c ≠ 0)
    (hdis : Disjoint (interior P) (interior Q))
    (hPT : P ⊆ convexHull ℝ ({a, b, c} : Set Plane))
    (hQT : Q ⊆ convexHull ℝ ({a, b, c} : Set Plane))
    (haP : a ∈ P) (hbP : b ∈ P) (hcP : c ∈ P)
    (haQ : a ∈ Q) (hbQ : b ∈ Q) (hcQ : c ∈ Q) : False := by
  have hab : a ≠ b := by
    rintro rfl
    exact hnonzero (by simp [UnitPairs.sideDet])
  have hac : a ≠ c := by
    rintro rfl
    exact hnonzero (by simp [UnitPairs.sideDet])
  have hbc : b ≠ c := by
    rintro rfl
    exact hnonzero (by simp [UnitPairs.sideDet, mul_comm])
  let v : Fin 3 → Plane := ![a, b, c]
  have hinj : Function.Injective v := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [v]
  apply jordan_regions_no_three_common_boundary_points hP hQ
    (isJordanRegion_convexHull_triangle hnonzero) hPT hQT hdis v
  · intro j
    fin_cases j
    · exact haP
    · exact hbP
    · exact hcP
  · intro j
    fin_cases j
    · exact haQ
    · exact hbQ
    · exact hcQ
  · intro j
    fin_cases j
    · exact left_mem_frontier_convexHull_triangle hnonzero
    · exact middle_mem_frontier_convexHull_triangle hnonzero
    · exact right_mem_frontier_convexHull_triangle hnonzero
  · exact hinj

/-- The square admits only one inward unit-equilateral apex on a named side;
two pieces with that side hull therefore share three forbidden boundary contacts. -/
theorem no_two_equilateral_side_hulls {P Q : Set Plane} (i : Fin 4) {c d : Plane}
    (hP : IsJordanRegion P) (hQ : IsJordanRegion Q)
    (hdis : Disjoint (interior P) (interior Q))
    (haP : corner i ∈ P) (hbP : corner (i + 1) ∈ P)
    (haQ : corner i ∈ Q) (hbQ : corner (i + 1) ∈ Q)
    (hcP : c ∈ P) (hdQ : d ∈ Q)
    (hcS : c ∈ unitSquare) (hdS : d ∈ unitSquare)
    (hbc : dist (corner (i + 1)) c = 1) (hca : dist c (corner i) = 1)
    (hbd : dist (corner (i + 1)) d = 1) (hda : dist d (corner i) = 1)
    (hPT : P ⊆ convexHull ℝ ({corner i, corner (i + 1), c} : Set Plane))
    (hQT : Q ⊆ convexHull ℝ ({corner i, corner (i + 1), d} : Set Plane)) : False := by
  have hcd := equilateral_apex_unique i hcS hdS hbc hca hbd hda
  subst d
  exact no_two_triangle_hulls hP hQ
    (UnitPairs.sideDet_ne_zero_of_equidistant (dist_adjacent_corners i) hbc hca)
    hdis hPT hQT haP hbP hcP haQ hbQ hdQ

/-- Predicate form for pieces of a square dissection with the same assigned side. -/
theorem no_two_equilateral_side_hull_pieces {P Q : Set Plane} {i : Fin 4}
    (hP : IsJordanRegion P) (hQ : IsJordanRegion Q)
    (hPS : P ⊆ unitSquare) (hQS : Q ⊆ unitSquare)
    (hdis : Disjoint (interior P) (interior Q))
    (haP : corner i ∈ P) (hbP : corner (i + 1) ∈ P)
    (haQ : corner i ∈ Q) (hbQ : corner (i + 1) ∈ Q)
    (hPside : HasEquilateralSideHull P i) (hQside : HasEquilateralSideHull Q i) :
    False := by
  obtain ⟨c, hcP, hbc, hca, hPT⟩ := hPside
  obtain ⟨d, hdQ, hbd, hda, hQT⟩ := hQside
  exact no_two_equilateral_side_hulls i hP hQ hdis haP hbP haQ hbQ hcP hdQ
    (hPS hcP) (hQS hdQ) hbc hca hbd hda hPT hQT

/-- A Jordan region inside a nondegenerate triangle that contains all three
actual side segments is the entire triangle. -/
theorem eq_triangle_of_three_segments {P : Set Plane} {a b c : Plane}
    (hP : IsJordanRegion P)
    (hPT : P ⊆ convexHull ℝ ({a, b, c} : Set Plane))
    (hnonzero : UnitPairs.sideDet a b c ≠ 0)
    (hab : segment ℝ a b ⊆ P) (hbc : segment ℝ b c ⊆ P)
    (hca : segment ℝ c a ⊆ P) :
    P = convexHull ℝ ({a, b, c} : Set Plane) := by
  apply eq_of_subset_of_frontier_subset hP
    (isJordanRegion_convexHull_triangle hnonzero) hPT
  rw [frontier_convexHull_triangle hnonzero]
  exact union_subset (union_subset hab hbc) hca

end Puzzling139335.N8
