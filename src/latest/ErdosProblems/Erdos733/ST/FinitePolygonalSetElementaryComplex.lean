import ErdosProblems.Erdos733.ST.FinitePolygonalSet
import Mathlib.Data.Finset.Sort

open Classical
noncomputable section

-- [TABLET NODE: FinitePolygonalSetElementaryComplex]
structure FinitePolygonalSetElementaryComplex (K : FinitePolygonalSet) where
-- BODY
  vertices : Finset (EuclideanSpace ℝ (Fin 2))
  edges : Finset (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))
  vertices_eq_points : vertices = K.points
  edge_source_mem :
    ∀ e : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
      e ∈ edges → e.1 ∈ vertices
  edge_target_mem :
    ∀ e : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
      e ∈ edges → e.2 ∈ vertices
  edge_nondegenerate :
    ∀ e : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
      e ∈ edges → e.1 ≠ e.2
  edge_consecutive_cut :
    ∀ e : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
      e ∈ edges →
        ∃ s : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
          s ∈ K.segments ∧
            ∃ L : List ℝ,
              L.Nodup ∧
                L.SortedLT ∧
                  (∀ t : ℝ, t ∈ L ↔
                    t = 0 ∨ t = 1 ∨
                      (0 ≤ t ∧ t ≤ 1 ∧
                        AffineMap.lineMap s.1 s.2 t ∈ K.points)) ∧
                    (0 : ℝ) ∈ L ∧
                      (1 : ℝ) ∈ L ∧
                        (∀ t : ℝ, t ∈ L → 0 ≤ t ∧ t ≤ 1) ∧
                          (∀ n (hn : n + 1 < L.length), L[n] < L[n + 1]) ∧
                            (∀ n (hn : n + 1 < L.length) t,
                              0 ≤ t → t ≤ 1 →
                                AffineMap.lineMap s.1 s.2 t ∈ K.points →
                                  ¬ (L[n] < t ∧ t < L[n + 1])) ∧
                              ∃ k, ∃ hk : k + 1 < L.length,
                                e.1 = AffineMap.lineMap s.1 s.2 L[k] ∧
                                  e.2 = AffineMap.lineMap s.1 s.2 L[k + 1]
  edge_subset_raw :
    ∀ e : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
      e ∈ edges →
        ∃ s : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
          s ∈ K.segments ∧ segment ℝ e.1 e.2 ⊆ segment ℝ s.1 s.2
  no_vertex_in_edge_interior :
    ∀ e : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
      e ∈ edges →
        ∀ v : EuclideanSpace ℝ (Fin 2),
          v ∈ vertices → v ∉ openSegment ℝ e.1 e.2
  edge_open_interiors_disjoint :
    ∀ e f : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
      e ∈ edges → f ∈ edges → e ≠ f →
        Disjoint (openSegment ℝ e.1 e.2) (openSegment ℝ f.1 f.2)
  carrier_eq :
    K.carrier =
      (vertices : Set (EuclideanSpace ℝ (Fin 2))) ∪
        ⋃ e : {e // e ∈ edges}, segment ℝ e.1.1 e.1.2
