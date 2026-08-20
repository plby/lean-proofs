import ErdosProblems.Erdos733.ST.PolygonalPath
import Mathlib.Tactic

open Classical
noncomputable section

set_option linter.unusedVariables false

-- [TABLET NODE: PolygonalPathRetainedElementaryEdges]
structure PolygonalPathRetainedElementaryEdges
    (γ : PolygonalPath) (cutVertices : Finset (EuclideanSpace ℝ (Fin 2))) where
-- BODY
  subdivisionList : Fin (γ.vertices.length - 1) → List ℝ
  retainedEdges :
    Finset (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))
  subdivision_nodup :
    ∀ (i : Fin (γ.vertices.length - 1)),
      γ.vertices[i.1]'(by omega) ≠ γ.vertices[i.1 + 1]'(by omega) →
        (subdivisionList i).Nodup
  subdivision_sorted :
    ∀ (i : Fin (γ.vertices.length - 1)),
      γ.vertices[i.1]'(by omega) ≠ γ.vertices[i.1 + 1]'(by omega) →
        (subdivisionList i).SortedLT
  subdivision_mem :
    ∀ (i : Fin (γ.vertices.length - 1))
      (hseg :
        γ.vertices[i.1]'(by omega) ≠ γ.vertices[i.1 + 1]'(by omega))
      (t : ℝ),
        t ∈ subdivisionList i ↔
          t = 0 ∨ t = 1 ∨
            (0 ≤ t ∧ t ≤ 1 ∧
              AffineMap.lineMap
                (γ.vertices[i.1]'(by omega))
                (γ.vertices[i.1 + 1]'(by omega)) t ∈ cutVertices)
  subdivision_zero :
    ∀ (i : Fin (γ.vertices.length - 1)),
      γ.vertices[i.1]'(by omega) ≠ γ.vertices[i.1 + 1]'(by omega) →
        (0 : ℝ) ∈ subdivisionList i
  subdivision_one :
    ∀ (i : Fin (γ.vertices.length - 1)),
      γ.vertices[i.1]'(by omega) ≠ γ.vertices[i.1 + 1]'(by omega) →
        (1 : ℝ) ∈ subdivisionList i
  subdivision_bounds :
    ∀ (i : Fin (γ.vertices.length - 1))
      (hseg :
        γ.vertices[i.1]'(by omega) ≠ γ.vertices[i.1 + 1]'(by omega))
      (t : ℝ),
        t ∈ subdivisionList i → 0 ≤ t ∧ t ≤ 1
  subdivision_lt :
    ∀ (i : Fin (γ.vertices.length - 1))
      (hseg :
        γ.vertices[i.1]'(by omega) ≠ γ.vertices[i.1 + 1]'(by omega))
      (k : ℕ) (hk : k + 1 < (subdivisionList i).length),
        (subdivisionList i)[k] < (subdivisionList i)[k + 1]
  subdivision_no_between :
    ∀ (i : Fin (γ.vertices.length - 1))
      (hseg :
        γ.vertices[i.1]'(by omega) ≠ γ.vertices[i.1 + 1]'(by omega))
      (k : ℕ) (hk : k + 1 < (subdivisionList i).length) (t : ℝ),
        0 ≤ t → t ≤ 1 →
          AffineMap.lineMap
            (γ.vertices[i.1]'(by omega))
            (γ.vertices[i.1 + 1]'(by omega)) t ∈ cutVertices →
            ¬ ((subdivisionList i)[k] < t ∧
              t < (subdivisionList i)[k + 1])
  elementary_source_mem :
    ∀ (i : Fin (γ.vertices.length - 1))
      (hseg :
        γ.vertices[i.1]'(by omega) ≠ γ.vertices[i.1 + 1]'(by omega))
      (k : ℕ) (hk : k + 1 < (subdivisionList i).length),
        AffineMap.lineMap
          (γ.vertices[i.1]'(by omega))
          (γ.vertices[i.1 + 1]'(by omega))
          ((subdivisionList i)[k]'(Nat.lt_of_succ_lt hk)) ∈ cutVertices
  elementary_target_mem :
    ∀ (i : Fin (γ.vertices.length - 1))
      (hseg :
        γ.vertices[i.1]'(by omega) ≠ γ.vertices[i.1 + 1]'(by omega))
      (k : ℕ) (hk : k + 1 < (subdivisionList i).length),
        AffineMap.lineMap
          (γ.vertices[i.1]'(by omega))
          (γ.vertices[i.1 + 1]'(by omega))
          ((subdivisionList i)[k + 1]'hk) ∈ cutVertices
  elementary_nondegenerate :
    ∀ (i : Fin (γ.vertices.length - 1))
      (hseg :
        γ.vertices[i.1]'(by omega) ≠ γ.vertices[i.1 + 1]'(by omega))
      (k : ℕ) (hk : k + 1 < (subdivisionList i).length),
        AffineMap.lineMap
            (γ.vertices[i.1]'(by omega))
            (γ.vertices[i.1 + 1]'(by omega))
            ((subdivisionList i)[k]'(Nat.lt_of_succ_lt hk)) ≠
          AffineMap.lineMap
            (γ.vertices[i.1]'(by omega))
            (γ.vertices[i.1 + 1]'(by omega))
            ((subdivisionList i)[k + 1]'hk)
  elementary_subset_original :
    ∀ (i : Fin (γ.vertices.length - 1))
      (hseg :
        γ.vertices[i.1]'(by omega) ≠ γ.vertices[i.1 + 1]'(by omega))
      (k : ℕ) (hk : k + 1 < (subdivisionList i).length),
        segment ℝ
            (AffineMap.lineMap
              (γ.vertices[i.1]'(by omega))
              (γ.vertices[i.1 + 1]'(by omega))
              ((subdivisionList i)[k]'(Nat.lt_of_succ_lt hk)))
            (AffineMap.lineMap
              (γ.vertices[i.1]'(by omega))
              (γ.vertices[i.1 + 1]'(by omega))
              ((subdivisionList i)[k + 1]'hk)) ⊆
          segment ℝ
            (γ.vertices[i.1]'(by omega))
            (γ.vertices[i.1 + 1]'(by omega))
  elementary_subset_carrier :
    ∀ (i : Fin (γ.vertices.length - 1))
      (hseg :
        γ.vertices[i.1]'(by omega) ≠ γ.vertices[i.1 + 1]'(by omega))
      (k : ℕ) (hk : k + 1 < (subdivisionList i).length),
        segment ℝ
            (AffineMap.lineMap
              (γ.vertices[i.1]'(by omega))
              (γ.vertices[i.1 + 1]'(by omega))
              ((subdivisionList i)[k]'(Nat.lt_of_succ_lt hk)))
            (AffineMap.lineMap
              (γ.vertices[i.1]'(by omega))
              (γ.vertices[i.1 + 1]'(by omega))
              ((subdivisionList i)[k + 1]'hk)) ⊆
          γ.carrier
  elementary_no_cut_open :
    ∀ (i : Fin (γ.vertices.length - 1))
      (hseg :
        γ.vertices[i.1]'(by omega) ≠ γ.vertices[i.1 + 1]'(by omega))
      (k : ℕ) (hk : k + 1 < (subdivisionList i).length)
      (v : EuclideanSpace ℝ (Fin 2)),
        v ∈ cutVertices →
          v ∉ openSegment ℝ
            (AffineMap.lineMap
              (γ.vertices[i.1]'(by omega))
              (γ.vertices[i.1 + 1]'(by omega))
              ((subdivisionList i)[k]'(Nat.lt_of_succ_lt hk)))
            (AffineMap.lineMap
              (γ.vertices[i.1]'(by omega))
              (γ.vertices[i.1 + 1]'(by omega))
              ((subdivisionList i)[k + 1]'hk))
  original_segment_covered :
    ∀ (i : Fin (γ.vertices.length - 1))
      (hseg :
        γ.vertices[i.1]'(by omega) ≠ γ.vertices[i.1 + 1]'(by omega)),
        segment ℝ
            (γ.vertices[i.1]'(by omega))
            (γ.vertices[i.1 + 1]'(by omega)) ⊆
          ⋃ k : {k : ℕ // k + 1 < (subdivisionList i).length},
            segment ℝ
              (AffineMap.lineMap
                (γ.vertices[i.1]'(by omega))
                (γ.vertices[i.1 + 1]'(by omega))
                ((subdivisionList i)[k.1]'(Nat.lt_of_succ_lt k.2)))
              (AffineMap.lineMap
                (γ.vertices[i.1]'(by omega))
                (γ.vertices[i.1 + 1]'(by omega))
                ((subdivisionList i)[k.1 + 1]'k.2))
  represented_exactly_one :
    ∀ (i : Fin (γ.vertices.length - 1))
      (hseg :
        γ.vertices[i.1]'(by omega) ≠ γ.vertices[i.1 + 1]'(by omega))
      (k : ℕ) (hk : k + 1 < (subdivisionList i).length),
        let a :=
          AffineMap.lineMap
            (γ.vertices[i.1]'(by omega))
            (γ.vertices[i.1 + 1]'(by omega))
            ((subdivisionList i)[k]'(Nat.lt_of_succ_lt hk))
        let b :=
          AffineMap.lineMap
            (γ.vertices[i.1]'(by omega))
            (γ.vertices[i.1 + 1]'(by omega))
            ((subdivisionList i)[k + 1]'hk)
        ((a, b) ∈ retainedEdges ∧ (b, a) ∉ retainedEdges) ∨
          ((b, a) ∈ retainedEdges ∧ (a, b) ∉ retainedEdges)
  retained_edge_data :
    ∀ e : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
      e ∈ retainedEdges →
        e.1 ∈ cutVertices ∧
          e.2 ∈ cutVertices ∧
            e.1 ≠ e.2 ∧
              (∃ (i : Fin (γ.vertices.length - 1))
                (hseg :
                  γ.vertices[i.1]'(by omega) ≠
                    γ.vertices[i.1 + 1]'(by omega))
                (k : ℕ) (hk : k + 1 < (subdivisionList i).length),
                  let a :=
                    AffineMap.lineMap
                      (γ.vertices[i.1]'(by omega))
                      (γ.vertices[i.1 + 1]'(by omega))
                      ((subdivisionList i)[k]'(Nat.lt_of_succ_lt hk))
                  let b :=
                    AffineMap.lineMap
                      (γ.vertices[i.1]'(by omega))
                      (γ.vertices[i.1 + 1]'(by omega))
                      ((subdivisionList i)[k + 1]'hk)
                  (e = (a, b) ∨ e = (b, a)) ∧
                    segment ℝ e.1 e.2 ⊆
                      segment ℝ
                        (γ.vertices[i.1]'(by omega))
                        (γ.vertices[i.1 + 1]'(by omega)) ∧
                    segment ℝ e.1 e.2 ⊆ γ.carrier)
  retained_sym2_injective :
    ∀ {e f : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)},
      e ∈ retainedEdges → f ∈ retainedEdges →
        Sym2.mk e.1 e.2 = Sym2.mk f.1 f.2 → e = f

