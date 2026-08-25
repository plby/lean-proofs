import Util.IncidenceGeometry.CyclicCurvePresentation

open Classical
noncomputable section

def CyclicPresentationTriangleGeneralPosition
    {J : SimpleClosedPolygonalCurve} {K : FinitePolygonalSet}
    (R : CyclicCurvePresentation J K)
    (z a b : EuclideanSpace ℝ (Fin 2)) : Prop :=
  (∀ p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ R.vertices},
      p.1 ∉ segment ℝ z a ∧ p.1 ∉ segment ℝ a b ∧ p.1 ∉ segment ℝ b z) ∧
    z ∉ J.carrier ∧ a ∉ J.carrier ∧ b ∉ J.carrier ∧
      (∀ p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ R.vertices},
        ¬ ∃ u v : EuclideanSpace ℝ (Fin 2),
          u ≠ v ∧
            segment ℝ u v ⊆
              segment ℝ p.1 (R.successor p).1 ∩ segment ℝ z a) ∧
        (∀ p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ R.vertices},
          ¬ ∃ u v : EuclideanSpace ℝ (Fin 2),
            u ≠ v ∧
              segment ℝ u v ⊆
                segment ℝ p.1 (R.successor p).1 ∩ segment ℝ a b) ∧
          (∀ p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ R.vertices},
            ¬ ∃ u v : EuclideanSpace ℝ (Fin 2),
              u ≠ v ∧
                segment ℝ u v ⊆
                  segment ℝ p.1 (R.successor p).1 ∩ segment ℝ b z) ∧
            (∀ (p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ R.vertices})
                (x : EuclideanSpace ℝ (Fin 2)),
              x ∈ openSegment ℝ p.1 (R.successor p).1 →
                x ∈ openSegment ℝ z a →
                  ¬ ∃ c : ℝ, a - z = c • ((R.successor p).1 - p.1)) ∧
              (∀ (p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ R.vertices})
                  (x : EuclideanSpace ℝ (Fin 2)),
                x ∈ openSegment ℝ p.1 (R.successor p).1 →
                  x ∈ openSegment ℝ a b →
                    ¬ ∃ c : ℝ, b - a = c • ((R.successor p).1 - p.1)) ∧
                (∀ (p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ R.vertices})
                    (x : EuclideanSpace ℝ (Fin 2)),
                  x ∈ openSegment ℝ p.1 (R.successor p).1 →
                    x ∈ openSegment ℝ b z →
                      ¬ ∃ c : ℝ, z - b = c • ((R.successor p).1 - p.1)) ∧
                  Set.Finite
                    (J.carrier ∩
                      (segment ℝ z a ∪ segment ℝ a b ∪ segment ℝ b z))
