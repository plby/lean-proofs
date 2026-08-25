import Util.IncidenceGeometry.Basic

open Classical
noncomputable section

lemma EndpointUnitDiskLocalFivePointVerticesAvoid
    (toWorld : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (coord : EuclideanSpace ℝ (Fin 2) → ℝ)
    (P0 P1 P2 P3 P4 : EuclideanSpace ℝ (Fin 2))
    (hbetween :
      ∀ {A B C : EuclideanSpace ℝ (Fin 2)},
        toWorld C ∈ openSegment ℝ (toWorld A) (toWorld B) →
          coord A < coord B →
            coord A < coord C ∧ coord C < coord B)
    (hstrict :
      coord P0 < coord P1 ∧
        coord P1 < coord P2 ∧
          coord P2 < coord P3 ∧
            coord P3 < coord P4) :
    ∀ ⦃i k : ℕ⦄,
      (hi : i + 1 <
        [toWorld P0, toWorld P1, toWorld P2, toWorld P3, toWorld P4].length) →
      (hk : k <
        [toWorld P0, toWorld P1, toWorld P2, toWorld P3, toWorld P4].length) →
      k ≠ i →
      k ≠ i + 1 →
      [toWorld P0, toWorld P1, toWorld P2, toWorld P3, toWorld P4][k] ∉
        openSegment ℝ
          [toWorld P0, toWorld P1, toWorld P2, toWorld P3, toWorld P4][i]
          [toWorld P0, toWorld P1, toWorld P2, toWorld P3, toWorld P4][i + 1] := by
  rcases hstrict with ⟨h01, h12, h23, h34⟩
  intro i k hi hk hki hks hmem
  have hi4 : i < 4 := by
    have hi' : i + 1 < 5 := by simpa using hi
    omega
  have hk5 : k < 5 := by
    simpa using hk
  interval_cases i <;> interval_cases k <;>
    simp at hki hks hmem ⊢
  all_goals
    first
    | contradiction
    | have hb := hbetween hmem (by linarith)
      linarith
