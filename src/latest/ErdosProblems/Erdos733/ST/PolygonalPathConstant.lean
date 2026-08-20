import ErdosProblems.Erdos733.ST.PolygonalPath

open Classical
noncomputable section

-- [TABLET NODE: PolygonalPathConstant]
lemma PolygonalPathConstant (p : EuclideanSpace ℝ (Fin 2)) :
    ∃ γ : PolygonalPath,
      γ.source = p ∧
        γ.target = p ∧
          γ.carrier = ({p} : Set (EuclideanSpace ℝ (Fin 2))) := by
-- BODY
  let γ : PolygonalPath :=
    { vertices := [p]
      vertices_nonempty := by simp
      source := p
      target := p
      source_eq_head := by simp
      target_eq_last := by simp
      carrier := ({p} : Set (EuclideanSpace ℝ (Fin 2)))
      carrier_eq := by
        ext q
        simp }
  exact ⟨γ, rfl, rfl, rfl⟩
