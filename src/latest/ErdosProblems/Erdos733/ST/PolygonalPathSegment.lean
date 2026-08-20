import ErdosProblems.Erdos733.ST.PolygonalPath

open Classical
noncomputable section

-- [TABLET NODE: PolygonalPathSegment]
lemma PolygonalPathSegment
    (p q : EuclideanSpace ℝ (Fin 2)) :
    ∃ γ : PolygonalPath,
      γ.source = p ∧
        γ.target = q ∧
          γ.carrier = segment ℝ p q := by
-- BODY
  let γ : PolygonalPath :=
    { vertices := [p, q]
      vertices_nonempty := by simp
      source := p
      target := q
      source_eq_head := by simp
      target_eq_last := by simp
      carrier := segment ℝ p q
      carrier_eq := by
        ext r
        constructor
        · intro hr
          right
          exact ⟨0, by simp, by simpa using hr⟩
        · intro hr
          rcases hr with hr_end | hr_seg
          · rcases hr_end with hrp | hrq
            · cases hrp
              exact left_mem_segment ℝ p q
            · cases hrq
              exact right_mem_segment ℝ p q
          · rcases hr_seg with ⟨i, hi, hri⟩
            have hi_lt : i + 1 < 2 := by simpa using hi
            have hi0 : i = 0 := by omega
            subst i
            simpa using hri }
  exact ⟨γ, rfl, rfl, rfl⟩
