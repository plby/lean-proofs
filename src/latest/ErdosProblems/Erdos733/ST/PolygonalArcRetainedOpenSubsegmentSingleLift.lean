import Mathlib.Tactic
import ErdosProblems.Erdos733.ST.PolygonalArc

open Classical
noncomputable section


-- [TABLET NODE: PolygonalArcRetainedOpenSubsegmentSingleLift]
lemma PolygonalArcRetainedOpenSubsegmentSingleLift
    (Q R : PolygonalArc)
    (a b : EuclideanSpace ℝ (Fin 2))
    (i : ℕ) (hi : i + 1 < Q.vertices.length)
    (hsubsegment_direction :
      ∃ d : ℝ, d ≠ 0 ∧
        b - a = d • (Q.vertices[i + 1] - Q.vertices[i]))
    (htransfer :
      ∀ z, z ∈ openSegment ℝ a b →
        ∃ j : ℕ, ∃ hj : j + 1 < R.vertices.length,
          z ∈ openSegment ℝ R.vertices[j] R.vertices[j + 1] ∧
            ∃ c : ℝ, c ≠ 0 ∧
              R.vertices[j + 1] - R.vertices[j] =
                c • (Q.vertices[i + 1] - Q.vertices[i])) :
    ∃ j : ℕ, ∃ hj : j + 1 < R.vertices.length,
      openSegment ℝ a b ⊆
          openSegment ℝ R.vertices[j] R.vertices[j + 1] ∧
        ∃ c : ℝ, c ≠ 0 ∧
          R.vertices[j + 1] - R.vertices[j] =
            c • (Q.vertices[i + 1] - Q.vertices[i]) := by
-- BODY
  have retained_avoids_vertices :
      ∀ z, z ∈ openSegment ℝ a b → z ∉ R.vertices := by
    intro z hzOld hzVertex
    obtain ⟨k, hk, hkz⟩ := List.mem_iff_getElem.mp hzVertex
    rcases htransfer z hzOld with ⟨j, hj, hzOpen, _c, _hc, _hdir⟩
    have hkj : k ≠ j := by
      intro h
      subst k
      have hleft : R.vertices[j] ∈
          openSegment ℝ R.vertices[j] R.vertices[j + 1] := by
        simpa [hkz] using hzOpen
      have hne : R.vertices[j] ≠ R.vertices[j + 1] := by
        exact (List.Nodup.getElem_inj_iff R.simple_vertices).not.mpr (by omega)
      exact hne (left_mem_openSegment_iff.mp hleft)
    have hkjs : k ≠ j + 1 := by
      intro h
      subst k
      have hright : R.vertices[j + 1] ∈
          openSegment ℝ R.vertices[j] R.vertices[j + 1] := by
        simpa [hkz] using hzOpen
      have hne : R.vertices[j] ≠ R.vertices[j + 1] := by
        exact (List.Nodup.getElem_inj_iff R.simple_vertices).not.mpr (by omega)
      exact hne (right_mem_openSegment_iff.mp hright)
    exact R.vertices_avoid_nonincident_interiors hj hk hkj hkjs
      (by simpa [hkz] using hzOpen)
  have parallel_cover :
      ∀ (a₀ b₀ a₁ b₁ z₀ : EuclideanSpace ℝ (Fin 2)) (c : ℝ),
        c ≠ 0 →
          b₁ - a₁ = c • (b₀ - a₀) →
            z₀ ∈ openSegment ℝ a₀ b₀ →
              z₀ ∈ openSegment ℝ a₁ b₁ →
                a₁ ∉ openSegment ℝ a₀ b₀ →
                  b₁ ∉ openSegment ℝ a₀ b₀ →
                    openSegment ℝ a₀ b₀ ⊆ openSegment ℝ a₁ b₁ := by
    intro a₀ b₀ a₁ b₁ z₀ c hc hdir hzOld hzNew ha₁ hb₁
    simp only [openSegment_eq_image_lineMap] at hzOld hzNew ⊢
    rcases hzOld with ⟨u₀, hu₀, hzu₀⟩
    rcases hzNew with ⟨t₀, ht₀, hzt₀⟩
    let s : ℝ := u₀ - t₀ * c
    have ha₁line : a₁ = AffineMap.lineMap a₀ b₀ s := by
      have heq₀ : AffineMap.lineMap a₁ b₁ t₀ =
          AffineMap.lineMap a₀ b₀ u₀ := hzt₀.trans hzu₀.symm
      have heq : t₀ • (b₁ - a₁) + a₁ =
          u₀ • (b₀ - a₀) + a₀ := by
        simpa only [AffineMap.lineMap_apply_module'] using heq₀
      rw [hdir, smul_smul] at heq
      calc
        a₁ = (u₀ • (b₀ - a₀) + a₀) -
            (t₀ * c) • (b₀ - a₀) := by
          rw [← heq]
          abel
        _ = AffineMap.lineMap a₀ b₀ s := by
          dsimp [s]
          simp only [AffineMap.lineMap_apply_module']
          module
    have hb₁line : b₁ = AffineMap.lineMap a₀ b₀ (s + c) := by
      calc
        b₁ = a₁ + (b₁ - a₁) := by abel
        _ = AffineMap.lineMap a₀ b₀ s + c • (b₀ - a₀) := by
          rw [hdir, ha₁line]
        _ = AffineMap.lineMap a₀ b₀ (s + c) := by
          simp only [AffineMap.lineMap_apply_module']
          module
    have hs_not : ¬ (0 < s ∧ s < 1) := by
      intro hs
      apply ha₁
      rw [openSegment_eq_image_lineMap]
      exact ⟨s, hs, ha₁line.symm⟩
    have hsc_not : ¬ (0 < s + c ∧ s + c < 1) := by
      intro hsc
      apply hb₁
      rw [openSegment_eq_image_lineMap]
      exact ⟨s + c, hsc, hb₁line.symm⟩
    have hu₀eq : u₀ = s + t₀ * c := by
      dsimp [s]
      ring
    intro z hz
    rcases hz with ⟨u, hu, hzu⟩
    by_cases hcpos : 0 < c
    · have hsle : s ≤ 0 := by
        by_contra hs0
        have hspos : 0 < s := lt_of_not_ge hs0
        have hsu₀ : s < u₀ := by
          rw [hu₀eq]
          nlinarith [mul_pos ht₀.1 hcpos]
        exact hs_not ⟨hspos, hsu₀.trans hu₀.2⟩
      have honele : 1 ≤ s + c := by
        by_contra hsc1
        have hsclt : s + c < 1 := lt_of_not_ge hsc1
        have hu₀sc : u₀ < s + c := by
          rw [hu₀eq]
          nlinarith [mul_pos (sub_pos.mpr ht₀.2) hcpos]
        exact hsc_not ⟨hu₀.1.trans hu₀sc, hsclt⟩
      refine ⟨(u - s) / c, ?_, ?_⟩
      · constructor
        · exact div_pos (sub_pos.mpr (lt_of_le_of_lt hsle hu.1)) hcpos
        · apply (div_lt_one hcpos).2
          have hu_sc : u < s + c := hu.2.trans_le honele
          linarith
      · rw [← hzu, ha₁line, hb₁line]
        have hnested : ∀ t : ℝ,
            AffineMap.lineMap (AffineMap.lineMap a₀ b₀ s)
                (AffineMap.lineMap a₀ b₀ (s + c)) t =
              AffineMap.lineMap a₀ b₀ (s + t * c) := by
          intro t
          simp only [AffineMap.lineMap_apply_module']
          module
        rw [hnested]
        congr 1
        field_simp [hc]
        ring
    · have hcneg : c < 0 := lt_of_le_of_ne (le_of_not_gt hcpos) hc
      have hscone : s + c ≤ 0 := by
        by_contra hsc0
        have hscpos : 0 < s + c := lt_of_not_ge hsc0
        have hscu₀ : s + c < u₀ := by
          rw [hu₀eq]
          nlinarith [mul_pos (sub_pos.mpr ht₀.2) (neg_pos.mpr hcneg)]
        exact hsc_not ⟨hscpos, hscu₀.trans hu₀.2⟩
      have honele : 1 ≤ s := by
        by_contra hs1
        have hslt : s < 1 := lt_of_not_ge hs1
        have hu₀s : u₀ < s := by
          rw [hu₀eq]
          nlinarith [mul_neg_of_pos_of_neg ht₀.1 hcneg]
        exact hs_not ⟨hu₀.1.trans hu₀s, hslt⟩
      refine ⟨(u - s) / c, ?_, ?_⟩
      · constructor
        · exact div_pos_of_neg_of_neg
            (sub_neg.mpr (hu.2.trans_le honele)) hcneg
        · rw [div_lt_one_of_neg hcneg]
          have hsc_u : s + c < u := hscone.trans_lt hu.1
          linarith
      · rw [← hzu, ha₁line, hb₁line]
        have hnested : ∀ t : ℝ,
            AffineMap.lineMap (AffineMap.lineMap a₀ b₀ s)
                (AffineMap.lineMap a₀ b₀ (s + c)) t =
              AffineMap.lineMap a₀ b₀ (s + t * c) := by
          intro t
          simp only [AffineMap.lineMap_apply_module']
          module
        rw [hnested]
        congr 1
        field_simp [hc]
        ring
  let z₀ := AffineMap.lineMap a b (1 / 2 : ℝ)
  have hz₀ : z₀ ∈ openSegment ℝ a b := by
    apply lineMap_mem_openSegment
    norm_num
  rcases htransfer z₀ hz₀ with ⟨j, hj, hz₀New, c, hc, hdir⟩
  rcases hsubsegment_direction with ⟨d, hd, hsubdir⟩
  have hcoverdir : R.vertices[j + 1] - R.vertices[j] =
      (c / d) • (b - a) := by
    rw [hdir, hsubdir, smul_smul]
    congr 1
    field_simp [hd]
  have hleft : R.vertices[j] ∉ openSegment ℝ a b := by
    intro hmem
    exact retained_avoids_vertices R.vertices[j] hmem (List.getElem_mem _)
  have hright : R.vertices[j + 1] ∉ openSegment ℝ a b := by
    intro hmem
    exact retained_avoids_vertices R.vertices[j + 1] hmem (List.getElem_mem _)
  exact ⟨j, hj,
    parallel_cover a b R.vertices[j] R.vertices[j + 1]
      z₀ (c / d) (div_ne_zero hc hd) hcoverdir hz₀ hz₀New hleft hright,
    c, hc, hdir⟩
