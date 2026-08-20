import ErdosProblems.Erdos733.ST.PolygonalArc

open Classical
noncomputable section

-- [TABLET NODE: TwoSegmentPolygonalArc]
lemma TwoSegmentPolygonalArc
    (a z b : EuclideanSpace ℝ (Fin 2))
    (haz : a ≠ z)
    (hncol : ¬ ∃ c : ℝ, b - a = c • (z - a)) :
    ∃ Γ : PolygonalArc,
      Γ.source = a ∧
        Γ.target = b ∧
          Γ.carrier = segment ℝ a z ∪ segment ℝ z b ∧
            Γ.relativeInterior =
              (segment ℝ a z ∪ segment ℝ z b) \
                ({a, b} : Set (EuclideanSpace ℝ (Fin 2))) := by
-- BODY
  let E := EuclideanSpace ℝ (Fin 2)
  have hLI_az_ab : LinearIndependent ℝ ![z - a, b - a] := by
    rw [LinearIndependent.pair_iff' (sub_ne_zero.mpr haz.symm)]
    intro c hc
    exact hncol ⟨c, hc.symm⟩
  have hLI_za_zb : LinearIndependent ℝ ![a - z, b - z] := by
    rw [LinearIndependent.pair_iff' (sub_ne_zero.mpr haz)]
    intro c hc
    apply hncol
    refine ⟨1 - c, ?_⟩
    calc
      b - a = (b - z) + (z - a) := by abel
      _ = c • (a - z) + (z - a) := by rw [← hc]
      _ = (1 - c) • (z - a) := by module
  have haz_inter :
      segment ℝ a z ∩ segment ℝ z b = ({z} : Set E) := by
    have h :=
      segment_inter_eq_endpoint_of_linearIndependent_sub
        (𝕜 := ℝ) (c := z) (x := a) (y := b) hLI_za_zb
    simpa [segment_symm, Set.inter_comm] using h
  have hzb : z ≠ b := by
    intro h
    apply hncol
    refine ⟨1, ?_⟩
    simp [h]
  have hab : a ≠ b := by
    intro h
    apply hncol
    refine ⟨0, ?_⟩
    simp [h]
  have hb_not_open_az : b ∉ openSegment ℝ a z := by
    intro hb
    have hb_inter : b ∈ segment ℝ a z ∩ segment ℝ z b :=
      ⟨openSegment_subset_segment ℝ a z hb, right_mem_segment ℝ z b⟩
    have hbz : b ∈ ({z} : Set E) := by
      simpa [haz_inter] using hb_inter
    have hb_eq_z : b = z := by simpa using hbz
    exact hzb hb_eq_z.symm
  have ha_not_open_zb : a ∉ openSegment ℝ z b := by
    intro ha
    have ha_inter : a ∈ segment ℝ a z ∩ segment ℝ z b :=
      ⟨left_mem_segment ℝ a z, openSegment_subset_segment ℝ z b ha⟩
    have haz' : a ∈ ({z} : Set E) := by
      simpa [haz_inter] using ha_inter
    exact haz (by simpa using haz')
  refine ⟨
    { vertices := [a, z, b]
      length_ge_two := by norm_num
      source := a
      target := b
      source_eq_head := by simp
      target_eq_last := by simp
      carrier := segment ℝ a z ∪ segment ℝ z b
      relativeInterior :=
        (segment ℝ a z ∪ segment ℝ z b) \ ({a, b} : Set E)
      carrier_eq := ?_
      relativeInterior_eq := rfl
      simple_vertices := by simp [haz, hzb, hab]
      segment_intersections := ?_
      vertices_avoid_nonincident_interiors := ?_ },
    by simp⟩
  · ext p
    constructor
    · intro hp
      rcases hp with hp | hp
      · refine ⟨0, by norm_num, ?_⟩
        simpa using hp
      · refine ⟨1, by norm_num, ?_⟩
        simpa using hp
    · rintro ⟨i, hi, hp⟩
      have hi' : i + 1 < 3 := by simpa using hi
      have hi_cases : i = 0 ∨ i = 1 := by omega
      rcases hi_cases with rfl | rfl
      · exact Or.inl (by simpa using hp)
      · exact Or.inr (by simpa using hp)
  · intro i j hi hj hij
    have hi' : i + 1 < 3 := by simpa using hi
    have hj' : j + 1 < 3 := by simpa using hj
    have hi_cases : i = 0 ∨ i = 1 := by omega
    have hj_cases : j = 0 ∨ j = 1 := by omega
    rcases hi_cases with rfl | rfl <;> rcases hj_cases with rfl | rfl
    · omega
    · simp [haz_inter]
    · omega
    · omega
  · intro i k hi hk hki hkine
    have hi' : i + 1 < 3 := by simpa using hi
    have hk' : k < 3 := by simpa using hk
    have hi_cases : i = 0 ∨ i = 1 := by omega
    have hk_cases : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hi_cases with rfl | rfl
    · rcases hk_cases with rfl | h
      · exact (hki rfl).elim
      · rcases h with rfl | rfl
        · exact (hkine rfl).elim
        · simpa using hb_not_open_az
    · rcases hk_cases with rfl | h
      · simpa using ha_not_open_zb
      · rcases h with rfl | rfl
        · exact (hki rfl).elim
        · exact (hkine rfl).elim
