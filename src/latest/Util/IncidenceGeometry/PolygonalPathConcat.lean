import Util.IncidenceGeometry.PolygonalPath

open Classical
noncomputable section

lemma PolygonalPathConcat
    (S : Set (EuclideanSpace ℝ (Fin 2))) (γ η : PolygonalPath) :
    γ.target = η.source →
      γ.carrier ⊆ S →
        η.carrier ⊆ S →
          ∃ ζ : PolygonalPath,
            ζ.source = γ.source ∧
              ζ.target = η.target ∧
                ζ.carrier ⊆ S := by
  intro hmatch hγS hηS
  have hγsource : γ.source ∈ γ.carrier := by
    rw [γ.carrier_eq]
    exact Or.inl (Or.inl rfl)
  have hγtarget : γ.target ∈ γ.carrier := by
    rw [γ.carrier_eq]
    exact Or.inl (Or.inr rfl)
  have hηsource : η.source ∈ η.carrier := by
    rw [η.carrier_eq]
    exact Or.inl (Or.inl rfl)
  have hηtarget : η.target ∈ η.carrier := by
    rw [η.carrier_eq]
    exact Or.inl (Or.inr rfl)
  let ζ : PolygonalPath :=
    { vertices := γ.vertices ++ η.vertices
      vertices_nonempty := by simp [γ.vertices_nonempty]
      source := γ.source
      target := η.target
      source_eq_head := by
        rw [List.head?_append_of_ne_nil _ γ.vertices_nonempty]
        exact γ.source_eq_head
      target_eq_last := by
        rw [List.getLast?_append_of_ne_nil _ η.vertices_nonempty]
        exact η.target_eq_last
      carrier :=
        ({γ.source, η.target} : Set (EuclideanSpace ℝ (Fin 2))) ∪
          {p | ∃ i : ℕ, ∃ hi : i + 1 < (γ.vertices ++ η.vertices).length,
            p ∈ segment ℝ (γ.vertices ++ η.vertices)[i]
              (γ.vertices ++ η.vertices)[i + 1]}
      carrier_eq := rfl }
  refine ⟨ζ, rfl, rfl, ?_⟩
  intro p hp
  change p ∈
      (({γ.source, η.target} : Set (EuclideanSpace ℝ (Fin 2))) ∪
        {p | ∃ i : ℕ, ∃ hi : i + 1 < (γ.vertices ++ η.vertices).length,
          p ∈ segment ℝ (γ.vertices ++ η.vertices)[i]
            (γ.vertices ++ η.vertices)[i + 1]}) at hp
  rcases hp with hp_end | hp_seg
  · rcases hp_end with hp_source | hp_target
    · subst p
      exact hγS hγsource
    · subst p
      exact hηS hηtarget
  · rcases hp_seg with ⟨i, hi, hpi⟩
    have hi_total : i + 1 < γ.vertices.length + η.vertices.length := by
      simpa using hi
    by_cases hleft : i + 1 < γ.vertices.length
    · apply hγS
      rw [γ.carrier_eq]
      right
      refine ⟨i, hleft, ?_⟩
      have hget_i :
          (γ.vertices ++ η.vertices)[i] = γ.vertices[i] := by
        exact List.getElem_append_left (as := γ.vertices) (bs := η.vertices)
          (i := i) (Nat.lt_of_succ_lt hleft)
      have hget_succ :
          (γ.vertices ++ η.vertices)[i + 1] = γ.vertices[i + 1] := by
        exact List.getElem_append_left (as := γ.vertices) (bs := η.vertices)
          (i := i + 1) hleft
      simpa [hget_i, hget_succ] using hpi
    · by_cases hi_left_vertex : i < γ.vertices.length
      · have hbridge_index : i + 1 = γ.vertices.length := by
          omega
        have hlenγ_pos : 0 < γ.vertices.length :=
          List.length_pos_of_ne_nil γ.vertices_nonempty
        have hget_i :
            (γ.vertices ++ η.vertices)[i] = γ.target := by
          have hi_last : i = γ.vertices.length - 1 := by omega
          subst i
          have hlast :
              γ.vertices[γ.vertices.length - 1]'(Nat.sub_one_lt_of_lt hlenγ_pos) =
                γ.target := by
            have hsome := γ.target_eq_last
            rw [List.getLast?_eq_getLast_of_ne_nil γ.vertices_nonempty] at hsome
            simpa [List.getLast_eq_getElem] using Option.some.inj hsome
          have hleft_get :
              (γ.vertices ++ η.vertices)[γ.vertices.length - 1] =
                γ.vertices[γ.vertices.length - 1] := by
            exact List.getElem_append_left (as := γ.vertices) (bs := η.vertices)
              (i := γ.vertices.length - 1) (Nat.sub_one_lt_of_lt hlenγ_pos)
          simpa [hleft_get] using hlast
        have hget_succ :
            (γ.vertices ++ η.vertices)[i + 1] = η.source := by
          have hlenη_pos : 0 < η.vertices.length :=
            List.length_pos_of_ne_nil η.vertices_nonempty
          have hi_last : i = γ.vertices.length - 1 := by omega
          have hright_get :
              (γ.vertices ++ η.vertices)[γ.vertices.length] =
                η.vertices[0] := by
            simp
          have hhead :
              η.vertices[0]'hlenη_pos = η.source := by
            have hsome := η.source_eq_head
            rw [List.head?_eq_getElem?] at hsome
            rw [List.getElem?_eq_getElem hlenη_pos] at hsome
            exact Option.some.inj hsome
          subst i
          have hidx : γ.vertices.length - 1 + 1 = γ.vertices.length := by omega
          simpa [hidx, hright_get] using hhead
        have hp_eq_target : p = γ.target := by
          simpa [hget_i, hget_succ, hmatch] using hpi
        exact hγS (by simpa [hp_eq_target] using hγtarget)
      · apply hηS
        rw [η.carrier_eq]
        right
        let j : ℕ := i - γ.vertices.length
        have hi_ge : γ.vertices.length ≤ i := Nat.le_of_not_gt hi_left_vertex
        have hj_succ_lt : j + 1 < η.vertices.length := by
          dsimp [j]
          omega
        refine ⟨j, hj_succ_lt, ?_⟩
        have hget_i :
            (γ.vertices ++ η.vertices)[i] = η.vertices[j] := by
          dsimp [j]
          exact List.getElem_append_right (as := γ.vertices) (bs := η.vertices)
            (i := i) hi_ge
        have hget_succ :
            (γ.vertices ++ η.vertices)[i + 1] = η.vertices[j + 1] := by
          have hi_succ_ge : γ.vertices.length ≤ i + 1 := by omega
          dsimp [j]
          have hsub_succ : i + 1 - γ.vertices.length = i - γ.vertices.length + 1 := by
            omega
          simpa [hsub_succ] using
            (List.getElem_append_right (as := γ.vertices) (bs := η.vertices)
            (i := i + 1) hi_succ_ge
            )
        simpa [hget_i, hget_succ, j] using hpi
