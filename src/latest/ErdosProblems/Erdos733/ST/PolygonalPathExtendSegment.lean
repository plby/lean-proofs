import ErdosProblems.Erdos733.ST.PolygonalPath

open Classical
noncomputable section

-- [TABLET NODE: PolygonalPathExtendSegment]
lemma PolygonalPathExtendSegment
    (S : Set (EuclideanSpace ℝ (Fin 2))) (γ : PolygonalPath)
    (z : EuclideanSpace ℝ (Fin 2)) :
    γ.carrier ⊆ S →
      segment ℝ γ.target z ⊆ S →
        ∃ η : PolygonalPath,
          η.source = γ.source ∧
            η.target = z ∧
              η.carrier ⊆ S := by
-- BODY
  intro hγ hseg
  have source_mem : γ.source ∈ γ.carrier := by
    rw [γ.carrier_eq]
    left
    exact Or.inl rfl
  have target_mem : γ.target ∈ γ.carrier := by
    rw [γ.carrier_eq]
    left
    exact Or.inr rfl
  let η : PolygonalPath :=
    { vertices := γ.vertices ++ [z]
      vertices_nonempty := by simp [γ.vertices_nonempty]
      source := γ.source
      target := z
      source_eq_head := by
        rw [List.head?_append_of_ne_nil _ γ.vertices_nonempty]
        exact γ.source_eq_head
      target_eq_last := by simp
      carrier :=
        ({γ.source, z} : Set (EuclideanSpace ℝ (Fin 2))) ∪
          {p | ∃ i : ℕ,
            ∃ hi : i + 1 < (γ.vertices ++ [z]).length,
              p ∈ segment ℝ
                (γ.vertices ++ [z])[i]
                (γ.vertices ++ [z])[i + 1]}
      carrier_eq := rfl }
  refine ⟨η, rfl, rfl, ?_⟩
  intro p hp
  change p ∈
      (({γ.source, z} : Set (EuclideanSpace ℝ (Fin 2))) ∪
        {p | ∃ i : ℕ,
          ∃ hi : i + 1 < (γ.vertices ++ [z]).length,
            p ∈ segment ℝ
              (γ.vertices ++ [z])[i]
              (γ.vertices ++ [z])[i + 1]}) at hp
  rcases hp with hp_end | hp_seg
  · rcases hp_end with hps | hpz
    · cases hps
      exact hγ source_mem
    · cases hpz
      exact hseg (right_mem_segment ℝ γ.target z)
  · rcases hp_seg with ⟨i, hi, hpi⟩
    have hi_bound : i + 1 < γ.vertices.length + 1 := by simpa using hi
    have hile : i + 1 ≤ γ.vertices.length := Nat.lt_succ_iff.mp hi_bound
    rcases lt_or_eq_of_le hile with hlt | heq
    · apply hγ
      rw [γ.carrier_eq]
      right
      refine ⟨i, hlt, ?_⟩
      have hleft :
          (γ.vertices ++ [z])[i] = γ.vertices[i] := by
        exact List.getElem_append_left (as := γ.vertices) (bs := [z])
          (i := i) (Nat.lt_of_succ_lt hlt)
      have hright :
          (γ.vertices ++ [z])[i + 1] = γ.vertices[i + 1] := by
        exact List.getElem_append_left (as := γ.vertices) (bs := [z])
          (i := i + 1) hlt
      simpa [hleft, hright] using hpi
    · apply hseg
      have hi_last : i = γ.vertices.length - 1 := by omega
      have hlen_pos : 0 < γ.vertices.length :=
        List.length_pos_of_ne_nil γ.vertices_nonempty
      have hlast_get :
          (γ.vertices ++ [z])[i] = γ.target := by
        subst i
        have hlast :
            γ.vertices[γ.vertices.length - 1]'(Nat.sub_one_lt_of_lt hlen_pos) =
              γ.target := by
          have hgetlast :
              γ.vertices.getLast γ.vertices_nonempty = γ.target := by
            have hsome := γ.target_eq_last
            rw [List.getLast?_eq_getLast_of_ne_nil γ.vertices_nonempty] at hsome
            exact Option.some.inj hsome
          simpa [List.getLast_eq_getElem] using hgetlast
        have hleft :
            (γ.vertices ++ [z])[γ.vertices.length - 1] =
              γ.vertices[γ.vertices.length - 1] := by
          exact List.getElem_append_left (as := γ.vertices) (bs := [z])
            (i := γ.vertices.length - 1) (Nat.sub_one_lt_of_lt hlen_pos)
        simpa [hleft] using hlast
      have hnext_get :
          (γ.vertices ++ [z])[i + 1] = z := by
        subst i
        have hone_le : 1 ≤ γ.vertices.length := Nat.succ_le_iff.mpr hlen_pos
        have hright :
            (γ.vertices ++ [z])[γ.vertices.length] =
              [z][γ.vertices.length - γ.vertices.length] := by
          exact List.getElem_append_right (as := γ.vertices) (bs := [z])
            (i := γ.vertices.length) (Nat.le_refl γ.vertices.length)
        simpa [Nat.sub_add_cancel hone_le] using hright
      simpa [hlast_get, hnext_get] using hpi
