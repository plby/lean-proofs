import ErdosProblems.Erdos733.ST.EndpointUnitDiskAlternatingVertexList

open Classical
noncomputable section

-- [TABLET NODE: EndpointUnitDiskAlternatingVertexListNodup]
lemma EndpointUnitDiskAlternatingVertexListNodup
    {β : Type*}
    (A B : EuclideanSpace ℝ (Fin 2))
    (items : List β)
    (block : β → List (EuclideanSpace ℝ (Fin 2)))
    (hAB : A ≠ B)
    (hblocks_nodup : ∀ x ∈ items, (block x).Nodup)
    (hblocks_pairwise : (items.map block).Pairwise List.Disjoint)
    (hA_blocks : ∀ x ∈ items, A ∉ block x)
    (hB_blocks : ∀ x ∈ items, B ∉ block x) :
    (EndpointUnitDiskAlternatingVertexList A B (items.map block)).Nodup := by
-- BODY
  have hflatten_nodup : ((items.map block).flatten).Nodup := by
    rw [List.nodup_flatten]
    constructor
    · intro l hl
      rcases List.mem_map.mp hl with ⟨x, hx, rfl⟩
      exact hblocks_nodup x hx
    · exact hblocks_pairwise
  have hA_not : A ∉ (items.map block).flatten := by
    intro h
    rcases List.mem_flatten.mp h with ⟨l, hl, hAl⟩
    rcases List.mem_map.mp hl with ⟨x, hx, rfl⟩
    exact hA_blocks x hx hAl
  have hB_not : B ∉ (items.map block).flatten := by
    intro h
    rcases List.mem_flatten.mp h with ⟨l, hl, hBl⟩
    rcases List.mem_map.mp hl with ⟨x, hx, rfl⟩
    exact hB_blocks x hx hBl
  have htail : ((items.map block).flatten ++ [B]).Nodup := by
    exact hflatten_nodup.append (List.nodup_singleton B) (by
      rw [List.disjoint_left]
      intro x hx hxB
      simp at hxB
      subst x
      exact hB_not hx)
  have hA_not_tail : A ∉ (items.map block).flatten ++ [B] := by
    intro h
    rcases List.mem_append.mp h with h | h
    · exact hA_not h
    · simp at h
      exact hAB h
  simpa [EndpointUnitDiskAlternatingVertexList] using htail.cons hA_not_tail
