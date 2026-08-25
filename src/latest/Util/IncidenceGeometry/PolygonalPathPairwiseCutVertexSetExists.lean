import Util.IncidenceGeometry.PolygonalPath

open Classical
noncomputable section

lemma PolygonalPathPairwiseCutVertexSetExists (γ : PolygonalPath) :
    ∃ V : Finset (EuclideanSpace ℝ (Fin 2)),
      (∀ v : EuclideanSpace ℝ (Fin 2), v ∈ γ.vertices → v ∈ V) ∧
        (∀ i j : ℕ,
          (hi : i + 1 < γ.vertices.length) →
            (hj : j + 1 < γ.vertices.length) →
              Set.Finite
                (segment ℝ γ.vertices[i] γ.vertices[i + 1] ∩
                  segment ℝ γ.vertices[j] γ.vertices[j + 1]) →
                ∀ p : EuclideanSpace ℝ (Fin 2),
                  p ∈ segment ℝ γ.vertices[i] γ.vertices[i + 1] →
                    p ∈ segment ℝ γ.vertices[j] γ.vertices[j + 1] →
                      p ∈ V) ∧
          (∀ i j : ℕ,
            (hi : i + 1 < γ.vertices.length) →
              (hj : j + 1 < γ.vertices.length) →
                ¬ Set.Finite
                  (segment ℝ γ.vertices[i] γ.vertices[i + 1] ∩
                    segment ℝ γ.vertices[j] γ.vertices[j + 1]) →
                  γ.vertices[i] ∈ V ∧
                    γ.vertices[i + 1] ∈ V ∧
                      γ.vertices[j] ∈ V ∧ γ.vertices[j + 1] ∈ V) := by
  classical
  let E := EuclideanSpace ℝ (Fin 2)
  let I : Finset (Fin (γ.vertices.length - 1)) := Finset.univ
  let A : Fin (γ.vertices.length - 1) → E := fun k =>
    γ.vertices[k.1]'(by omega)
  let B : Fin (γ.vertices.length - 1) → E := fun k =>
    γ.vertices[k.1 + 1]'(by omega)
  let pairIntersection : Fin (γ.vertices.length - 1) → Fin (γ.vertices.length - 1) → Set E :=
    fun k l => segment ℝ (A k) (B k) ∩ segment ℝ (A l) (B l)
  let pairCuts : Fin (γ.vertices.length - 1) → Fin (γ.vertices.length - 1) → Finset E :=
    fun k l =>
      if hfin : Set.Finite (pairIntersection k l) then
        hfin.toFinset
      else
        ({A k, B k, A l, B l} : Finset E)
  let V : Finset E :=
    γ.vertices.toFinset ∪ I.biUnion (fun k => I.biUnion fun l => pairCuts k l)
  have hV_original :
      ∀ v : E, v ∈ γ.vertices → v ∈ V := by
    intro v hv
    exact Finset.mem_union.mpr (Or.inl (by simpa using hv))
  refine ⟨V, hV_original, ?_, ?_⟩
  · intro i j hi hj hfin p hpi hpj
    let k : Fin (γ.vertices.length - 1) := ⟨i, by omega⟩
    let l : Fin (γ.vertices.length - 1) := ⟨j, by omega⟩
    have hfin_pair : Set.Finite (pairIntersection k l) := by
      simpa [pairIntersection, A, B, k, l] using hfin
    have hp_pair : p ∈ pairIntersection k l := by
      simpa [pairIntersection, A, B, k, l] using And.intro hpi hpj
    have hp_cut : p ∈ pairCuts k l := by
      dsimp [pairCuts]
      rw [dif_pos hfin_pair]
      exact (Set.Finite.mem_toFinset hfin_pair).2 hp_pair
    exact Finset.mem_union.mpr (Or.inr (by
      refine Finset.mem_biUnion.mpr ⟨k, by simp [I], ?_⟩
      exact Finset.mem_biUnion.mpr ⟨l, by simp [I], hp_cut⟩))
  · intro i j hi hj _hnot
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact hV_original γ.vertices[i]
        (List.getElem_mem (l := γ.vertices) (n := i) (Nat.lt_of_succ_lt hi))
    · exact hV_original γ.vertices[i + 1]
        (List.getElem_mem (l := γ.vertices) (n := i + 1) hi)
    · exact hV_original γ.vertices[j]
        (List.getElem_mem (l := γ.vertices) (n := j) (Nat.lt_of_succ_lt hj))
    · exact hV_original γ.vertices[j + 1]
        (List.getElem_mem (l := γ.vertices) (n := j + 1) hj)

