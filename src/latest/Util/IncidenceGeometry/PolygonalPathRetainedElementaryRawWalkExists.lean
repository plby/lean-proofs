import Util.IncidenceGeometry.FiniteSortedRealCutListEndpointEntries
import Util.IncidenceGeometry.PolygonalPathRetainedElementaryEdges
import Mathlib.Data.List.Chain
import Mathlib.Tactic

open Classical
noncomputable section

lemma PolygonalPathRetainedElementaryRawWalkExists
    (γ : PolygonalPath)
    (cutVertices : Finset (EuclideanSpace ℝ (Fin 2)))
    (hcut_original :
      ∀ v : EuclideanSpace ℝ (Fin 2), v ∈ γ.vertices → v ∈ cutVertices)
    (retainedEdgesData : PolygonalPathRetainedElementaryEdges γ cutVertices) :
    ∃ rawWalk : List (EuclideanSpace ℝ (Fin 2)),
      rawWalk.head? = some γ.source ∧
        rawWalk.getLast? = some γ.target ∧
          (γ.source ≠ γ.target → 2 ≤ rawWalk.length) ∧
            (∀ v : EuclideanSpace ℝ (Fin 2), v ∈ rawWalk → v ∈ cutVertices) ∧
              ∀ i : ℕ, (hi : i + 1 < rawWalk.length) →
                (rawWalk[i], rawWalk[i + 1]) ∈ retainedEdgesData.retainedEdges ∨
                  (rawWalk[i + 1], rawWalk[i]) ∈ retainedEdgesData.retainedEdges := by
  classical
  let P := EuclideanSpace ℝ (Fin 2)
  let A : Fin (γ.vertices.length - 1) → P := fun i =>
    γ.vertices[i.1]'(by omega)
  let B : Fin (γ.vertices.length - 1) → P := fun i =>
    γ.vertices[i.1 + 1]'(by omega)
  let G : SimpleGraph P :=
    { Adj := fun a b =>
        a ≠ b ∧ ((a, b) ∈ retainedEdgesData.retainedEdges ∨
          (b, a) ∈ retainedEdgesData.retainedEdges)
      symm := by
        constructor
        intro a b h
        constructor
        · exact h.1.symm
        · rcases h.2 with hab | hba
          · exact Or.inr hab
          · exact Or.inl hba
      loopless := by
        constructor
        intro a h
        exact h.1 rfl }
  have represented_adj :
      ∀ (i : Fin (γ.vertices.length - 1)) (hseg : A i ≠ B i)
        (k : ℕ) (hk : k + 1 < (retainedEdgesData.subdivisionList i).length),
          let a :=
            AffineMap.lineMap (A i) (B i)
              ((retainedEdgesData.subdivisionList i)[k]'(Nat.lt_of_succ_lt hk))
          let b :=
            AffineMap.lineMap (A i) (B i)
              ((retainedEdgesData.subdivisionList i)[k + 1]'hk)
          G.Adj a b := by
    intro i hseg k hk
    dsimp only
    constructor
    · simpa [A, B] using
        retainedEdgesData.elementary_nondegenerate i
          (by simpa [A, B] using hseg) k hk
    · rcases retainedEdgesData.represented_exactly_one i
        (by simpa [A, B] using hseg) k hk with hdir | hrev
      · exact Or.inl (by simpa [A, B] using hdir.1)
      · exact Or.inr (by simpa [A, B] using hrev.1)
  have segment_reachable :
      ∀ i : Fin (γ.vertices.length - 1),
        Relation.ReflTransGen G.Adj (A i) (B i) := by
    intro i
    by_cases hseg : A i ≠ B i
    · let L : List ℝ := retainedEdgesData.subdivisionList i
      let points : List P := L.map (AffineMap.lineMap (A i) (B i))
      have hseg' :
          γ.vertices[i.1]'(by omega) ≠ γ.vertices[i.1 + 1]'(by omega) := by
        simpa [A, B] using hseg
      have hentries :
          2 ≤ L.length ∧
            (∀ h : 0 < L.length, L[0]'h = 0) ∧
              (∀ h : L.length - 1 < L.length,
                L[L.length - 1]'h = 1) :=
        FiniteSortedRealCutListEndpointEntries L
          (retainedEdgesData.subdivision_sorted i hseg')
          (retainedEdgesData.subdivision_zero i hseg')
          (retainedEdgesData.subdivision_one i hseg')
          (retainedEdgesData.subdivision_bounds i hseg')
      have hpoints_ne : points ≠ [] := by
        intro hnil
        have hlen_points : points.length = 0 := by simp [hnil]
        have hlen_L : L.length = 0 := by simpa [points] using hlen_points
        omega
      have hpoints_chain : points.IsChain G.Adj := by
        rw [List.isChain_iff_getElem]
        intro k hk
        have hkL : k + 1 < L.length := by
          simpa [points] using hk
        have hadj := represented_adj i hseg k hkL
        simpa [points, L] using hadj
      have hpoints_head : points.head hpoints_ne = A i := by
        have hLpos : 0 < L.length := by omega
        have hzero : L[0]'hLpos = 0 := hentries.2.1 hLpos
        rw [List.head_eq_getElem]
        simp [points, L, hzero]
      have hpoints_last : points.getLast hpoints_ne = B i := by
        have hLlast : L.length - 1 < L.length := by omega
        have hone : L[L.length - 1]'hLlast = 1 := hentries.2.2 hLlast
        rw [List.getLast_eq_getElem]
        simp [points, L, hone]
      have hrt_points :
          Relation.ReflTransGen G.Adj (points.head hpoints_ne)
            (points.getLast hpoints_ne) :=
        List.relationReflTransGen_of_exists_isChain points hpoints_chain hpoints_ne
      simpa [hpoints_head, hpoints_last] using hrt_points
    · have hEq : A i = B i := not_not.mp hseg
      simpa [hEq] using
        (Relation.ReflTransGen.refl : Relation.ReflTransGen G.Adj (A i) (A i))
  have hvertices_chain :
      γ.vertices.IsChain (Relation.ReflTransGen G.Adj) := by
    rw [List.isChain_iff_getElem]
    intro i hi
    simpa [A, B] using segment_reachable ⟨i, by omega⟩
  have hvertices_rt0 :
      Relation.ReflTransGen (Relation.ReflTransGen G.Adj)
        (γ.vertices.head γ.vertices_nonempty)
        (γ.vertices.getLast γ.vertices_nonempty) :=
    List.relationReflTransGen_of_exists_isChain
      γ.vertices hvertices_chain γ.vertices_nonempty
  have hvertices_head : γ.vertices.head γ.vertices_nonempty = γ.source := by
    simpa [List.head?_eq_some_head γ.vertices_nonempty] using γ.source_eq_head
  have hvertices_last : γ.vertices.getLast γ.vertices_nonempty = γ.target := by
    simpa [List.getLast?_eq_getLast_of_ne_nil γ.vertices_nonempty] using γ.target_eq_last
  have hsource_target_rt0 :
      Relation.ReflTransGen (Relation.ReflTransGen G.Adj) γ.source γ.target := by
    simpa [hvertices_head, hvertices_last] using hvertices_rt0
  have hsource_target_rt :
      Relation.ReflTransGen G.Adj γ.source γ.target := by
    simpa [Relation.reflTransGen_eq_self] using hsource_target_rt0
  rcases List.exists_isChain_ne_nil_of_relationReflTransGen hsource_target_rt with
    ⟨rawWalk, hraw_ne, hraw_chain, hraw_head, hraw_last⟩
  have hsource_mem_vertices : γ.source ∈ γ.vertices := by
    cases hverts : γ.vertices with
    | nil => exact False.elim (γ.vertices_nonempty hverts)
    | cons x xs =>
        have hx : x = γ.source := by
          simpa [hverts] using γ.source_eq_head
        simp [hx]
  have hsource_cut : γ.source ∈ cutVertices :=
    hcut_original γ.source hsource_mem_vertices
  have adj_preserves_cut :
      ∀ {x y : P}, G.Adj x y → x ∈ cutVertices → y ∈ cutVertices := by
    intro x y hxy _hx
    rcases hxy.2 with hxy_edge | hyx_edge
    · exact (retainedEdgesData.retained_edge_data (x, y) hxy_edge).2.1
    · exact (retainedEdgesData.retained_edge_data (y, x) hyx_edge).1
  refine ⟨rawWalk, ?_, ?_, ?_, ?_, ?_⟩
  · rw [List.head?_eq_some_head hraw_ne, hraw_head]
  · rw [List.getLast?_eq_getLast_of_ne_nil hraw_ne, hraw_last]
  · intro hst
    cases rawWalk with
    | nil => exact False.elim (hraw_ne rfl)
    | cons x xs =>
        cases xs with
        | nil =>
            have hx_source : x = γ.source := by simpa using hraw_head
            have hx_target : x = γ.target := by simpa using hraw_last
            exact False.elim (hst (hx_source.symm.trans hx_target))
        | cons y ys =>
            simp
  · intro v hv
    exact List.IsChain.induction (p := fun z : P => z ∈ cutVertices)
      rawWalk hraw_chain
      (by
        intro x y hxy hx
        exact adj_preserves_cut hxy hx)
      (by
        intro hne
        simpa [hraw_head] using hsource_cut)
      v hv
  · intro i hi
    exact (List.isChain_iff_getElem.mp hraw_chain i hi).2
