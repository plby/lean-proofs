import ErdosProblems.Erdos733.ST.FiniteWalkCycleErasure
import ErdosProblems.Erdos733.ST.PolygonalPathRawStraightLineComplex
import ErdosProblems.Erdos733.ST.PolygonalPathStraightLineComplex

open Classical
noncomputable section

-- [TABLET NODE: PolygonalPathStraightLineComplexOfRaw]
lemma PolygonalPathStraightLineComplexOfRaw
    (γ : PolygonalPath) (R : PolygonalPathRawStraightLineComplex γ) :
    γ.source ≠ γ.target →
      Nonempty (PolygonalPathStraightLineComplex γ) := by
-- BODY
  intro hst
  let P := EuclideanSpace ℝ (Fin 2)
  let G : SimpleGraph P :=
    { Adj := fun a b => a ≠ b ∧ ((a, b) ∈ R.edges ∨ (b, a) ∈ R.edges)
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
  have hraw_len : 2 ≤ R.rawWalk.length := R.rawWalk_length_ge_two hst
  have hraw_ne : R.rawWalk ≠ [] := by
    intro hnil
    have : R.rawWalk.length = 0 := by simp [hnil]
    omega
  have hraw_head : R.rawWalk.head hraw_ne = γ.source := by
    simpa [List.head?_eq_some_head hraw_ne] using R.rawWalk_head
  have hraw_last : R.rawWalk.getLast hraw_ne = γ.target := by
    simpa [List.getLast?_eq_getLast_of_ne_nil hraw_ne] using R.rawWalk_last
  have hraw_chain : R.rawWalk.IsChain G.Adj := by
    rw [List.isChain_iff_getElem]
    intro i hi
    have hstep := R.rawWalk_steps i hi
    change R.rawWalk[i] ≠ R.rawWalk[i + 1] ∧
      ((R.rawWalk[i], R.rawWalk[i + 1]) ∈ R.edges ∨
        (R.rawWalk[i + 1], R.rawWalk[i]) ∈ R.edges)
    constructor
    · rcases hstep with hstep | hstep
      · exact R.edge_nondegenerate _ hstep
      · exact (R.edge_nondegenerate _ hstep).symm
    · exact hstep
  let p0 : G.Walk (R.rawWalk.head hraw_ne) (R.rawWalk.getLast hraw_ne) :=
    SimpleGraph.Walk.ofSupport R.rawWalk hraw_ne hraw_chain
  let p : G.Walk γ.source γ.target := p0.copy hraw_head hraw_last
  obtain ⟨q, _hq_path, hq_nodup, hq_head, hq_last, hq_len,
      hq_support_subset, _hq_edges_subset⟩ :=
    FiniteWalkCycleErasure G p hst
  have hsupport_raw : q.support ⊆ R.rawWalk := by
    intro v hv
    have hvp := hq_support_subset hv
    simpa [p, p0, SimpleGraph.Walk.support_ofSupport] using hvp
  let retainedEdges : Finset (P × P) :=
    Finset.univ.image fun i : Fin (q.support.length - 1) =>
      (q.support[i.1]'(by omega), q.support[i.1 + 1]'(by omega))
  have retained_adj :
      ∀ e : P × P, e ∈ retainedEdges → G.Adj e.1 e.2 := by
    intro e he
    rcases Finset.mem_image.mp he with ⟨i, _hi, rfl⟩
    have hi : i.1 + 1 < q.support.length := by omega
    exact (List.isChain_iff_getElem.mp (SimpleGraph.Walk.isChain_adj_support q)) i.1 hi
  have retained_vertices :
      ∀ e : P × P, e ∈ retainedEdges → e.1 ∈ R.vertices ∧ e.2 ∈ R.vertices := by
    intro e he
    rcases Finset.mem_image.mp he with ⟨i, _hi, rfl⟩
    constructor
    · exact R.rawWalk_vertices_mem _ (hsupport_raw (List.getElem_mem (by omega)))
    · exact R.rawWalk_vertices_mem _ (hsupport_raw (List.getElem_mem (by omega)))
  have raw_edge_data :
      ∀ e : P × P, e ∈ retainedEdges →
        ∃ er : P × P, er ∈ R.edges ∧
          segment ℝ er.1 er.2 = segment ℝ e.1 e.2 ∧
            openSegment ℝ er.1 er.2 = openSegment ℝ e.1 e.2 ∧
              ({er.1, er.2} : Set P) = ({e.1, e.2} : Set P) ∧
                s(er.1, er.2) = s(e.1, e.2) := by
    intro e he
    have hadj := retained_adj e he
    rcases hadj.2 with hraw | hraw
    · exact ⟨e, hraw, rfl, rfl, rfl, rfl⟩
    · refine ⟨(e.2, e.1), hraw, ?_, ?_, ?_, ?_⟩
      · simpa using segment_symm ℝ e.2 e.1
      · simpa using openSegment_symm ℝ e.2 e.1
      · exact Set.pair_comm e.2 e.1
      · exact Sym2.eq_swap
  have retained_sym2_injective :
      ∀ {e f : P × P}, e ∈ retainedEdges → f ∈ retainedEdges →
        s(e.1, e.2) = s(f.1, f.2) → e = f := by
    intro e f he hf hsym
    rcases Finset.mem_image.mp he with ⟨i, _hi, rfl⟩
    rcases Finset.mem_image.mp hf with ⟨j, _hj, rfl⟩
    have hrel := (Sym2.eq.mp hsym)
    rw [Sym2.rel_iff'] at hrel
    rcases hrel with hp | hp
    · exact hp
    · have hfirst :
          q.support[i.1]'(by omega) = q.support[j.1 + 1]'(by omega) :=
        congrArg Prod.fst hp
      have hsecond :
          q.support[i.1 + 1]'(by omega) = q.support[j.1]'(by omega) :=
        congrArg Prod.snd hp
      have hij1 : i.1 = j.1 + 1 :=
        (List.Nodup.getElem_inj_iff hq_nodup).mp hfirst
      have hi1j : i.1 + 1 = j.1 :=
        (List.Nodup.getElem_inj_iff hq_nodup).mp hsecond
      omega
  have raw_distinct_of_retained :
      ∀ {e f er fr : P × P}, e ∈ retainedEdges → f ∈ retainedEdges → e ≠ f →
        s(er.1, er.2) = s(e.1, e.2) →
          s(fr.1, fr.2) = s(f.1, f.2) → er ≠ fr := by
    intro e f er fr he hf hef her hfr herfr
    apply hef
    apply retained_sym2_injective he hf
    calc
      s(e.1, e.2) = s(er.1, er.2) := her.symm
      _ = s(fr.1, fr.2) := by rw [herfr]
      _ = s(f.1, f.2) := hfr
  refine ⟨
    { vertices := R.vertices
      edges := retainedEdges
      source_mem := R.source_mem
      target_mem := R.target_mem
      edge_source_mem := by
        intro e he
        exact (retained_vertices e he).1
      edge_target_mem := by
        intro e he
        exact (retained_vertices e he).2
      edge_nondegenerate := by
        intro e he
        exact (retained_adj e he).1
      edge_refines_path_segment := by
        intro e he
        rcases raw_edge_data e he with ⟨er, her, hseg, _hopen, _hset, _hsym⟩
        rcases R.edge_refines_path_segment er her with ⟨i, hi, hrefines⟩
        exact ⟨i, hi, by simpa [hseg] using hrefines⟩
      edge_subset_carrier := by
        intro e he x hx
        rcases raw_edge_data e he with ⟨er, her, hseg, _hopen, _hset, _hsym⟩
        exact R.edge_subset_carrier er her (by simpa [hseg] using hx)
      no_vertex_in_edge_interior := by
        intro e he v hv hvopen
        rcases raw_edge_data e he with ⟨er, her, _hseg, hopen, _hset, _hsym⟩
        exact R.no_vertex_in_edge_interior er her v hv (by simpa [hopen] using hvopen)
      distinct_edges_meet_at_common_endpoints := by
        intro e f he hf hne
        rcases raw_edge_data e he with ⟨er, her, hseg_e, _hopen_e, hset_e, hsym_e⟩
        rcases raw_edge_data f hf with ⟨fr, hfr, hseg_f, _hopen_f, hset_f, hsym_f⟩
        have hraw_ne : er ≠ fr :=
          raw_distinct_of_retained he hf hne hsym_e hsym_f
        have hR := R.distinct_edges_meet_at_common_endpoints er fr her hfr hraw_ne
        calc
          segment ℝ e.1 e.2 ∩ segment ℝ f.1 f.2
              = segment ℝ er.1 er.2 ∩ segment ℝ fr.1 fr.2 := by
                rw [← hseg_e, ← hseg_f]
          _ = ({er.1, er.2} : Set P) ∩ ({fr.1, fr.2} : Set P) := hR
          _ = ({e.1, e.2} : Set P) ∩ ({f.1, f.2} : Set P) := by
                rw [hset_e, hset_f]
      walk := q.support
      walk_nodup := hq_nodup
      walk_head := hq_head
      walk_last := hq_last
      walk_length_ge_two := hq_len
      walk_vertices_mem := by
        intro v hv
        exact R.rawWalk_vertices_mem v (hsupport_raw hv)
      walk_steps := by
        intro i hi
        change (q.support[i], q.support[i + 1]) ∈ retainedEdges
        refine Finset.mem_image.mpr ⟨⟨i, by omega⟩, by simp, ?_⟩
        rfl }⟩
