import ErdosProblems.Erdos733.ST.OrdinaryDrawingImage
import ErdosProblems.Erdos733.ST.PlaneFaceData
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.Tactic

open Classical
noncomputable section

-- [TABLET NODE: DeleteNonbridgePathArcList]
lemma DeleteNonbridgePathArcList {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] [DecidableRel G.Adj] (D : OrdinaryPolygonalDrawing G)
    (A : PlaneFaceData G D) (d : G.Dart)
    (p : (G.deleteEdges {s(d.snd, d.fst)}).Walk d.snd d.fst) (hp : p.IsPath) :
    ∃ q : G.Walk d.snd d.fst,
      q = p.mapLe (G.deleteEdges_le {s(d.snd, d.fst)}) ∧
        q.IsPath ∧
          ∃ hq_nonempty : ¬ q.Nil,
            ∃ arcs : List PolygonalArc,
              arcs = (A.dartArc d) :: q.darts.map A.dartArc ∧
                (A.dartArc d) ∈ arcs ∧
                  arcs.head? = some (A.dartArc d) ∧
                    (∀ γ ∈ arcs, γ.carrier ⊆ OrdinaryDrawingImage G D) ∧
                      arcs.IsChain (fun γ δ => γ.target = δ.source) ∧
                        (A.dartArc d).target =
                            (A.dartArc (q.firstDart hq_nonempty)).source ∧
                          (A.dartArc (q.lastDart hq_nonempty)).target =
                            (A.dartArc d).source ∧
                            arcs.Nodup ∧
                              2 ≤ q.darts.length ∧
                                3 ≤ arcs.length ∧
                                  (A.dartArc d) ∉ q.darts.map A.dartArc ∧
                                    (∀ γ : PolygonalArc, γ ∈ arcs →
                                      γ.target = (arcs.formPerm γ).source) := by
-- BODY
  classical
  let q : G.Walk d.snd d.fst := p.mapLe (G.deleteEdges_le {s(d.snd, d.fst)})
  have hq_path : q.IsPath := by
    dsimp [q]
    exact hp.mapLe (G.deleteEdges_le {s(d.snd, d.fst)})
  have hq_nonempty : ¬ q.Nil := SimpleGraph.Walk.not_nil_of_ne d.snd_ne_fst
  let arcs : List PolygonalArc := (A.dartArc d) :: q.darts.map A.dartArc
  have hdartArc_injective : Function.Injective A.dartArc := by
    intro d₁ d₂ h
    apply SimpleGraph.Dart.ext
    apply Prod.ext
    · apply D.vertexPlacement_injective
      have hsource := congrArg PolygonalArc.source h
      simpa [A.dartArc_source d₁, A.dartArc_source d₂] using hsource
    · apply D.vertexPlacement_injective
      have htarget := congrArg PolygonalArc.target h
      simpa [A.dartArc_target d₁, A.dartArc_target d₂] using htarget
  have hp_deleted_edge_not_mem : s(d.snd, d.fst) ∉ p.edges := by
    intro hmem
    have hEdgeSet :
        s(d.snd, d.fst) ∈ (G.deleteEdges {s(d.snd, d.fst)}).edgeSet :=
      SimpleGraph.Walk.edges_subset_edgeSet p hmem
    rw [SimpleGraph.edgeSet_deleteEdges] at hEdgeSet
    exact hEdgeSet.2 (by simp)
  have hq_edges_eq : q.edges = p.edges := by
    dsimp [q]
    exact p.edges_mapLe_eq_edges (G.deleteEdges_le {s(d.snd, d.fst)})
  have hq_deleted_edge_not_mem : s(d.snd, d.fst) ∉ q.edges := by
    intro hmem
    exact hp_deleted_edge_not_mem (by simpa [hq_edges_eq] using hmem)
  have hd_edge_eq : d.edge = s(d.snd, d.fst) := by
    simp [SimpleGraph.Dart.edge]
  have hd_not_mem_path_arcs : (A.dartArc d) ∉ q.darts.map A.dartArc := by
    intro hmem
    rcases List.mem_map.mp hmem with ⟨d', hd'_mem, hd'_eq⟩
    have hd'_eq_d : d' = d := hdartArc_injective hd'_eq
    subst d'
    have hd_edge_mem : d.edge ∈ q.edges := by
      exact List.mem_map.mpr ⟨d, hd'_mem, rfl⟩
    exact hq_deleted_edge_not_mem (by simpa [hd_edge_eq] using hd_edge_mem)
  have hpath_arcs_nodup : (q.darts.map A.dartArc).Nodup := by
    exact (SimpleGraph.Walk.darts_nodup_of_support_nodup hq_path.support_nodup).map
      hdartArc_injective
  have harcs_nodup : arcs.Nodup := by
    simp [arcs, hd_not_mem_path_arcs, hpath_arcs_nodup]
  have hp_length_two : 2 ≤ p.length := by
    by_contra hlt
    have hp_lt_two : p.length < 2 := Nat.lt_of_not_ge hlt
    have hp_cases : p.length = 0 ∨ p.length = 1 := by omega
    rcases hp_cases with hp_zero | hp_one
    · exact d.snd_ne_fst (SimpleGraph.Walk.eq_of_length_eq_zero (p := p) hp_zero)
    · have hAdj : (G.deleteEdges {s(d.snd, d.fst)}).Adj d.snd d.fst :=
        SimpleGraph.Walk.adj_of_length_eq_one (p := p) hp_one
      have hAdj' :=
        (SimpleGraph.deleteEdges_adj (G := G)
          (s := ({s(d.snd, d.fst)} : Set (Sym2 V)))
          (v := d.snd) (w := d.fst)).mp hAdj
      exact hAdj'.2 (by simp)
  have hq_darts_length_two : 2 ≤ q.darts.length := by
    have hq_length_two : 2 ≤ q.length := by
      have hq_length_eq : q.length = p.length := by
        dsimp [q, SimpleGraph.Walk.mapLe]
        exact SimpleGraph.Walk.length_map
          (SimpleGraph.Hom.ofLE (G.deleteEdges_le {s(d.snd, d.fst)})) p
      simpa [hq_length_eq] using hp_length_two
    rw [SimpleGraph.Walk.length_darts]
    exact hq_length_two
  have harcs_length_three : 3 ≤ arcs.length := by
    simpa [arcs] using Nat.succ_le_succ hq_darts_length_two
  have hchain_arcs_local : arcs.IsChain (fun γ δ => γ.target = δ.source) := by
    have hchainDarts : q.darts.IsChain G.DartAdj :=
      SimpleGraph.Walk.isChain_dartAdj_darts q
    have hchainPath : (q.darts.map A.dartArc).IsChain
        (fun γ δ : PolygonalArc => γ.target = δ.source) := by
      exact List.isChain_map_of_isChain (f := A.dartArc)
        (fun d₁ d₂ hd => by
          rw [A.dartArc_target d₁, A.dartArc_source d₂]
          exact congrArg D.vertexPlacement hd)
        hchainDarts
    have hfirst : ∀ y ∈ (q.darts.map A.dartArc).head?,
        (A.dartArc d).target = y.source := by
      intro y hy
      have hdarts_ne : q.darts ≠ [] := SimpleGraph.Walk.darts_eq_nil.not.mpr hq_nonempty
      have hhead : (q.darts.map A.dartArc).head? =
          some (A.dartArc (q.firstDart hq_nonempty)) := by
        rw [List.head?_eq_some_head]
        · rw [List.head_map]
          rw [q.firstDart_eq_head_darts hq_nonempty]
        · simpa using hdarts_ne
      rw [hhead] at hy
      simp only [Option.mem_def, Option.some.injEq] at hy
      subst y
      rw [A.dartArc_target d, A.dartArc_source (q.firstDart hq_nonempty)]
      rfl
    exact (List.isChain_cons).mpr ⟨hfirst, hchainPath⟩
  have hlast_attach_local :
      (A.dartArc (q.lastDart hq_nonempty)).target = (A.dartArc d).source := by
    rw [A.dartArc_target (q.lastDart hq_nonempty), A.dartArc_source d]
    rfl
  have hform_endpoint :
      ∀ γ : PolygonalArc, γ ∈ arcs → γ.target = (arcs.formPerm γ).source := by
    intro γ hγ
    rw [List.formPerm_apply_mem_eq_next harcs_nodup γ hγ]
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hγ
    by_cases hnext : i + 1 < arcs.length
    · have hchain_get :=
        (List.isChain_iff_getElem.mp hchain_arcs_local i hnext)
      have hnext_eq :
          arcs.next arcs[i] (List.getElem_mem hi) = arcs[i + 1] := by
        simpa [Nat.mod_eq_of_lt hnext] using
          (List.next_getElem arcs harcs_nodup i hi)
      simpa [hnext_eq] using hchain_get
    · have hi_last : i = arcs.length - 1 := by omega
      have hnext_eq :
          arcs.next arcs[i] (List.getElem_mem hi) = arcs.head (List.ne_nil_of_mem (List.getElem_mem hi)) := by
        rw [List.next_getElem arcs harcs_nodup i hi]
        have hmod : (i + 1) % arcs.length = 0 := by
          rw [hi_last]
          have hlen_pos : 0 < arcs.length := lt_of_le_of_lt (Nat.zero_le i) hi
          rw [Nat.sub_add_cancel hlen_pos, Nat.mod_self]
        simp [hmod, List.head_eq_getElem_zero]
      have hγ_last : arcs[i] = A.dartArc (q.lastDart hq_nonempty) := by
        have hmap_ne : q.darts.map A.dartArc ≠ [] := by
          exact List.ne_nil_of_length_pos (by
            have hpos : 0 < (q.darts.map A.dartArc).length := by
              simpa using Nat.lt_of_lt_of_le (by decide : 0 < 2) hq_darts_length_two
            simpa using hpos)
        have harcs_last :
            arcs.getLast (List.ne_nil_of_mem (List.getElem_mem hi)) =
              A.dartArc (q.lastDart hq_nonempty) := by
          simp [arcs, List.getLast_cons, hmap_ne]
        have hidx_last :
            arcs[i] = arcs.getLast (List.ne_nil_of_mem (List.getElem_mem hi)) := by
          rw [List.getLast_eq_getElem]
          congr
        exact hidx_last.trans harcs_last
      have hhead_eq :
          arcs.head (List.ne_nil_of_mem (List.getElem_mem hi)) = A.dartArc d := by
        simp [arcs]
      simpa [hnext_eq, hhead_eq] using (by
        simpa [hγ_last] using hlast_attach_local)
  refine ⟨q, rfl, hq_path, hq_nonempty, arcs, rfl, by simp [arcs], by simp [arcs], ?_,
    hchain_arcs_local, ?_, hlast_attach_local, harcs_nodup, hq_darts_length_two,
    harcs_length_three, hd_not_mem_path_arcs, hform_endpoint⟩
  · intro γ hγ x hx
    simp [arcs] at hγ
    rcases hγ with hγ | ⟨d', _hd', hγ⟩
    · subst γ
      rw [A.dartArc_carrier d] at hx
      rw [OrdinaryDrawingImage]
      exact Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨A.dartEdge d, hx⟩)
    · subst γ
      rw [A.dartArc_carrier d'] at hx
      rw [OrdinaryDrawingImage]
      exact Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨A.dartEdge d', hx⟩)
  · rw [A.dartArc_target d, A.dartArc_source (q.firstDart hq_nonempty)]
    rfl
