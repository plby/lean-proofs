import Util.IncidenceGeometry.OrdinaryDrawingImage
import Util.IncidenceGeometry.PlaneFaceData
import Util.IncidenceGeometry.SimpleClosedPolygonalCurve
import Util.IncidenceGeometry.SimpleClosedPolygonalCurveOfCyclicArcList
import Util.IncidenceGeometry.DeleteNonbridgeReturnPathWitness
import Util.IncidenceGeometry.DeleteNonbridgePathArcList
import Util.IncidenceGeometry.PlaneDartArcLocalGeometry
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Tactic

open Classical
noncomputable section

lemma DeleteNonbridgeSimpleClosedCurveWitness {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] [DecidableRel G.Adj] (D : OrdinaryPolygonalDrawing G)
    (hD : D.crossingSet.card = 0) (A : PlaneFaceData G D) (e : G.edgeFinset)
    (hconn : G.Connected) (he : ¬ G.IsBridge e.1) :
    ∃ d : G.Dart, d.edge = e.1 ∧
      ∃ J : SimpleClosedPolygonalCurve,
        J.carrier ⊆ OrdinaryDrawingImage G D ∧
          ∃ γ : {γ : PolygonalArc // γ ∈ J.edgeArcs},
            γ.1.carrier = (A.dartArc d).carrier ∧
              γ.1.source = (A.dartArc d).source ∧
                γ.1.target = (A.dartArc d).target := by
  classical
  rcases DeleteNonbridgeReturnPathWitness G e he with ⟨d, hd, p, hp⟩
  rcases DeleteNonbridgePathArcList G D A d p hp with
    ⟨q, hq_eq, hq_path, hq_nonempty, arcs, harcs, hd_mem_arcs, hhead_arcs,
      hcarrier_arcs, hchain_arcs, hfirst_attach, hlast_attach, harcs_nodup,
      hq_darts_length_two, harcs_length_three, hd_not_mem_path_arcs,
      hform_endpoint⟩
  have harcs_length_two : 2 ≤ arcs.length :=
    le_trans (by decide : 2 ≤ 3) harcs_length_three
  have hlocal_geom := PlaneDartArcLocalGeometry G D hD A
  have hp_deleted_edge_not_mem : s(d.snd, d.fst) ∉ p.edges := by
    intro hmem
    have hEdgeSet :
        s(d.snd, d.fst) ∈ (G.deleteEdges {s(d.snd, d.fst)}).edgeSet :=
      SimpleGraph.Walk.edges_subset_edgeSet p hmem
    rw [SimpleGraph.edgeSet_deleteEdges] at hEdgeSet
    exact hEdgeSet.2 (by simp)
  have hq_edges_eq : q.edges = p.edges := by
    rw [hq_eq]
    exact p.edges_mapLe_eq_edges (G.deleteEdges_le {s(d.snd, d.fst)})
  have hq_deleted_edge_not_mem : s(d.snd, d.fst) ∉ q.edges := by
    intro hmem
    exact hp_deleted_edge_not_mem (by simpa [hq_edges_eq] using hmem)
  have hd_edge_eq : d.edge = s(d.snd, d.fst) := by
    simp [SimpleGraph.Dart.edge]
  have hq_edges_nodup : q.edges.Nodup := hq_path.isTrail.edges_nodup
  have harcs_length_eq : arcs.length = q.darts.length + 1 := by
    simp [harcs]
  have hq_darts_length_eq : q.darts.length = q.length := by
    rw [SimpleGraph.Walk.length_darts]
  have hq_length_two : 2 ≤ q.length := by
    simpa [hq_darts_length_eq] using hq_darts_length_two
  have h_adjacent_intersection :
      ∀ γ : PolygonalArc, γ ∈ arcs →
        γ.carrier ∩ (arcs.formPerm γ).carrier = {γ.target} := by
    intro γ hγ
    rw [List.formPerm_apply_mem_eq_next harcs_nodup γ hγ]
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hγ
    rw [List.next_getElem arcs harcs_nodup i hi]
    by_cases hi_zero : i = 0
    · subst i
      have hq_darts_pos : 0 < q.darts.length := by omega
      have hmod : (0 + 1) % arcs.length = 1 := by
        apply Nat.mod_eq_of_lt
        omega
      have hcur : arcs[0] = A.dartArc d := by
        simpa [harcs]
      have hnext : arcs[(0 + 1) % arcs.length] = A.dartArc q.darts[0] := by
        have hmod' : 1 % (q.length + 1) = 1 := by
          apply Nat.mod_eq_of_lt
          omega
        simpa [harcs, hmod', hq_darts_length_eq]
      have hshare : d.toProd.2 = q.darts[0].toProd.1 := by
        have hdart := SimpleGraph.Walk.darts_getElem_eq_getVert (p := q) 0 hq_darts_pos
        rw [hdart]
        simp
      have hedge_ne : d.edge ≠ q.darts[0].edge := by
        intro hedge
        have hmem_edge : q.darts[0].edge ∈ q.edges := by
          rw [SimpleGraph.Walk.edges]
          exact List.mem_map.mpr ⟨q.darts[0], List.getElem_mem hq_darts_pos, rfl⟩
        have hsel_mem : d.edge ∈ q.edges := by
          simpa [hedge] using hmem_edge
        exact hq_deleted_edge_not_mem (by simpa [hd_edge_eq] using hsel_mem)
      have h := hlocal_geom.1 d q.darts[0] hshare hedge_ne
      simpa [hcur, hnext, A.dartArc_target d] using h
    · by_cases hi_next : i + 1 < arcs.length
      · have hi_pos : 0 < i := Nat.pos_of_ne_zero hi_zero
        let j := i - 1
        have hij : i = j + 1 := by
          dsimp [j]
          omega
        have hj_lt : j < q.darts.length := by
          dsimp [j]
          omega
        have hj_next_lt : j + 1 < q.darts.length := by
          dsimp [j]
          omega
        have hmod : (i + 1) % arcs.length = i + 1 := by
          exact Nat.mod_eq_of_lt hi_next
        have hcur : arcs[i] = A.dartArc q.darts[j] := by
          have hj_lt_len : j < q.length := by
            simpa [hq_darts_length_eq] using hj_lt
          simpa [harcs, hij, List.getElem_map, hj_lt_len]
        have hnext : arcs[(i + 1) % arcs.length] = A.dartArc q.darts[j + 1] := by
          have hj_next_lt_len : j + 1 < q.length := by
            simpa [hq_darts_length_eq] using hj_next_lt
          have hmod' : (j + 1 + 1) % (q.length + 1) = j + 1 + 1 := by
            apply Nat.mod_eq_of_lt
            omega
          simpa [harcs, hmod', hij, List.getElem_map, hj_next_lt_len]
        have hshare : q.darts[j].toProd.2 = q.darts[j + 1].toProd.1 := by
          have hdart_j := SimpleGraph.Walk.darts_getElem_eq_getVert (p := q) j hj_lt
          have hdart_next := SimpleGraph.Walk.darts_getElem_eq_getVert (p := q) (j + 1) hj_next_lt
          rw [hdart_j, hdart_next]
        have hedge_ne : q.darts[j].edge ≠ q.darts[j + 1].edge := by
          intro hedge
          have hj_edge_lt : j < q.edges.length := by simpa [SimpleGraph.Walk.edges] using hj_lt
          have hj_next_edge_lt : j + 1 < q.edges.length := by
            simpa [SimpleGraph.Walk.edges] using hj_next_lt
          have hedge_get :
              q.edges[j] = q.edges[j + 1] := by
            simpa [SimpleGraph.Walk.edges, List.getElem_map] using hedge
          have hidx_eq := (List.Nodup.getElem_inj_iff hq_edges_nodup).1 hedge_get
          omega
        have h := hlocal_geom.1 q.darts[j] q.darts[j + 1] hshare hedge_ne
        simpa [hcur, hnext, A.dartArc_target] using h
      · have hi_last : i = arcs.length - 1 := by omega
        have hq_darts_pos : 0 < q.darts.length := by omega
        let j := q.darts.length - 1
        have hj_lt : j < q.darts.length := by
          dsimp [j]
          omega
        have hmod : (i + 1) % arcs.length = 0 := by
          rw [hi_last]
          have hlen_pos : 0 < arcs.length := by omega
          rw [Nat.sub_add_cancel hlen_pos, Nat.mod_self]
        have hcur : arcs[i] = A.dartArc q.darts[j] := by
          have hmap_ne : q.darts.map A.dartArc ≠ [] := by
            exact List.ne_nil_of_length_pos (by simpa using hq_darts_pos)
          have hlast_dart : q.lastDart hq_nonempty = q.darts[j] := by
            rw [q.lastDart_eq_getLast_darts hq_nonempty]
            rw [List.getLast_eq_getElem]
          have harcs_last :
              arcs.getLast (List.ne_nil_of_mem hγ) = A.dartArc q.darts[j] := by
            simpa [harcs, List.getLast_cons, hmap_ne, hlast_dart, j]
          have hidx_last :
              arcs[i] = arcs.getLast (List.ne_nil_of_mem hγ) := by
            rw [List.getLast_eq_getElem]
            congr
          exact hidx_last.trans harcs_last
        have hnext : arcs[(i + 1) % arcs.length] = A.dartArc d := by
          have hmod' : (i + 1) % (q.length + 1) = 0 := by
            rw [hi_last, harcs_length_eq, hq_darts_length_eq]
            simp
          simpa [harcs, hmod']
        have hshare : q.darts[j].toProd.2 = d.toProd.1 := by
          have hdart := SimpleGraph.Walk.darts_getElem_eq_getVert (p := q) j hj_lt
          rw [hdart]
          have hq_length_pos : 0 < q.length := by omega
          simpa [j, hq_darts_length_eq, Nat.sub_add_cancel hq_length_pos] using
            (SimpleGraph.Walk.getVert_length (p := q))
        have hedge_ne : q.darts[j].edge ≠ d.edge := by
          intro hedge
          have hmem_edge : q.darts[j].edge ∈ q.edges := by
            rw [SimpleGraph.Walk.edges]
            exact List.mem_map.mpr ⟨q.darts[j], List.getElem_mem hj_lt, rfl⟩
          have hsel_mem : d.edge ∈ q.edges := by
            simpa [hedge] using hmem_edge
          exact hq_deleted_edge_not_mem (by simpa [hd_edge_eq] using hsel_mem)
        have h := hlocal_geom.1 q.darts[j] d hshare hedge_ne
        simpa [hcur, hnext, A.dartArc_target] using h
  have h_nonadjacent_disjoint :
      ∀ γ δ : PolygonalArc, γ ∈ arcs → δ ∈ arcs →
        δ ≠ γ → δ ≠ arcs.formPerm γ → arcs.formPerm δ ≠ γ →
          Disjoint γ.carrier δ.carrier := by
    intro γ δ hγ hδ hδ_ne hδ_ne_succ hsuccδ_ne
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hγ
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hδ
    have hform_get :
        ∀ r (hr : r < arcs.length),
          arcs.formPerm (arcs[r]) =
            arcs[(r + 1) % arcs.length]'(Nat.mod_lt _ (by omega)) := by
      intro r hr
      rw [List.formPerm_apply_mem_eq_next harcs_nodup (arcs[r]) (List.getElem_mem hr)]
      rw [List.next_getElem arcs harcs_nodup r hr]
    have hk_ne_i : k ≠ i := by
      intro hki
      exact hδ_ne (by subst k; rfl)
    have hk_ne_succ_i : k ≠ (i + 1) % arcs.length := by
      intro hki
      apply hδ_ne_succ
      rw [hform_get i hi]
      subst k
      rfl
    have hsucc_k_ne_i : (k + 1) % arcs.length ≠ i := by
      intro hki
      apply hsuccδ_ne
      rw [hform_get k hk]
      simpa [hki]
    have dart_fst_get :
        ∀ r (hr : r < q.darts.length), q.darts[r].toProd.1 = q.getVert r := by
      intro r hr
      have hdart := SimpleGraph.Walk.darts_getElem_eq_getVert (p := q) r hr
      simpa using congrArg (fun d : G.Dart => d.toProd.1) hdart
    have dart_snd_get :
        ∀ r (hr : r < q.darts.length), q.darts[r].toProd.2 = q.getVert (r + 1) := by
      intro r hr
      have hdart := SimpleGraph.Walk.darts_getElem_eq_getVert (p := q) r hr
      simpa using congrArg (fun d : G.Dart => d.toProd.2) hdart
    have getVert_inj :
        ∀ a b : ℕ, a ≤ q.length → b ≤ q.length →
          q.getVert a = q.getVert b → a = b := by
      intro a b ha hb hab
      exact hq_path.getVert_injOn ha hb hab
    have selected_path_endpoint_ne :
        ∀ r (hr : r < q.darts.length), r ≠ 0 → r + 1 ≠ q.length →
          d.toProd.1 ≠ q.darts[r].toProd.1 ∧
            d.toProd.1 ≠ q.darts[r].toProd.2 ∧
              d.toProd.2 ≠ q.darts[r].toProd.1 ∧
                d.toProd.2 ≠ q.darts[r].toProd.2 := by
      intro r hr hr_ne_zero hr_succ_ne_len
      have hr_len : r < q.length := by simpa [hq_darts_length_eq] using hr
      have hsource_end : d.toProd.1 = q.getVert q.length := by simp
      have htarget_start : d.toProd.2 = q.getVert 0 := by simp
      have hfst := dart_fst_get r hr
      have hsnd := dart_snd_get r hr
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro h
        have hget : q.getVert q.length = q.getVert r := by
          calc
            q.getVert q.length = d.toProd.1 := hsource_end.symm
            _ = q.darts[r].toProd.1 := h
            _ = q.getVert r := hfst
        have hidx := getVert_inj q.length r (by omega) (by omega) hget
        omega
      · intro h
        have hget : q.getVert q.length = q.getVert (r + 1) := by
          calc
            q.getVert q.length = d.toProd.1 := hsource_end.symm
            _ = q.darts[r].toProd.2 := h
            _ = q.getVert (r + 1) := hsnd
        have hidx := getVert_inj q.length (r + 1) (by omega) (by omega) hget
        exact hr_succ_ne_len hidx.symm
      · intro h
        have hget : q.getVert 0 = q.getVert r := by
          calc
            q.getVert 0 = d.toProd.2 := htarget_start.symm
            _ = q.darts[r].toProd.1 := h
            _ = q.getVert r := hfst
        have hidx := getVert_inj 0 r (by omega) (by omega) hget
        exact hr_ne_zero hidx.symm
      · intro h
        have hget : q.getVert 0 = q.getVert (r + 1) := by
          calc
            q.getVert 0 = d.toProd.2 := htarget_start.symm
            _ = q.darts[r].toProd.2 := h
            _ = q.getVert (r + 1) := hsnd
        have hidx := getVert_inj 0 (r + 1) (by omega) (by omega) hget
        omega
    have path_path_endpoint_ne :
        ∀ r s (hr : r < q.darts.length) (hs : s < q.darts.length),
          s ≠ r → s ≠ r + 1 → s + 1 ≠ r →
            q.darts[r].toProd.1 ≠ q.darts[s].toProd.1 ∧
              q.darts[r].toProd.1 ≠ q.darts[s].toProd.2 ∧
                q.darts[r].toProd.2 ≠ q.darts[s].toProd.1 ∧
                  q.darts[r].toProd.2 ≠ q.darts[s].toProd.2 := by
      intro r s hr hs hs_ne_r hs_ne_rsucc hssucc_ne_r
      have hr_len : r < q.length := by simpa [hq_darts_length_eq] using hr
      have hs_len : s < q.length := by simpa [hq_darts_length_eq] using hs
      have hrf := dart_fst_get r hr
      have hrs := dart_snd_get r hr
      have hsf := dart_fst_get s hs
      have hss := dart_snd_get s hs
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro h
        have hget : q.getVert r = q.getVert s := by
          calc
            q.getVert r = q.darts[r].toProd.1 := hrf.symm
            _ = q.darts[s].toProd.1 := h
            _ = q.getVert s := hsf
        exact hs_ne_r ((getVert_inj r s (by omega) (by omega) hget).symm)
      · intro h
        have hget : q.getVert r = q.getVert (s + 1) := by
          calc
            q.getVert r = q.darts[r].toProd.1 := hrf.symm
            _ = q.darts[s].toProd.2 := h
            _ = q.getVert (s + 1) := hss
        have hidx := getVert_inj r (s + 1) (by omega) (by omega) hget
        exact hssucc_ne_r hidx.symm
      · intro h
        have hget : q.getVert (r + 1) = q.getVert s := by
          calc
            q.getVert (r + 1) = q.darts[r].toProd.2 := hrs.symm
            _ = q.darts[s].toProd.1 := h
            _ = q.getVert s := hsf
        have hidx := getVert_inj (r + 1) s (by omega) (by omega) hget
        exact hs_ne_rsucc hidx.symm
      · intro h
        have hget : q.getVert (r + 1) = q.getVert (s + 1) := by
          calc
            q.getVert (r + 1) = q.darts[r].toProd.2 := hrs.symm
            _ = q.darts[s].toProd.2 := h
            _ = q.getVert (s + 1) := hss
        have hidx := getVert_inj (r + 1) (s + 1) (by omega) (by omega) hget
        exact hs_ne_r (by omega)
    by_cases hi_zero : i = 0
    · subst i
      by_cases hk_zero : k = 0
      · exact False.elim (hk_ne_i hk_zero)
      · let sidx := k - 1
        have hk_eq : k = sidx + 1 := by
          dsimp [sidx]
          omega
        have hsidx_lt : sidx < q.darts.length := by
          dsimp [sidx]
          omega
        have hsidx_ne_zero : sidx ≠ 0 := by
          intro hs0
          have hk_one : k = 1 := by omega
          exact hk_ne_succ_i (by
            rw [hk_one]
            have hmod1 : (0 + 1) % arcs.length = 1 := by
              apply Nat.mod_eq_of_lt
              omega
            exact hmod1.symm)
        have hsidx_succ_ne_len : sidx + 1 ≠ q.length := by
          intro hlast
          apply hsucc_k_ne_i
          rw [hk_eq, harcs_length_eq, hq_darts_length_eq, hlast]
          simp
        rcases selected_path_endpoint_ne sidx hsidx_lt hsidx_ne_zero hsidx_succ_ne_len with
          ⟨hff, hfs, hsf, hss⟩
        have hcur : arcs[0] = A.dartArc d := by simpa [harcs]
        have hdel : arcs[k] = A.dartArc q.darts[sidx] := by
          simpa [harcs, hk_eq, List.getElem_map]
        have hdisj := hlocal_geom.2 d q.darts[sidx] hff hfs hsf hss
        simpa [hcur, hdel] using hdisj
    · by_cases hk_zero : k = 0
      · subst k
        let ridx := i - 1
        have hi_eq : i = ridx + 1 := by
          dsimp [ridx]
          omega
        have hridx_lt : ridx < q.darts.length := by
          dsimp [ridx]
          omega
        have hridx_ne_zero : ridx ≠ 0 := by
          intro hr0
          apply hsucc_k_ne_i
          rw [hi_eq, hr0]
          have hmod1 : (0 + 1) % arcs.length = 1 := by
            apply Nat.mod_eq_of_lt
            omega
          exact hmod1
        have hridx_succ_ne_len : ridx + 1 ≠ q.length := by
          intro hlast
          apply hk_ne_succ_i
          rw [hi_eq, harcs_length_eq, hq_darts_length_eq, hlast]
          simp
        rcases selected_path_endpoint_ne ridx hridx_lt hridx_ne_zero hridx_succ_ne_len with
          ⟨hff, hfs, hsf, hss⟩
        have hcur : arcs[i] = A.dartArc q.darts[ridx] := by
          simpa [harcs, hi_eq, List.getElem_map]
        have hdel : arcs[0] = A.dartArc d := by simpa [harcs]
        have hdisj := (hlocal_geom.2 d q.darts[ridx] hff hfs hsf hss).symm
        simpa [hcur, hdel] using hdisj
      · let ridx := i - 1
        let sidx := k - 1
        have hi_eq : i = ridx + 1 := by
          dsimp [ridx]
          omega
        have hk_eq : k = sidx + 1 := by
          dsimp [sidx]
          omega
        have hridx_lt : ridx < q.darts.length := by
          dsimp [ridx]
          omega
        have hsidx_lt : sidx < q.darts.length := by
          dsimp [sidx]
          omega
        have hs_ne_r : sidx ≠ ridx := by
          intro hsr
          exact hk_ne_i (by omega)
        have hs_ne_rsucc : sidx ≠ ridx + 1 := by
          intro hsr
          exact hk_ne_succ_i (by
            rw [hi_eq, hk_eq, hsr]
            have hmod : (ridx + 1 + 1) % arcs.length = ridx + 1 + 1 := by
              apply Nat.mod_eq_of_lt
              omega
            exact hmod.symm)
        have hssucc_ne_r : sidx + 1 ≠ ridx := by
          intro hsr
          exact hsucc_k_ne_i (by
            rw [hi_eq, hk_eq]
            have hmod : (sidx + 1 + 1) % arcs.length = sidx + 1 + 1 := by
              apply Nat.mod_eq_of_lt
              omega
            rw [hmod]
            omega)
        rcases path_path_endpoint_ne ridx sidx hridx_lt hsidx_lt hs_ne_r hs_ne_rsucc
            hssucc_ne_r with
          ⟨hff, hfs, hsf, hss⟩
        have hcur : arcs[i] = A.dartArc q.darts[ridx] := by
          simpa [harcs, hi_eq, List.getElem_map]
        have hdel : arcs[k] = A.dartArc q.darts[sidx] := by
          simpa [harcs, hk_eq, List.getElem_map]
        have hdisj := hlocal_geom.2 q.darts[ridx] q.darts[sidx] hff hfs hsf hss
        simpa [hcur, hdel] using hdisj
  rcases SimpleClosedPolygonalCurveOfCyclicArcList arcs harcs_nodup harcs_length_two
      hform_endpoint h_adjacent_intersection h_nonadjacent_disjoint with
    ⟨J, hJ_edges, hJ_carrier, hhead_edge⟩
  refine ⟨d, hd, J, ?_, ?_⟩
  · intro x hx
    rw [hJ_carrier] at hx
    rcases Set.mem_iUnion.mp hx with ⟨γ, hxγ⟩
    have hγ_mem_arcs : γ.1 ∈ arcs := List.mem_toFinset.mp γ.2
    exact hcarrier_arcs γ.1 hγ_mem_arcs hxγ
  · rcases hhead_edge (A.dartArc d) hhead_arcs with ⟨γ, hγ⟩
    refine ⟨γ, ?_, ?_, ?_⟩ <;> rw [hγ]
