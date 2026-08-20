import ErdosProblems.Erdos733.ST.FinitePolygonalSetCyclicTraversalCuts
import ErdosProblems.Erdos733.ST.CollinearAdjacentSubsegmentsMeetAtEndpoint

open Classical
noncomputable section

-- [TABLET NODE: FinitePolygonalSetCyclicAdjacentPieceCarriersMeetAtJunction]
lemma FinitePolygonalSetCyclicAdjacentPieceCarriersMeetAtJunction
    (J : SimpleClosedPolygonalCurve) (K : FinitePolygonalSet)
    (D : FinitePolygonalSetCyclicTraversalCuts J K)
    (p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points})
    (n : ℕ) (hn : n + 1 < (D.arcPieceOrder p).length) :
    D.pieceCarrier ((D.arcPieceOrder p)[n]) ∩
        D.pieceCarrier ((D.arcPieceOrder p)[n + 1]) =
      ({D.pieceTarget ((D.arcPieceOrder p)[n])} :
        Set (EuclideanSpace ℝ (Fin 2))) := by
-- BODY
  let i : D.pieceIndex := (D.arcPieceOrder p)[n]
  let j : D.pieceIndex := (D.arcPieceOrder p)[n + 1]
  have hconsec := D.arcPieceOrder_consecutive p n hn
  have hjoin : D.pieceTarget i = D.pieceSource j := by
    simpa [i, j] using hconsec.1
  have hpiece_subset_parent :
      ∀ q : D.pieceIndex,
        D.pieceCarrier q ⊆
          segment ℝ
            ((D.pieceArc q).1.vertices[(D.pieceSegmentIndex q).1]'
              (Nat.lt_of_succ_lt (D.pieceSegmentIndex q).2))
            ((D.pieceArc q).1.vertices[(D.pieceSegmentIndex q).1 + 1]'
              (D.pieceSegmentIndex q).2) := by
    intro q x hx
    rw [D.pieceCarrier_eq q] at hx
    have hs :
        D.pieceSource q ∈
          segment ℝ
            ((D.pieceArc q).1.vertices[(D.pieceSegmentIndex q).1]'
              (Nat.lt_of_succ_lt (D.pieceSegmentIndex q).2))
            ((D.pieceArc q).1.vertices[(D.pieceSegmentIndex q).1 + 1]'
              (D.pieceSegmentIndex q).2) := by
      rw [D.pieceSource_eq q, segment_eq_image_lineMap]
      exact ⟨(D.pieceSourceParam q).1, (D.pieceSourceParam q).2, rfl⟩
    have ht :
        D.pieceTarget q ∈
          segment ℝ
            ((D.pieceArc q).1.vertices[(D.pieceSegmentIndex q).1]'
              (Nat.lt_of_succ_lt (D.pieceSegmentIndex q).2))
            ((D.pieceArc q).1.vertices[(D.pieceSegmentIndex q).1 + 1]'
              (D.pieceSegmentIndex q).2) := by
      rw [D.pieceTarget_eq q, segment_eq_image_lineMap]
      exact ⟨(D.pieceTargetParam q).1, (D.pieceTargetParam q).2, rfl⟩
    exact (convex_segment _ _).segment_subset hs ht hx
  have hpiece_subset_arc :
      ∀ q : D.pieceIndex, D.pieceCarrier q ⊆ (D.pieceArc q).1.carrier := by
    intro q x hx
    rw [(D.pieceArc q).1.carrier_eq]
    exact ⟨(D.pieceSegmentIndex q).1, (D.pieceSegmentIndex q).2,
      hpiece_subset_parent q hx⟩
  rcases hconsec.2 with hsameSeg | hnextOrSucc
  · rcases hsameSeg with ⟨harc, hseg, hparam⟩
    have hverts :
        (D.pieceArc i).1.vertices[(D.pieceSegmentIndex i).1]'
            (Nat.lt_of_succ_lt (D.pieceSegmentIndex i).2) ≠
          (D.pieceArc i).1.vertices[(D.pieceSegmentIndex i).1 + 1]'
            (D.pieceSegmentIndex i).2 := by
      intro hv
      have hidx : (D.pieceSegmentIndex i).1 = (D.pieceSegmentIndex i).1 + 1 :=
        ((D.pieceArc i).1.simple_vertices.getElem_inj_iff).mp hv
      omega
    have hvlt : D.pieceTargetParam i < D.pieceTargetParam j := by
      have hsrc_tgt_j := D.pieceSourceParam_lt_targetParam j
      rwa [← hparam] at hsrc_tgt_j
    have hbase :=
      CollinearAdjacentSubsegmentsMeetAtEndpoint
        ((D.pieceArc i).1.vertices[(D.pieceSegmentIndex i).1]'
          (Nat.lt_of_succ_lt (D.pieceSegmentIndex i).2))
        ((D.pieceArc i).1.vertices[(D.pieceSegmentIndex i).1 + 1]'
          (D.pieceSegmentIndex i).2)
        hverts
        (D.pieceSourceParam i) (D.pieceTargetParam i) (D.pieceTargetParam j)
        (D.pieceSourceParam_lt_targetParam i) hvlt
    simpa [i, j, D.pieceCarrier_eq, D.pieceSource_eq, D.pieceTarget_eq,
      harc, hseg, hparam] using hbase
  · rcases hnextOrSucc with hnext | hsucc
    · rcases hnext with ⟨harc, hseg, htarget_one, hsource_zero⟩
      let γ : PolygonalArc := (D.pieceArc i).1
      let m : ℕ := (D.pieceSegmentIndex i).1
      have hi : m + 1 < γ.vertices.length := by
        simpa [γ, m] using (D.pieceSegmentIndex i).2
      have hj : m + 1 + 1 < γ.vertices.length := by
        have hj0 := (D.pieceSegmentIndex j).2
        simpa [γ, m, i, j, harc, ← hseg, Nat.add_assoc] using hj0
      have htarget_vertex : D.pieceTarget i = γ.vertices[m + 1]'hi := by
        rw [D.pieceTarget_eq i, htarget_one]
        simp [γ, m]
      apply subset_antisymm
      · intro x hx
        have hxi_full :
            x ∈ segment ℝ (γ.vertices[m]'(Nat.lt_of_succ_lt hi))
                (γ.vertices[m + 1]'hi) := by
          simpa [γ, m] using hpiece_subset_parent i hx.1
        have hxj_full :
            x ∈ segment ℝ (γ.vertices[m + 1]'(Nat.lt_of_succ_lt hj))
                (γ.vertices[m + 1 + 1]'hj) := by
          simpa [γ, m, i, j, harc, ← hseg, Nat.add_assoc] using
            hpiece_subset_parent j hx.2
        have hx_inter :
            x ∈ segment ℝ (γ.vertices[m]'(Nat.lt_of_succ_lt hi))
                  (γ.vertices[m + 1]'hi) ∩
                segment ℝ (γ.vertices[m + 1]'(Nat.lt_of_succ_lt hj))
                  (γ.vertices[m + 1 + 1]'hj) := ⟨hxi_full, hxj_full⟩
        have hinter := γ.segment_intersections hi hj (by omega)
        rw [hinter] at hx_inter
        have hadj : m + 1 = m + 1 := rfl
        have hx_eq : x = γ.vertices[m + 1]'hi := by
          simpa [hadj] using hx_inter
        exact Set.mem_singleton_iff.2 (by simpa [i, htarget_vertex] using hx_eq)
      · intro x hx
        rw [Set.mem_singleton_iff] at hx
        subst x
        constructor
        · rw [D.pieceCarrier_eq i]
          exact right_mem_segment ℝ (D.pieceSource i) (D.pieceTarget i)
        · rw [D.pieceCarrier_eq j]
          simpa [i, j, hjoin] using
            left_mem_segment ℝ (D.pieceSource j) (D.pieceTarget j)
    · rcases hsucc with ⟨harc, hlast, hzero, htarget_one, hsource_zero⟩
      let γ : PolygonalArc := (D.pieceArc i).1
      let m : ℕ := (D.pieceSegmentIndex i).1
      have hi : m + 1 < γ.vertices.length := by
        simpa [γ, m] using (D.pieceSegmentIndex i).2
      have htarget_arc : D.pieceTarget i = γ.target := by
        have htarget_vertex : D.pieceTarget i = γ.vertices[m + 1]'hi := by
          rw [D.pieceTarget_eq i, htarget_one]
          simp [γ, m]
        have hvertex_target : γ.vertices[m + 1]'hi = γ.target := by
          have hlast_some :
              γ.vertices.getLast? = some (γ.vertices[m + 1]'hi) := by
            rw [List.getLast?_eq_getElem?]
            have hidx : γ.vertices.length - 1 = m + 1 := by
              have hlast' : m + 2 = γ.vertices.length := by
                simpa [γ, m, i] using hlast
              omega
            simp [hidx]
          exact Option.some.inj (by rw [← hlast_some, γ.target_eq_last])
        exact htarget_vertex.trans hvertex_target
      apply subset_antisymm
      · intro x hx
        have hxi_arc : x ∈ γ.carrier := by
          simpa [γ] using hpiece_subset_arc i hx.1
        have hxj_arc : x ∈ (J.successor (D.pieceArc i)).1.carrier := by
          simpa [i, j, harc] using hpiece_subset_arc j hx.2
        have hx_inter :
            x ∈ γ.carrier ∩ (J.successor (D.pieceArc i)).1.carrier :=
          ⟨hxi_arc, hxj_arc⟩
        have hinter := J.adjacent_intersection (D.pieceArc i)
        rw [hinter] at hx_inter
        have hx_eq : x = γ.target := by
          simpa [γ] using hx_inter
        exact Set.mem_singleton_iff.2 (by simpa [i, γ, htarget_arc] using hx_eq)
      · intro x hx
        rw [Set.mem_singleton_iff] at hx
        subst x
        constructor
        · rw [D.pieceCarrier_eq i]
          exact right_mem_segment ℝ (D.pieceSource i) (D.pieceTarget i)
        · rw [D.pieceCarrier_eq j]
          simpa [i, j, hjoin] using
            left_mem_segment ℝ (D.pieceSource j) (D.pieceTarget j)
