import Util.IncidenceGeometry.FinitePolygonalSetCyclicSameEdgeArcSourceSeparation
import Util.IncidenceGeometry.FinitePolygonalSetCyclicPieceSourceNotArcTarget

open Classical
noncomputable section

lemma FinitePolygonalSetCyclicGlobalSourceSeparation
    (J : SimpleClosedPolygonalCurve)
    (E : List {γ : PolygonalArc // γ ∈ J.edgeArcs})
    (hEnodup : E.Nodup)
    (segmentIndex_lt :
      (e : Fin E.length) →
        (n : Fin ((E[e.1]'e.2).1.vertices.length - 1)) →
          n.1 + 1 < (E[e.1]'e.2).1.vertices.length)
    (cutList :
      (e : Fin E.length) →
        Fin ((E[e.1]'e.2).1.vertices.length - 1) → List ℝ)
    (cutList_nodup : ∀ e n, (cutList e n).Nodup)
    (cutList_bounds : ∀ e n t, t ∈ cutList e n → 0 ≤ t ∧ t ≤ 1)
    (localPieceIndex :
      (e : Fin E.length) →
        Fin ((E[e.1]'e.2).1.vertices.length - 1) → Type)
    (pieceNumber :
      (Sigma (fun e : Fin E.length =>
        Sigma (fun n : Fin ((E[e.1]'e.2).1.vertices.length - 1) =>
          localPieceIndex e n))) → ℕ)
    (pieceNumber_lt :
      ∀ i : Sigma (fun e : Fin E.length =>
        Sigma (fun n : Fin ((E[e.1]'e.2).1.vertices.length - 1) =>
          localPieceIndex e n)),
        pieceNumber i + 1 < (cutList i.1 i.2.1).length)
    (pieceNumber_injective :
      ∀ e n (a b : localPieceIndex e n),
        pieceNumber ⟨e, ⟨n, a⟩⟩ =
          pieceNumber ⟨e, ⟨n, b⟩⟩ →
        a = b)
    (pieceSourceParam :
      (Sigma (fun e : Fin E.length =>
        Sigma (fun n : Fin ((E[e.1]'e.2).1.vertices.length - 1) =>
          localPieceIndex e n))) → Set.Icc (0 : ℝ) 1)
    (pieceTargetParam :
      (Sigma (fun e : Fin E.length =>
        Sigma (fun n : Fin ((E[e.1]'e.2).1.vertices.length - 1) =>
          localPieceIndex e n))) → Set.Icc (0 : ℝ) 1)
    (pieceSourceParam_lt :
      ∀ i : Sigma (fun e : Fin E.length =>
        Sigma (fun n : Fin ((E[e.1]'e.2).1.vertices.length - 1) =>
          localPieceIndex e n)),
        pieceSourceParam i < pieceTargetParam i)
    (pieceSourceParam_eq :
      ∀ i : Sigma (fun e : Fin E.length =>
        Sigma (fun n : Fin ((E[e.1]'e.2).1.vertices.length - 1) =>
          localPieceIndex e n)),
        (pieceSourceParam i).1 =
          (cutList i.1 i.2.1)[pieceNumber i]'
            (Nat.lt_of_succ_lt (pieceNumber_lt i)))
    (pieceTargetParam_eq :
      ∀ i : Sigma (fun e : Fin E.length =>
        Sigma (fun n : Fin ((E[e.1]'e.2).1.vertices.length - 1) =>
          localPieceIndex e n)),
        (pieceTargetParam i).1 =
          (cutList i.1 i.2.1)[pieceNumber i + 1]'(pieceNumber_lt i))
    (pieceSource :
      (Sigma (fun e : Fin E.length =>
        Sigma (fun n : Fin ((E[e.1]'e.2).1.vertices.length - 1) =>
          localPieceIndex e n))) → EuclideanSpace ℝ (Fin 2))
    (pieceSource_eq :
      ∀ i : Sigma (fun e : Fin E.length =>
        Sigma (fun n : Fin ((E[e.1]'e.2).1.vertices.length - 1) =>
          localPieceIndex e n)),
        pieceSource i =
          AffineMap.lineMap
            ((E[i.1.1]'i.1.2).1.vertices[i.2.1.1]'
              (Nat.lt_of_succ_lt (segmentIndex_lt i.1 i.2.1)))
            ((E[i.1.1]'i.1.2).1.vertices[i.2.1.1 + 1]'
              (segmentIndex_lt i.1 i.2.1))
            (pieceSourceParam i).1) :
    let PieceIndex : Type :=
      Sigma (fun e : Fin E.length =>
        Sigma (fun n : Fin ((E[e.1]'e.2).1.vertices.length - 1) =>
          localPieceIndex e n))
    ∀ i j : PieceIndex, pieceSource i = pieceSource j → i = j := by
  intro PieceIndex i j hsource
  have source_mem_arc :
      ∀ q : PieceIndex, pieceSource q ∈ (E[q.1.1]'q.1.2).1.carrier := by
    intro q
    rw [(E[q.1.1]'q.1.2).1.carrier_eq]
    refine ⟨q.2.1.1, segmentIndex_lt q.1 q.2.1, ?_⟩
    rw [pieceSource_eq q, segment_eq_image_lineMap]
    exact ⟨(pieceSourceParam q).1, (pieceSourceParam q).2, rfl⟩
  have source_not_arc_target :
      ∀ q : PieceIndex, pieceSource q ≠ (E[q.1.1]'q.1.2).1.target := by
    intro q
    exact
      FinitePolygonalSetCyclicPieceSourceNotArcTarget
        J E segmentIndex_lt cutList cutList_bounds localPieceIndex
        pieceNumber pieceNumber_lt pieceSourceParam pieceTargetParam
        pieceSourceParam_lt pieceTargetParam_eq pieceSource pieceSource_eq q
  rcases i with ⟨ei, ni, ai⟩
  rcases j with ⟨ej, nj, aj⟩
  by_cases hedge_val : ei.1 = ej.1
  · have hedge : ei = ej := Fin.ext hedge_val
    subst ej
    exact
      FinitePolygonalSetCyclicSameEdgeArcSourceSeparation
        J E segmentIndex_lt cutList cutList_nodup cutList_bounds
        localPieceIndex pieceNumber pieceNumber_lt pieceNumber_injective
        pieceSourceParam pieceTargetParam pieceSourceParam_lt
        pieceSourceParam_eq pieceTargetParam_eq pieceSource pieceSource_eq
        ei ni nj ai aj hsource
  · let γ : {γ : PolygonalArc // γ ∈ J.edgeArcs} := E[ei.1]'ei.2
    let δ : {γ : PolygonalArc // γ ∈ J.edgeArcs} := E[ej.1]'ej.2
    have hγ_mem :
        pieceSource (⟨ei, ⟨ni, ai⟩⟩ : PieceIndex) ∈ γ.1.carrier := by
      simpa [γ] using source_mem_arc (⟨ei, ⟨ni, ai⟩⟩ : PieceIndex)
    have hδ_mem :
        pieceSource (⟨ej, ⟨nj, aj⟩⟩ : PieceIndex) ∈ δ.1.carrier := by
      simpa [δ] using source_mem_arc (⟨ej, ⟨nj, aj⟩⟩ : PieceIndex)
    have hδ_ne_γ : δ ≠ γ := by
      intro hδγ
      have hidx : ej.1 = ei.1 := hEnodup.getElem_inj_iff.mp hδγ
      exact hedge_val hidx.symm
    by_cases hforward : δ = J.successor γ
    · have hmem_inter :
          pieceSource (⟨ei, ⟨ni, ai⟩⟩ : PieceIndex) ∈
            γ.1.carrier ∩ δ.1.carrier :=
        ⟨hγ_mem, by simpa [hsource] using hδ_mem⟩
      have hinter := J.adjacent_intersection γ
      have hsource_target :
          pieceSource (⟨ei, ⟨ni, ai⟩⟩ : PieceIndex) = γ.1.target := by
        rw [hforward] at hmem_inter
        rw [hinter] at hmem_inter
        simpa using hmem_inter
      exact (source_not_arc_target (⟨ei, ⟨ni, ai⟩⟩ : PieceIndex)
        (by simpa [γ] using hsource_target)).elim
    · by_cases hbackward : γ = J.successor δ
      · have hmem_inter :
            pieceSource (⟨ej, ⟨nj, aj⟩⟩ : PieceIndex) ∈
              δ.1.carrier ∩ γ.1.carrier :=
          ⟨hδ_mem, by simpa [hsource] using hγ_mem⟩
        have hinter := J.adjacent_intersection δ
        have hsource_target :
            pieceSource (⟨ej, ⟨nj, aj⟩⟩ : PieceIndex) = δ.1.target := by
          rw [hbackward] at hmem_inter
          rw [hinter] at hmem_inter
          simpa using hmem_inter
        exact (source_not_arc_target (⟨ej, ⟨nj, aj⟩⟩ : PieceIndex)
          (by simpa [δ] using hsource_target)).elim
      · have hsuccδ_ne_γ : J.successor δ ≠ γ := by
          intro hsucc
          exact hbackward hsucc.symm
        have hdisjoint : Disjoint γ.1.carrier δ.1.carrier :=
          J.nonadjacent_disjoint γ δ hδ_ne_γ hforward hsuccδ_ne_γ
        exact False.elim ((Set.disjoint_left.mp hdisjoint)
          hγ_mem (by simpa [hsource] using hδ_mem))
