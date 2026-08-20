import ErdosProblems.Erdos733.ST.FinitePolygonalSetCyclicGlobalElementaryPieceSkeleton
import Mathlib.Data.List.ProdSigma

open Classical
noncomputable section

-- [TABLET NODE: FinitePolygonalSetCyclicGlobalPieceStreamEnumeration]
lemma FinitePolygonalSetCyclicGlobalPieceStreamEnumeration
    (J : SimpleClosedPolygonalCurve) (_K : FinitePolygonalSet)
    (E : List {γ : PolygonalArc // γ ∈ J.edgeArcs})
    (cutList :
      (e : Fin E.length) →
        Fin ((E[e.1]'e.2).1.vertices.length - 1) → List ℝ)
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
    (pieceNumber_surjective :
      ∀ e n k (_hk : k + 1 < (cutList e n).length),
        ∃ a : localPieceIndex e n, pieceNumber ⟨e, ⟨n, a⟩⟩ = k)
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
          (cutList i.1 i.2.1)[pieceNumber i + 1]'
            (pieceNumber_lt i)) :
    let PieceIndex : Type :=
      Sigma (fun e : Fin E.length =>
        Sigma (fun n : Fin ((E[e.1]'e.2).1.vertices.length - 1) =>
          localPieceIndex e n))
    let OrderIndex : Type :=
      Sigma (fun e : Fin E.length =>
        Sigma (fun n : Fin ((E[e.1]'e.2).1.vertices.length - 1) =>
          Fin ((cutList e n).length - 1)))
    let orderIndexList : List OrderIndex :=
      (List.finRange E.length).sigma fun e =>
        (List.finRange ((E[e.1]'e.2).1.vertices.length - 1)).sigma fun n =>
          List.finRange ((cutList e n).length - 1)
    ∃ (pieceAt : OrderIndex → PieceIndex) (pieceStream : List PieceIndex),
      orderIndexList.Nodup ∧
        (∀ o : OrderIndex, o ∈ orderIndexList) ∧
          (∀ o : OrderIndex, (pieceAt o).1 = o.1) ∧
            (∀ o : OrderIndex, (pieceAt o).2.1.1 = o.2.1.1) ∧
              (∀ o : OrderIndex, pieceNumber (pieceAt o) = o.2.2.1) ∧
                Function.Injective pieceAt ∧
                  pieceStream = orderIndexList.map pieceAt ∧
                    pieceStream.Nodup ∧
                      (∀ i : PieceIndex, i ∈ pieceStream) ∧
                        (∀ (o : OrderIndex)
                          (hnext :
                            o.2.2.1 + 1 < (cutList o.1 o.2.1).length - 1),
                          let oNext : OrderIndex :=
                            ⟨o.1, ⟨o.2.1, ⟨o.2.2.1 + 1, hnext⟩⟩⟩
                          pieceTargetParam (pieceAt o) =
                            pieceSourceParam (pieceAt oNext)) := by
-- BODY
  classical
  let PieceIndex : Type :=
    Sigma (fun e : Fin E.length =>
      Sigma (fun n : Fin ((E[e.1]'e.2).1.vertices.length - 1) =>
        localPieceIndex e n))
  let OrderIndex : Type :=
    Sigma (fun e : Fin E.length =>
      Sigma (fun n : Fin ((E[e.1]'e.2).1.vertices.length - 1) =>
        Fin ((cutList e n).length - 1)))
  let orderIndexList : List OrderIndex :=
    (List.finRange E.length).sigma fun e =>
      (List.finRange ((E[e.1]'e.2).1.vertices.length - 1)).sigma fun n =>
        List.finRange ((cutList e n).length - 1)
  have orderIndexList_nodup : orderIndexList.Nodup := by
    dsimp [orderIndexList, OrderIndex]
    apply List.Nodup.sigma
    · exact List.nodup_finRange E.length
    · intro e
      apply List.Nodup.sigma
      · exact List.nodup_finRange ((E[e.1]'e.2).1.vertices.length - 1)
      · intro n
        exact List.nodup_finRange ((cutList e n).length - 1)
  have orderIndexList_mem : ∀ o : OrderIndex, o ∈ orderIndexList := by
    intro o
    rcases o with ⟨e, n, k⟩
    dsimp [orderIndexList, OrderIndex]
    rw [List.mem_sigma]
    refine ⟨List.mem_finRange e, ?_⟩
    rw [List.mem_sigma]
    exact ⟨List.mem_finRange n, List.mem_finRange k⟩
  let pieceAt : OrderIndex → PieceIndex := fun o =>
    let hk : o.2.2.1 + 1 < (cutList o.1 o.2.1).length := by
      have h : o.2.2.1 < (cutList o.1 o.2.1).length - 1 := o.2.2.2
      omega
    ⟨o.1, ⟨o.2.1,
      Classical.choose (pieceNumber_surjective o.1 o.2.1 o.2.2.1 hk)⟩⟩
  have pieceAt_number :
      ∀ o : OrderIndex, pieceNumber (pieceAt o) = o.2.2.1 := by
    intro o
    dsimp [pieceAt]
    exact Classical.choose_spec
      (pieceNumber_surjective o.1 o.2.1 o.2.2.1 (by
        have h : o.2.2.1 < (cutList o.1 o.2.1).length - 1 := o.2.2.2
        omega))
  have pieceAt_edge : ∀ o : OrderIndex, (pieceAt o).1 = o.1 := by
    intro o
    rfl
  have pieceAt_segment : ∀ o : OrderIndex, (pieceAt o).2.1.1 = o.2.1.1 := by
    intro o
    rfl
  have pieceAt_injective : Function.Injective pieceAt := by
    intro a b hab
    cases a with
    | mk ea resta =>
      cases b with
      | mk eb restb =>
        cases resta with
        | mk na ka =>
          cases restb with
          | mk nb kb =>
            dsimp [pieceAt] at hab
            have habNumber := congrArg pieceNumber hab
            injection hab with he hrest
            subst eb
            injection hrest with hn ha
            subst nb
            have hnum : ka.1 = kb.1 := by
              rw [← pieceAt_number ⟨ea, ⟨na, ka⟩⟩,
                ← pieceAt_number ⟨ea, ⟨na, kb⟩⟩]
              exact habNumber
            have hk : ka = kb := Fin.ext hnum
            subst kb
            rfl
  let pieceStream : List PieceIndex := orderIndexList.map pieceAt
  have pieceStream_nodup : pieceStream.Nodup := by
    exact orderIndexList_nodup.map pieceAt_injective
  have pieceStream_mem : ∀ i : PieceIndex, i ∈ pieceStream := by
    intro i
    rcases i with ⟨e, n, a⟩
    let hk : pieceNumber ⟨e, ⟨n, a⟩⟩ <
        (cutList e n).length - 1 := by
      have hlt : pieceNumber ⟨e, ⟨n, a⟩⟩ + 1 <
          (cutList e n).length := by
        simpa using pieceNumber_lt ⟨e, ⟨n, a⟩⟩
      omega
    let o : OrderIndex := ⟨e, ⟨n, ⟨pieceNumber ⟨e, ⟨n, a⟩⟩, hk⟩⟩⟩
    have ho_mem : o ∈ orderIndexList := orderIndexList_mem o
    have hpiece : pieceAt o = ⟨e, ⟨n, a⟩⟩ := by
      dsimp [o, pieceAt]
      congr
      exact pieceNumber_injective e n
        (Classical.choose
          (pieceNumber_surjective e n (pieceNumber ⟨e, ⟨n, a⟩⟩) (by
            exact pieceNumber_lt ⟨e, ⟨n, a⟩⟩))) a
        (by
          exact Classical.choose_spec
            (pieceNumber_surjective e n (pieceNumber ⟨e, ⟨n, a⟩⟩)
              (pieceNumber_lt ⟨e, ⟨n, a⟩⟩)))
    exact List.mem_map.mpr ⟨o, ho_mem, hpiece⟩
  have adjacent_params :
      ∀ (o : OrderIndex)
        (hnext : o.2.2.1 + 1 < (cutList o.1 o.2.1).length - 1),
        let oNext : OrderIndex :=
          ⟨o.1, ⟨o.2.1, ⟨o.2.2.1 + 1, hnext⟩⟩⟩
        pieceTargetParam (pieceAt o) = pieceSourceParam (pieceAt oNext) := by
    intro o hnext
    dsimp
    apply Subtype.ext
    have hnum := pieceAt_number o
    have hnumNext := pieceAt_number
      ⟨o.1, ⟨o.2.1, ⟨o.2.2.1 + 1, hnext⟩⟩⟩
    have hk1 : o.2.2.1 + 1 < (cutList o.1 o.2.1).length := by
      omega
    have ht :
        (pieceTargetParam (pieceAt o)).1 =
          (cutList o.1 o.2.1)[o.2.2.1 + 1]'hk1 := by
      simpa [pieceAt, hnum] using pieceTargetParam_eq (pieceAt o)
    have hs :
        (pieceSourceParam
          (pieceAt ⟨o.1, ⟨o.2.1, ⟨o.2.2.1 + 1, hnext⟩⟩⟩)).1 =
          (cutList o.1 o.2.1)[o.2.2.1 + 1]'hk1 := by
      simpa [pieceAt, hnumNext] using
        pieceSourceParam_eq
          (pieceAt ⟨o.1, ⟨o.2.1, ⟨o.2.2.1 + 1, hnext⟩⟩⟩)
    exact ht.trans hs.symm
  refine ⟨pieceAt, pieceStream, orderIndexList_nodup, orderIndexList_mem,
    pieceAt_edge, pieceAt_segment, pieceAt_number, pieceAt_injective, rfl,
    pieceStream_nodup, pieceStream_mem, adjacent_params⟩
