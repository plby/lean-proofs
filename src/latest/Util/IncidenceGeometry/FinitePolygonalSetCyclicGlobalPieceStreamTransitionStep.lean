import Util.IncidenceGeometry.FiniteSortedRealCutListEndpointEntries
import Util.IncidenceGeometry.FinitePolygonalSetCyclicGlobalPieceStreamEnumeration

open Classical
noncomputable section

lemma FinitePolygonalSetCyclicGlobalPieceStreamTransitionStep
    (J : SimpleClosedPolygonalCurve) (_K : FinitePolygonalSet)
    (E : List {γ : PolygonalArc // γ ∈ J.edgeArcs})
    (hEpos : 0 < E.length)
    (hEsucc : ∀ n (hn : n + 1 < E.length),
      J.successor (E[n]) = E[n + 1])
    (hEwrap : ∀ (hLast : E.length - 1 < E.length) (hFirst : 0 < E.length),
      J.successor (E[E.length - 1]'hLast) = E[0]'hFirst)
    (cutList :
      (e : Fin E.length) →
        Fin ((E[e.1]'e.2).1.vertices.length - 1) → List ℝ)
    (cutList_sorted : ∀ e n, (cutList e n).SortedLT)
    (cutList_zero : ∀ e n, (0 : ℝ) ∈ cutList e n)
    (cutList_one : ∀ e n, (1 : ℝ) ∈ cutList e n)
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
    (pieceNumber_surjective :
      ∀ e n k (_hk : k + 1 < (cutList e n).length),
        ∃ a : localPieceIndex e n, pieceNumber ⟨e, ⟨n, a⟩⟩ = k)
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
    ∃ (pieceAt : OrderIndex → PieceIndex),
      (∀ o : OrderIndex, (pieceAt o).1 = o.1) ∧
      (∀ o : OrderIndex, (pieceAt o).2.1.1 = o.2.1.1) ∧
      (∀ o : OrderIndex, pieceNumber (pieceAt o) = o.2.2.1) ∧
      ∀ o : OrderIndex,
        ∃ oNext : OrderIndex,
          let i : PieceIndex := pieceAt o
          let j : PieceIndex := pieceAt oNext
          ((i.1 = j.1 ∧
              i.2.1.1 = j.2.1.1 ∧
              pieceTargetParam i = pieceSourceParam j) ∨
            (i.1 = j.1 ∧
              i.2.1.1 + 1 = j.2.1.1 ∧
              (pieceTargetParam i).1 = 1 ∧
              (pieceSourceParam j).1 = 0) ∨
            (E[j.1.1]'j.1.2 = J.successor (E[i.1.1]'i.1.2) ∧
              i.2.1.1 + 2 = (E[i.1.1]'i.1.2).1.vertices.length ∧
              j.2.1.1 = 0 ∧
              (pieceTargetParam i).1 = 1 ∧
              (pieceSourceParam j).1 = 0)) := by
  classical
  intro PieceIndex OrderIndex
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
  have endpoint_data :
      ∀ e n,
        2 ≤ (cutList e n).length ∧
          (∀ h : 0 < (cutList e n).length,
            (cutList e n)[0]'h = 0) ∧
            (∀ h : (cutList e n).length - 1 < (cutList e n).length,
              (cutList e n)[(cutList e n).length - 1]'h = 1) := by
    intro e n
    exact FiniteSortedRealCutListEndpointEntries
      (cutList e n) (cutList_sorted e n) (cutList_zero e n)
      (cutList_one e n) (cutList_bounds e n)
  refine ⟨pieceAt, pieceAt_edge, pieceAt_segment, pieceAt_number, ?_⟩
  intro o
  rcases o with ⟨e, n, k⟩
  by_cases hgap : k.1 + 1 < (cutList e n).length - 1
  · let oNext : OrderIndex := ⟨e, ⟨n, ⟨k.1 + 1, hgap⟩⟩⟩
    refine ⟨oNext, Or.inl ?_⟩
    dsimp [oNext]
    refine ⟨?_, ?_, ?_⟩
    · rw [pieceAt_edge ⟨e, ⟨n, k⟩⟩,
        pieceAt_edge ⟨e, ⟨n, ⟨k.1 + 1, hgap⟩⟩⟩]
    · rw [pieceAt_segment ⟨e, ⟨n, k⟩⟩,
        pieceAt_segment ⟨e, ⟨n, ⟨k.1 + 1, hgap⟩⟩⟩]
    · apply Subtype.ext
      have hnum := pieceAt_number ⟨e, ⟨n, k⟩⟩
      have hnumNext := pieceAt_number ⟨e, ⟨n, ⟨k.1 + 1, hgap⟩⟩⟩
      have hk1 : k.1 + 1 < (cutList e n).length := by omega
      have ht :
          (pieceTargetParam (pieceAt ⟨e, ⟨n, k⟩⟩)).1 =
            (cutList e n)[k.1 + 1]'hk1 := by
        simpa [hnum] using pieceTargetParam_eq (pieceAt ⟨e, ⟨n, k⟩⟩)
      have hs :
          (pieceSourceParam (pieceAt ⟨e, ⟨n, ⟨k.1 + 1, hgap⟩⟩⟩)).1 =
            (cutList e n)[k.1 + 1]'hk1 := by
        simpa [hnumNext] using
          pieceSourceParam_eq (pieceAt ⟨e, ⟨n, ⟨k.1 + 1, hgap⟩⟩⟩)
      exact ht.trans hs.symm
  · have hk_last : k.1 + 1 = (cutList e n).length - 1 := by
      have hklt : k.1 < (cutList e n).length - 1 := k.2
      omega
    by_cases hseg : n.1 + 1 < (E[e.1]'e.2).1.vertices.length - 1
    · let nNext : Fin ((E[e.1]'e.2).1.vertices.length - 1) :=
        ⟨n.1 + 1, hseg⟩
      have hnext_len_two : 2 ≤ (cutList e nNext).length := (endpoint_data e nNext).1
      have hkFirst_pos : 0 < (cutList e nNext).length - 1 := by
        omega
      let kFirst : Fin ((cutList e nNext).length - 1) :=
        ⟨0, hkFirst_pos⟩
      let oNext : OrderIndex := ⟨e, ⟨nNext, kFirst⟩⟩
      refine ⟨oNext, Or.inr (Or.inl ?_)⟩
      dsimp [oNext, nNext, kFirst]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rfl
      · dsimp [pieceAt]
      · have hnum := pieceAt_number ⟨e, ⟨n, k⟩⟩
        have hlast_lt : (cutList e n).length - 1 < (cutList e n).length := by
          have hlen_two : 2 ≤ (cutList e n).length := (endpoint_data e n).1
          omega
        have ht :
            (pieceTargetParam (pieceAt ⟨e, ⟨n, k⟩⟩)).1 =
              (cutList e n)[(cutList e n).length - 1]'hlast_lt := by
          simpa [hnum, hk_last] using pieceTargetParam_eq (pieceAt ⟨e, ⟨n, k⟩⟩)
        exact ht.trans ((endpoint_data e n).2.2 hlast_lt)
      · have hnumNext := pieceAt_number
          ⟨e, ⟨(⟨n.1 + 1, hseg⟩ : Fin ((E[e.1]'e.2).1.vertices.length - 1)),
            (⟨0, hkFirst_pos⟩ : Fin ((cutList e
              (⟨n.1 + 1, hseg⟩ : Fin ((E[e.1]'e.2).1.vertices.length - 1))).length - 1))⟩⟩
        have hpos : 0 < (cutList e
            (⟨n.1 + 1, hseg⟩ : Fin ((E[e.1]'e.2).1.vertices.length - 1))).length := by
          have hlen_two := (endpoint_data e
            (⟨n.1 + 1, hseg⟩ : Fin ((E[e.1]'e.2).1.vertices.length - 1))).1
          omega
        have hs :
            (pieceSourceParam
              (pieceAt ⟨e, ⟨(⟨n.1 + 1, hseg⟩ :
                Fin ((E[e.1]'e.2).1.vertices.length - 1)),
                (⟨0, hkFirst_pos⟩ : Fin ((cutList e
                  (⟨n.1 + 1, hseg⟩ :
                    Fin ((E[e.1]'e.2).1.vertices.length - 1))).length - 1))⟩⟩)).1 =
              (cutList e
                (⟨n.1 + 1, hseg⟩ :
                  Fin ((E[e.1]'e.2).1.vertices.length - 1)))[0]'hpos := by
          simpa [hnumNext] using
            pieceSourceParam_eq
              (pieceAt ⟨e, ⟨(⟨n.1 + 1, hseg⟩ :
                Fin ((E[e.1]'e.2).1.vertices.length - 1)),
                (⟨0, hkFirst_pos⟩ : Fin ((cutList e
                  (⟨n.1 + 1, hseg⟩ :
                    Fin ((E[e.1]'e.2).1.vertices.length - 1))).length - 1))⟩⟩)
        exact hs.trans ((endpoint_data e
          (⟨n.1 + 1, hseg⟩ : Fin ((E[e.1]'e.2).1.vertices.length - 1))).2.1 hpos)
    · have hn_last : n.1 + 2 = (E[e.1]'e.2).1.vertices.length := by
        have hnlt : n.1 < (E[e.1]'e.2).1.vertices.length - 1 := n.2
        omega
      by_cases hedge : e.1 + 1 < E.length
      · let eNext : Fin E.length := ⟨e.1 + 1, hedge⟩
        have hseg_len_next : 0 < (E[eNext.1]'eNext.2).1.vertices.length - 1 := by
          have hlen : 2 ≤ (E[eNext.1]'eNext.2).1.vertices.length :=
            (E[eNext.1]'eNext.2).1.length_ge_two
          omega
        let nFirst : Fin ((E[eNext.1]'eNext.2).1.vertices.length - 1) :=
          ⟨0, hseg_len_next⟩
        have hnext_len_two : 2 ≤ (cutList eNext nFirst).length :=
          (endpoint_data eNext nFirst).1
        have hkFirst_pos : 0 < (cutList eNext nFirst).length - 1 := by
          omega
        let kFirst : Fin ((cutList eNext nFirst).length - 1) := ⟨0, hkFirst_pos⟩
        let oNext : OrderIndex := ⟨eNext, ⟨nFirst, kFirst⟩⟩
        refine ⟨oNext, Or.inr (Or.inr ?_)⟩
        dsimp [oNext, eNext, nFirst, kFirst]
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · have hi := pieceAt_edge ⟨e, ⟨n, k⟩⟩
          have hj := pieceAt_edge
            ⟨(⟨e.1 + 1, hedge⟩ : Fin E.length),
              ⟨(⟨0, hseg_len_next⟩ :
                Fin ((E[(e.1 + 1)]'hedge).1.vertices.length - 1)),
                (⟨0, hkFirst_pos⟩ : Fin ((cutList
                  (⟨e.1 + 1, hedge⟩ : Fin E.length)
                  (⟨0, hseg_len_next⟩ :
                    Fin ((E[(e.1 + 1)]'hedge).1.vertices.length - 1))).length - 1))⟩⟩
          have hsucc := hEsucc e.1 hedge
          rw [hi, hj]
          exact hsucc.symm
        · dsimp [pieceAt]
          exact hn_last
        · dsimp [pieceAt]
        · have hnum := pieceAt_number ⟨e, ⟨n, k⟩⟩
          have hlast_lt : (cutList e n).length - 1 < (cutList e n).length := by
            have hlen_two : 2 ≤ (cutList e n).length := (endpoint_data e n).1
            omega
          have ht :
              (pieceTargetParam (pieceAt ⟨e, ⟨n, k⟩⟩)).1 =
                (cutList e n)[(cutList e n).length - 1]'hlast_lt := by
            simpa [hnum, hk_last] using pieceTargetParam_eq (pieceAt ⟨e, ⟨n, k⟩⟩)
          exact ht.trans ((endpoint_data e n).2.2 hlast_lt)
        · have hnumNext := pieceAt_number
            ⟨(⟨e.1 + 1, hedge⟩ : Fin E.length),
              ⟨(⟨0, hseg_len_next⟩ :
                Fin ((E[(e.1 + 1)]'hedge).1.vertices.length - 1)),
                (⟨0, hkFirst_pos⟩ : Fin ((cutList
                  (⟨e.1 + 1, hedge⟩ : Fin E.length)
                  (⟨0, hseg_len_next⟩ :
                    Fin ((E[(e.1 + 1)]'hedge).1.vertices.length - 1))).length - 1))⟩⟩
          have hpos : 0 < (cutList
              (⟨e.1 + 1, hedge⟩ : Fin E.length)
              (⟨0, hseg_len_next⟩ :
                Fin ((E[(e.1 + 1)]'hedge).1.vertices.length - 1))).length := by
            have hlen_two := (endpoint_data
              (⟨e.1 + 1, hedge⟩ : Fin E.length)
              (⟨0, hseg_len_next⟩ :
                Fin ((E[(e.1 + 1)]'hedge).1.vertices.length - 1))).1
            omega
          have hs :
              (pieceSourceParam
                (pieceAt ⟨(⟨e.1 + 1, hedge⟩ : Fin E.length),
                  ⟨(⟨0, hseg_len_next⟩ :
                    Fin ((E[(e.1 + 1)]'hedge).1.vertices.length - 1)),
                    (⟨0, hkFirst_pos⟩ : Fin ((cutList
                      (⟨e.1 + 1, hedge⟩ : Fin E.length)
                      (⟨0, hseg_len_next⟩ :
                        Fin ((E[(e.1 + 1)]'hedge).1.vertices.length - 1))).length - 1))⟩⟩)).1 =
                (cutList
                  (⟨e.1 + 1, hedge⟩ : Fin E.length)
                  (⟨0, hseg_len_next⟩ :
                    Fin ((E[(e.1 + 1)]'hedge).1.vertices.length - 1)))[0]'hpos := by
            simpa [hnumNext] using
              pieceSourceParam_eq
                (pieceAt ⟨(⟨e.1 + 1, hedge⟩ : Fin E.length),
                  ⟨(⟨0, hseg_len_next⟩ :
                    Fin ((E[(e.1 + 1)]'hedge).1.vertices.length - 1)),
                    (⟨0, hkFirst_pos⟩ : Fin ((cutList
                      (⟨e.1 + 1, hedge⟩ : Fin E.length)
                      (⟨0, hseg_len_next⟩ :
                        Fin ((E[(e.1 + 1)]'hedge).1.vertices.length - 1))).length - 1))⟩⟩)
          exact hs.trans ((endpoint_data
            (⟨e.1 + 1, hedge⟩ : Fin E.length)
            (⟨0, hseg_len_next⟩ :
              Fin ((E[(e.1 + 1)]'hedge).1.vertices.length - 1))).2.1 hpos)
      · let eNext : Fin E.length := ⟨0, hEpos⟩
        have hseg_len_next : 0 < (E[eNext.1]'eNext.2).1.vertices.length - 1 := by
          have hlen : 2 ≤ (E[eNext.1]'eNext.2).1.vertices.length :=
            (E[eNext.1]'eNext.2).1.length_ge_two
          omega
        let nFirst : Fin ((E[eNext.1]'eNext.2).1.vertices.length - 1) :=
          ⟨0, hseg_len_next⟩
        have hnext_len_two : 2 ≤ (cutList eNext nFirst).length :=
          (endpoint_data eNext nFirst).1
        have hkFirst_pos : 0 < (cutList eNext nFirst).length - 1 := by
          omega
        let kFirst : Fin ((cutList eNext nFirst).length - 1) := ⟨0, hkFirst_pos⟩
        let oNext : OrderIndex := ⟨eNext, ⟨nFirst, kFirst⟩⟩
        refine ⟨oNext, Or.inr (Or.inr ?_)⟩
        dsimp [oNext, eNext, nFirst, kFirst]
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · have hi := pieceAt_edge ⟨e, ⟨n, k⟩⟩
          have hj := pieceAt_edge
            ⟨(⟨0, hEpos⟩ : Fin E.length),
              ⟨(⟨0, hseg_len_next⟩ :
                Fin ((E[0]'hEpos).1.vertices.length - 1)),
                (⟨0, hkFirst_pos⟩ : Fin ((cutList
                  (⟨0, hEpos⟩ : Fin E.length)
                  (⟨0, hseg_len_next⟩ :
                    Fin ((E[0]'hEpos).1.vertices.length - 1))).length - 1))⟩⟩
          have he_last : e.1 = E.length - 1 := by
            omega
          have hLast : E.length - 1 < E.length := by omega
          have hwrap := hEwrap hLast hEpos
          rw [hi, hj]
          have heqFin : e = (⟨E.length - 1, hLast⟩ : Fin E.length) := Fin.ext he_last
          simpa [heqFin] using hwrap.symm
        · dsimp [pieceAt]
          exact hn_last
        · dsimp [pieceAt]
        · have hnum := pieceAt_number ⟨e, ⟨n, k⟩⟩
          have hlast_lt : (cutList e n).length - 1 < (cutList e n).length := by
            have hlen_two : 2 ≤ (cutList e n).length := (endpoint_data e n).1
            omega
          have ht :
              (pieceTargetParam (pieceAt ⟨e, ⟨n, k⟩⟩)).1 =
                (cutList e n)[(cutList e n).length - 1]'hlast_lt := by
            simpa [hnum, hk_last] using pieceTargetParam_eq (pieceAt ⟨e, ⟨n, k⟩⟩)
          exact ht.trans ((endpoint_data e n).2.2 hlast_lt)
        · have hnumNext := pieceAt_number
            ⟨(⟨0, hEpos⟩ : Fin E.length),
              ⟨(⟨0, hseg_len_next⟩ :
                Fin ((E[0]'hEpos).1.vertices.length - 1)),
                (⟨0, hkFirst_pos⟩ : Fin ((cutList
                  (⟨0, hEpos⟩ : Fin E.length)
                  (⟨0, hseg_len_next⟩ :
                    Fin ((E[0]'hEpos).1.vertices.length - 1))).length - 1))⟩⟩
          have hpos : 0 < (cutList
              (⟨0, hEpos⟩ : Fin E.length)
              (⟨0, hseg_len_next⟩ :
                Fin ((E[0]'hEpos).1.vertices.length - 1))).length := by
            have hlen_two := (endpoint_data
              (⟨0, hEpos⟩ : Fin E.length)
              (⟨0, hseg_len_next⟩ :
                Fin ((E[0]'hEpos).1.vertices.length - 1))).1
            omega
          have hs :
              (pieceSourceParam
                (pieceAt ⟨(⟨0, hEpos⟩ : Fin E.length),
                  ⟨(⟨0, hseg_len_next⟩ :
                    Fin ((E[0]'hEpos).1.vertices.length - 1)),
                    (⟨0, hkFirst_pos⟩ : Fin ((cutList
                      (⟨0, hEpos⟩ : Fin E.length)
                      (⟨0, hseg_len_next⟩ :
                        Fin ((E[0]'hEpos).1.vertices.length - 1))).length - 1))⟩⟩)).1 =
                (cutList
                  (⟨0, hEpos⟩ : Fin E.length)
                  (⟨0, hseg_len_next⟩ :
                    Fin ((E[0]'hEpos).1.vertices.length - 1)))[0]'hpos := by
            simpa [hnumNext] using
              pieceSourceParam_eq
                (pieceAt ⟨(⟨0, hEpos⟩ : Fin E.length),
                  ⟨(⟨0, hseg_len_next⟩ :
                    Fin ((E[0]'hEpos).1.vertices.length - 1)),
                    (⟨0, hkFirst_pos⟩ : Fin ((cutList
                      (⟨0, hEpos⟩ : Fin E.length)
                      (⟨0, hseg_len_next⟩ :
                        Fin ((E[0]'hEpos).1.vertices.length - 1))).length - 1))⟩⟩)
          exact hs.trans ((endpoint_data
            (⟨0, hEpos⟩ : Fin E.length)
            (⟨0, hseg_len_next⟩ :
              Fin ((E[0]'hEpos).1.vertices.length - 1))).2.1 hpos)
