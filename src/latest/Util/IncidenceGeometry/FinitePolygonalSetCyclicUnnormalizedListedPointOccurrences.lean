import Util.IncidenceGeometry.FinitePolygonalSetCyclicListedPointOnElementarySegment
import Util.IncidenceGeometry.FiniteSortedRealCutListEndpointEntries

open Classical
noncomputable section

lemma FinitePolygonalSetCyclicUnnormalizedListedPointOccurrences
    (J : SimpleClosedPolygonalCurve) (K : FinitePolygonalSet)
    (hKJ : K.carrier = J.carrier)
    (E : List {γ : PolygonalArc // γ ∈ J.edgeArcs})
    (hEall : ∀ γ : {γ : PolygonalArc // γ ∈ J.edgeArcs}, γ ∈ E)
    (segmentIndex_lt :
      (e : Fin E.length) →
        (n : Fin ((E[e.1]'e.2).1.vertices.length - 1)) →
          n.1 + 1 < (E[e.1]'e.2).1.vertices.length)
    (cutList :
      (e : Fin E.length) →
        Fin ((E[e.1]'e.2).1.vertices.length - 1) → List ℝ)
    (cutList_sorted : ∀ e n, (cutList e n).SortedLT)
    (cutList_mem :
      ∀ e n (t : ℝ), t ∈ cutList e n ↔
        t = 0 ∨ t = 1 ∨
          (0 ≤ t ∧ t ≤ 1 ∧
            AffineMap.lineMap
              ((E[e.1]'e.2).1.vertices[n.1]'
                (Nat.lt_of_succ_lt (segmentIndex_lt e n)))
              ((E[e.1]'e.2).1.vertices[n.1 + 1]'
                (segmentIndex_lt e n)) t ∈ K.points))
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
            (pieceNumber_lt i))
    (pieceSource :
      (Sigma (fun e : Fin E.length =>
        Sigma (fun n : Fin ((E[e.1]'e.2).1.vertices.length - 1) =>
          localPieceIndex e n))) → EuclideanSpace ℝ (Fin 2))
    (pieceTarget :
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
            (pieceSourceParam i).1)
    (pieceTarget_eq :
      ∀ i : Sigma (fun e : Fin E.length =>
        Sigma (fun n : Fin ((E[e.1]'e.2).1.vertices.length - 1) =>
          localPieceIndex e n)),
        pieceTarget i =
          AffineMap.lineMap
            ((E[i.1.1]'i.1.2).1.vertices[i.2.1.1]'
              (Nat.lt_of_succ_lt (segmentIndex_lt i.1 i.2.1)))
            ((E[i.1.1]'i.1.2).1.vertices[i.2.1.1 + 1]'
              (segmentIndex_lt i.1 i.2.1))
            (pieceTargetParam i).1)
    (pieceStream :
      List (Sigma (fun e : Fin E.length =>
        Sigma (fun n : Fin ((E[e.1]'e.2).1.vertices.length - 1) =>
          localPieceIndex e n))))
    (pieceStream_mem :
      ∀ i : Sigma (fun e : Fin E.length =>
        Sigma (fun n : Fin ((E[e.1]'e.2).1.vertices.length - 1) =>
          localPieceIndex e n)),
        i ∈ pieceStream) :
    ∃ occurrenceList : List (EuclideanSpace ℝ (Fin 2)),
      occurrenceList =
        List.flatMap (fun i =>
          (if pieceSource i ∈ K.points then [pieceSource i] else []) ++
          (if pieceTarget i ∈ K.points then [pieceTarget i] else []))
          pieceStream ∧
        (∀ q, q ∈ occurrenceList → q ∈ K.points) ∧
          (∀ p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points},
            p.1 ∈ occurrenceList) := by
  classical
  let occurrenceList : List (EuclideanSpace ℝ (Fin 2)) :=
    List.flatMap (fun i =>
      (if pieceSource i ∈ K.points then [pieceSource i] else []) ++
      (if pieceTarget i ∈ K.points then [pieceTarget i] else []))
      pieceStream
  refine ⟨occurrenceList, rfl, ?_, ?_⟩
  · intro q hq
    dsimp [occurrenceList] at hq
    rw [List.mem_flatMap] at hq
    rcases hq with ⟨i, _hi, hqinner⟩
    rw [List.mem_append] at hqinner
    rcases hqinner with hqsource | hqtarget
    · by_cases hs : pieceSource i ∈ K.points
      · simp [hs] at hqsource
        simpa [hqsource] using hs
      · simp [hs] at hqsource
    · by_cases ht : pieceTarget i ∈ K.points
      · simp [ht] at hqtarget
        simpa [hqtarget] using ht
      · simp [ht] at hqtarget
  · intro p
    rcases FinitePolygonalSetCyclicListedPointOnElementarySegment J K hKJ p with
      ⟨γ, n, hn, hpseg⟩
    rcases List.getElem_of_mem (hEall γ) with ⟨eNat, heLen, hEγ⟩
    subst γ
    let e : Fin E.length := ⟨eNat, heLen⟩
    have hnE : n + 1 < (E[e.1]'e.2).1.vertices.length := by
      simpa [e] using hn
    let nFin : Fin ((E[e.1]'e.2).1.vertices.length - 1) :=
      ⟨n, by
        have := hnE
        omega⟩
    have hpsegE :
        p.1 ∈ segment ℝ
          ((E[e.1]'e.2).1.vertices[nFin.1]'
            (Nat.lt_of_succ_lt (segmentIndex_lt e nFin)))
          ((E[e.1]'e.2).1.vertices[nFin.1 + 1]'
            (segmentIndex_lt e nFin)) := by
      simpa [e, nFin] using hpseg
    rw [segment_eq_image_lineMap] at hpsegE
    rcases hpsegE with ⟨t, htIcc, htline⟩
    have htmem : t ∈ cutList e nFin := by
      rw [cutList_mem e nFin t]
      right
      right
      exact ⟨htIcc.1, htIcc.2, by simp [htline, p.2]⟩
    rcases List.getElem_of_mem htmem with ⟨r, hrLen, hrt⟩
    by_cases hr0 : r = 0
    · have hlen_two : 2 ≤ (cutList e nFin).length :=
        (FiniteSortedRealCutListEndpointEntries
          (cutList e nFin) (cutList_sorted e nFin)
          (cutList_zero e nFin) (cutList_one e nFin)
          (cutList_bounds e nFin)).1
      have hk : 0 + 1 < (cutList e nFin).length := by omega
      rcases pieceNumber_surjective e nFin 0 hk with ⟨a, ha⟩
      let i : Sigma (fun e : Fin E.length =>
          Sigma (fun n : Fin ((E[e.1]'e.2).1.vertices.length - 1) =>
            localPieceIndex e n)) := ⟨e, ⟨nFin, a⟩⟩
      have hiStream : i ∈ pieceStream := pieceStream_mem i
      have hsource_param : (pieceSourceParam i).1 = t := by
        have hget : (cutList e nFin)[pieceNumber i]'
            (Nat.lt_of_succ_lt (pieceNumber_lt i)) = t := by
          simpa [i, ha, hr0] using hrt
        exact (pieceSourceParam_eq i).trans hget
      have hsource : pieceSource i = p.1 := by
        rw [pieceSource_eq i, hsource_param]
        simpa [i] using htline
      have hsListed : pieceSource i ∈ K.points := by
        simp [hsource, p.2]
      dsimp [occurrenceList]
      rw [List.mem_flatMap]
      refine ⟨i, hiStream, ?_⟩
      rw [List.mem_append]
      left
      simp [hsource, p.2]
    · let k : ℕ := r - 1
      have hk_succ : k + 1 = r := by
        dsimp [k]
        omega
      have hk : k + 1 < (cutList e nFin).length := by
        simpa [hk_succ] using hrLen
      rcases pieceNumber_surjective e nFin k hk with ⟨a, ha⟩
      let i : Sigma (fun e : Fin E.length =>
          Sigma (fun n : Fin ((E[e.1]'e.2).1.vertices.length - 1) =>
            localPieceIndex e n)) := ⟨e, ⟨nFin, a⟩⟩
      have hiStream : i ∈ pieceStream := pieceStream_mem i
      have htarget_param : (pieceTargetParam i).1 = t := by
        have hget : (cutList e nFin)[pieceNumber i + 1]'
            (pieceNumber_lt i) = t := by
          simpa [i, ha, hk_succ] using hrt
        exact (pieceTargetParam_eq i).trans hget
      have htarget : pieceTarget i = p.1 := by
        rw [pieceTarget_eq i, htarget_param]
        simpa [i] using htline
      have htListed : pieceTarget i ∈ K.points := by
        simp [htarget, p.2]
      dsimp [occurrenceList]
      rw [List.mem_flatMap]
      refine ⟨i, hiStream, ?_⟩
      rw [List.mem_append]
      right
      simp [htarget, p.2]
