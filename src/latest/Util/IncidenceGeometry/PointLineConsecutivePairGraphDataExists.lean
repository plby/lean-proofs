import Util.IncidenceGeometry.PointLineConsecutivePairGraphData
import Util.IncidenceGeometry.PointLineConsecutivePairLineFamilyDataExists

open Classical
noncomputable section

lemma PointLineConsecutivePairGraphDataExists
    (P : Finset (EuclideanSpace ℝ (Fin 2)))
    (L : Finset {ell : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)) //
      IsAffineLine ell}) :
    Nonempty (PointLineConsecutivePairGraphData P L) := by
  obtain ⟨A⟩ := PointLineConsecutivePairLineFamilyDataExists P L
  let indexedEdges : Finset (Σ _ell : A.retainedLines, P × P) :=
    (Finset.univ : Finset A.retainedLines).sigma A.localEdges
  let endpoint : (Σ _ell : A.retainedLines, P × P) → Sym2 P :=
    fun i ↦ Sym2.mk i.2.1 i.2.2
  have indexed_mem (i : Σ _ell : A.retainedLines, P × P) :
      i ∈ indexedEdges ↔ i.2 ∈ A.localEdges i.1 := by
    simp [indexedEdges]
  have line_eq_of_two_points :
      ∀ (ell mu : A.retainedLines) (p q : P),
        (p.1 : EuclideanSpace ℝ (Fin 2)) ∈ ell.1.1 →
        (q.1 : EuclideanSpace ℝ (Fin 2)) ∈ ell.1.1 →
        (p.1 : EuclideanSpace ℝ (Fin 2)) ∈ mu.1.1 →
        (q.1 : EuclideanSpace ℝ (Fin 2)) ∈ mu.1.1 →
        p ≠ q → ell = mu := by
    intro ell mu p q hpell hqell hpmu hqmu hpq
    have hpq' : (p.1 : EuclideanSpace ℝ (Fin 2)) ≠ q.1 := by
      intro h
      exact hpq (Subtype.ext h)
    let linepq : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)) :=
      affineSpan ℝ ({p.1, q.1} : Set (EuclideanSpace ℝ (Fin 2)))
    have line_le_ell : linepq ≤ ell.1.1 :=
      affineSpan_le.2 (by
        intro z hz
        rcases hz with (rfl | hz)
        · exact hpell
        · simpa only [Set.mem_singleton_iff] using hz ▸ hqell)
    have line_le_mu : linepq ≤ mu.1.1 :=
      affineSpan_le.2 (by
        intro z hz
        rcases hz with (rfl | hz)
        · exact hpmu
        · simpa only [Set.mem_singleton_iff] using hz ▸ hqmu)
    have line_rank : Module.finrank ℝ linepq.direction = 1 := by
      rw [direction_affineSpan, vectorSpan_pair]
      exact finrank_span_singleton (vsub_ne_zero.2 hpq')
    have dir_ell : linepq.direction = ell.1.1.direction :=
      Submodule.eq_of_le_of_finrank_eq
        (AffineSubspace.direction_le line_le_ell)
        (line_rank.trans ell.1.2.2.symm)
    have dir_mu : linepq.direction = mu.1.1.direction :=
      Submodule.eq_of_le_of_finrank_eq
        (AffineSubspace.direction_le line_le_mu)
        (line_rank.trans mu.1.2.2.symm)
    have hline : ell.1.1 = mu.1.1 :=
      AffineSubspace.ext_of_direction_eq (dir_ell.symm.trans dir_mu)
        ⟨p.1, hpell, hpmu⟩
    exact Subtype.ext (Subtype.ext hline)
  have endpoint_inj_on : Set.InjOn endpoint indexedEdges := by
    intro i hi j hj hendpoint
    rcases i with ⟨ell, e⟩
    rcases j with ⟨mu, f⟩
    have he : e ∈ A.localEdges ell :=
      (indexed_mem ⟨ell, e⟩).mp hi
    have hf : f ∈ A.localEdges mu :=
      (indexed_mem ⟨mu, f⟩).mp hj
    have hespec := (A.localEdges_mem_iff ell e.1 e.2).mp he
    have hfspec := (A.localEdges_mem_iff mu f.1 f.2).mp hf
    change Sym2.mk e.1 e.2 = Sym2.mk f.1 f.2 at hendpoint
    rcases (Sym2.eq_iff).mp hendpoint with hdirect | hswapped
    · have hell : ell = mu := line_eq_of_two_points ell mu e.1 e.2
          hespec.1 hespec.2.1
          (by simpa [hdirect.1] using hfspec.1)
          (by simpa [hdirect.2] using hfspec.2.1)
          (by
            intro heq
            exact (ne_of_lt hespec.2.2.1)
              (congrArg (fun p : P ↦ A.coordinate ell p.1) heq))
      cases hell
      have hef : e = f := Prod.ext hdirect.1 hdirect.2
      cases hef
      rfl
    · have hell : ell = mu := line_eq_of_two_points ell mu e.1 e.2
          hespec.1 hespec.2.1
          (by simpa [hswapped.1] using hfspec.2.1)
          (by simpa [hswapped.2] using hfspec.1)
          (by
            intro heq
            exact (ne_of_lt hespec.2.2.1)
              (congrArg (fun p : P ↦ A.coordinate ell p.1) heq))
      cases hell
      have hreverse :
          A.coordinate ell e.2.1 < A.coordinate ell e.1.1 := by
        calc
          A.coordinate ell e.2.1 = A.coordinate ell f.1.1 :=
            congrArg (fun p : P ↦ A.coordinate ell p.1) hswapped.2
          _ < A.coordinate ell f.2.1 := hfspec.2.2.1
          _ = A.coordinate ell e.1.1 :=
            congrArg (fun p : P ↦ A.coordinate ell p.1) hswapped.1.symm
      exact False.elim (lt_asymm hespec.2.2.1 hreverse)
  have endpoint_nondiag : ∀ i ∈ indexedEdges, ¬(endpoint i).IsDiag := by
    intro i hi
    have hispec := (A.localEdges_mem_iff i.1 i.2.1 i.2.2).mp
      ((indexed_mem i).mp hi)
    change ¬(Sym2.mk i.2.1 i.2.2).IsDiag
    rw [Sym2.mk_isDiag_iff]
    intro heq
    exact (ne_of_lt hispec.2.2.1)
      (congrArg (fun p : P ↦ A.coordinate i.1 p.1) heq)
  let endpointImage : Finset (Sym2 P) := indexedEdges.image endpoint
  let G : SimpleGraph P := SimpleGraph.fromEdgeSet (endpointImage : Set (Sym2 P))
  letI : Fintype G.edgeSet := G.fintypeEdgeSet
  have edgeFinset_eq : G.edgeFinset = endpointImage := by
    ext e
    constructor
    · intro he
      have heSet : e ∈ G.edgeSet := SimpleGraph.mem_edgeFinset.mp he
      have heDiff : e ∈ (endpointImage : Set (Sym2 P)) \ Sym2.diagSet := by
        simpa [G] using heSet
      exact heDiff.1
    · intro he
      have hnotdiag : ¬e.IsDiag := by
        change e ∈ indexedEdges.image endpoint at he
        rcases Finset.mem_image.mp he with ⟨i, hi, rfl⟩
        exact endpoint_nondiag i hi
      apply SimpleGraph.mem_edgeFinset.mpr
      have heSet : e ∈
          (SimpleGraph.fromEdgeSet (endpointImage : Set (Sym2 P))).edgeSet := by
        rw [SimpleGraph.edgeSet_fromEdgeSet]
        exact ⟨by simpa using he, by simpa using hnotdiag⟩
      simpa [G] using heSet
  have rep_exists : ∀ e : G.edgeFinset,
      ∃ i ∈ indexedEdges, endpoint i = e.1 := by
    intro e
    have he : e.1 ∈ endpointImage := by
      simpa only [edgeFinset_eq] using e.2
    change e.1 ∈ indexedEdges.image endpoint at he
    exact Finset.mem_image.mp he
  let rep : G.edgeFinset → (Σ _ell : A.retainedLines, P × P) :=
    fun e ↦ (rep_exists e).choose
  have rep_mem : ∀ e : G.edgeFinset, rep e ∈ indexedEdges := by
    intro e
    exact (rep_exists e).choose_spec.1
  have rep_endpoint : ∀ e : G.edgeFinset, endpoint (rep e) = e.1 := by
    intro e
    exact (rep_exists e).choose_spec.2
  have rep_local_mem : ∀ e : G.edgeFinset,
      (rep e).2 ∈ A.localEdges (rep e).1 := by
    intro e
    exact (indexed_mem (rep e)).mp (rep_mem e)
  let owner : G.edgeFinset → A.retainedLines := fun e ↦ (rep e).1
  let sourceVertex : G.edgeFinset → P := fun e ↦ (rep e).2.1
  let targetVertex : G.edgeFinset → P := fun e ↦ (rep e).2.2
  have edge_eq (e : G.edgeFinset) :
      e.1 = Sym2.mk (sourceVertex e) (targetVertex e) := by
    calc
      e.1 = endpoint (rep e) := (rep_endpoint e).symm
      _ = Sym2.mk (sourceVertex e) (targetVertex e) := rfl
  have rep_pair_ne : ∀ {e₁ e₂ : G.edgeFinset}, e₁ ≠ e₂ →
      (rep e₁).2 ≠ (rep e₂).2 := by
    intro e₁ e₂ hne hpairs
    apply hne
    apply Subtype.ext
    calc
      e₁.1 = endpoint (rep e₁) := (rep_endpoint e₁).symm
      _ = endpoint (rep e₂) := by simp [endpoint, hpairs]
      _ = e₂.1 := rep_endpoint e₂
  have incidence_retained :
      LineIncidences P L =
        ∑ ell : A.retainedLines, (P.filter (fun p =>
          p ∈ (ell.1.1 : AffineSubspace ℝ
            (EuclideanSpace ℝ (Fin 2))))).card := by
    let fiberCard :
        {ell : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)) //
          IsAffineLine ell} → ℕ := fun ell =>
      (P.filter (fun p => p ∈
        (ell.1 : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))))).card
    have hinc : LineIncidences P L = ∑ ell ∈ L, fiberCard ell := by
      simp only [fiberCard]
      rw [LineIncidences, Finset.card_eq_sum_ones, Finset.sum_filter,
        show P.product L = P ×ˢ L by rfl]
      rw [Finset.sum_product]
      simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
      rw [Finset.sum_comm]
    calc
      LineIncidences P L = ∑ ell ∈ L, fiberCard ell := hinc
      _ = ∑ ell ∈ A.retainedLines, fiberCard ell := by
        symm
        apply Finset.sum_subset
        · intro ell hell
          exact (A.retainedLines_mem_iff ell).mp hell |>.1
        · intro ell hell hnot
          have hno : ¬∃ p : P,
              (p.1 : EuclideanSpace ℝ (Fin 2)) ∈
                (ell.1 : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))) := by
            intro hex
            exact hnot ((A.retainedLines_mem_iff ell).mpr ⟨hell, hex⟩)
          apply Finset.card_eq_zero.mpr
          apply Finset.filter_eq_empty_iff.mpr
          intro p hp hpline
          exact hno ⟨⟨p, hp⟩, hpline⟩
      _ = ∑ ell : A.retainedLines, fiberCard ell.1 := by
        exact Finset.sum_subtype A.retainedLines (fun _ ↦ Iff.rfl) fiberCard
      _ = ∑ ell : A.retainedLines, (P.filter (fun p =>
          p ∈ (ell.1.1 : AffineSubspace ℝ
            (EuclideanSpace ℝ (Fin 2))))).card := by
        rfl
  have indexed_count :
      indexedEdges.card + A.retainedLines.card =
        ∑ ell : A.retainedLines, (P.filter (fun p =>
          p ∈ (ell.1.1 : AffineSubspace ℝ
            (EuclideanSpace ℝ (Fin 2))))).card := by
    calc
      indexedEdges.card + A.retainedLines.card =
          (∑ ell : A.retainedLines, (A.localEdges ell).card) +
            ∑ _ell : A.retainedLines, 1 := by
        simp [indexedEdges, Finset.card_sigma]
      _ = ∑ ell : A.retainedLines, ((A.localEdges ell).card + 1) := by
        rw [Finset.sum_add_distrib]
      _ = ∑ ell : A.retainedLines, (P.filter (fun p =>
          p ∈ (ell.1.1 : AffineSubspace ℝ
            (EuclideanSpace ℝ (Fin 2))))).card := by
        apply Finset.sum_congr rfl
        intro ell _
        exact A.localEdges_card_add_one ell
  have graph_card : G.edgeFinset.card = indexedEdges.card := by
    rw [edgeFinset_eq]
    exact Finset.card_image_iff.mpr endpoint_inj_on
  refine ⟨{
    retainedLines := A.retainedLines
    retainedLines_subset := by
      intro ell hell
      exact (A.retainedLines_mem_iff ell).mp hell |>.1
    retainedLine_incident := by
      intro ell hell
      exact (A.retainedLines_mem_iff ell).mp hell |>.2
    graph := G
    edgeOwner := owner
    edgeSourceVertex := sourceVertex
    edgeTargetVertex := targetVertex
    edge_adjacent := by
      intro e
      rw [← SimpleGraph.mem_edgeSet, ← edge_eq e]
      exact SimpleGraph.mem_edgeFinset.mp e.2
    edge_eq_mk := edge_eq
    edge_source_on_owner := by
      intro e
      exact ((A.localEdges_mem_iff (rep e).1 (rep e).2.1 (rep e).2.2).mp
        (rep_local_mem e)).1
    edge_target_on_owner := by
      intro e
      exact ((A.localEdges_mem_iff (rep e).1 (rep e).2.1 (rep e).2.2).mp
        (rep_local_mem e)).2.1
    edge_no_point_in_openSegment := by
      intro e p
      exact A.localEdge_no_point_in_openSegment (rep e).1 (rep e).2
        (rep_local_mem e) p
    same_owner_openSegment_disjoint := by
      intro e₁ e₂ hne howner
      change (rep e₁).1 = (rep e₂).1 at howner
      have he₂ : (rep e₂).2 ∈ A.localEdges (rep e₁).1 := by
        rw [howner]
        exact rep_local_mem e₂
      exact A.distinct_localEdges_openSegment_disjoint (rep e₁).1
        (rep e₁).2 (rep e₂).2 (rep_local_mem e₁) he₂
        (rep_pair_ne hne)
    same_owner_segment_intersection_subsingleton := by
      intro e₁ e₂ hne howner
      change (rep e₁).1 = (rep e₂).1 at howner
      have he₂ : (rep e₂).2 ∈ A.localEdges (rep e₁).1 := by
        rw [howner]
        exact rep_local_mem e₂
      exact A.distinct_localEdges_segment_intersection_subsingleton (rep e₁).1
        (rep e₁).2 (rep e₂).2 (rep_local_mem e₁) he₂
        (rep_pair_ne hne)
    incidence_eq := by
      calc
        LineIncidences P L =
            ∑ ell : A.retainedLines, (P.filter (fun p =>
              p ∈ (ell.1.1 : AffineSubspace ℝ
                (EuclideanSpace ℝ (Fin 2))))).card := incidence_retained
        _ = indexedEdges.card + A.retainedLines.card := indexed_count.symm
        _ = G.edgeFinset.card + A.retainedLines.card := by omega
  }⟩
