import Util.IncidenceGeometry.OrdinaryCleanLocalCrossing

open Classical
noncomputable section


lemma OrdinaryCleanLocalCrossingOfOpenSegments {ι : Type*} [Fintype ι]
    (Γ : ι → PolygonalArc) (i j : ι) (p : EuclideanSpace ℝ (Fin 2))
    (hij : i ≠ j)
    (hpi : p ∈ (Γ i).relativeInterior)
    (hpj : p ∈ (Γ j).relativeInterior)
    (hnoTriple :
      ∀ ⦃i j k : ι⦄ ⦃q : EuclideanSpace ℝ (Fin 2)⦄,
        i ≠ j → i ≠ k → j ≠ k →
          q ∈ (Γ i).relativeInterior →
            q ∈ (Γ j).relativeInterior →
              q ∈ (Γ k).relativeInterior → False)
    (hendpoint_free :
      ∀ k : ι, p ≠ (Γ k).source ∧ p ≠ (Γ k).target)
    (hunique :
      ∀ ⦃q : EuclideanSpace ℝ (Fin 2)⦄,
        q ∈ (Γ i).relativeInterior → q ∈ (Γ j).relativeInterior → q = p)
    (m n : ℕ)
    (hm : m + 1 < (Γ i).vertices.length)
    (hn : n + 1 < (Γ j).vertices.length)
    (hpm : p ∈ openSegment ℝ (Γ i).vertices[m] (Γ i).vertices[m + 1])
    (hpn : p ∈ openSegment ℝ (Γ j).vertices[n] (Γ j).vertices[n + 1])
    (hnonparallel :
      ¬ ∃ t : ℝ,
        (Γ j).vertices[n + 1] - (Γ j).vertices[n] =
          t • ((Γ i).vertices[m + 1] - (Γ i).vertices[m])) :
    ∃ C : OrdinaryCleanLocalCrossing Γ i j p,
      C.firstIndex = m ∧ C.secondIndex = n := by
  have hnot_vertex :
      ∀ (k : ι) (s : ℕ) (hs : s + 1 < (Γ k).vertices.length),
        p ∈ openSegment ℝ (Γ k).vertices[s] (Γ k).vertices[s + 1] →
          p ∉ (Γ k).vertices := by
    intro k s hs hpopen hpmem
    obtain ⟨q, hq_lt, hqeq⟩ := List.mem_iff_getElem.mp hpmem
    have hend_ne : (Γ k).vertices[s] ≠ (Γ k).vertices[s + 1] := by
      have hrel := (Γ k).simple_vertices.rel_get_of_lt
        (a := ⟨s, by omega⟩) (b := ⟨s + 1, by omega⟩) (by simp)
      simpa [List.get_eq_getElem] using hrel
    by_cases hqs : q = s
    · have hp_eq : p = (Γ k).vertices[s] := by simpa [hqs] using hqeq.symm
      have hleft :
          (Γ k).vertices[s] ∈
            openSegment ℝ (Γ k).vertices[s] (Γ k).vertices[s + 1] := by
        simpa [hp_eq] using hpopen
      exact hend_ne (left_mem_openSegment_iff.mp hleft)
    by_cases hqs1 : q = s + 1
    · have hp_eq : p = (Γ k).vertices[s + 1] := by simpa [hqs1] using hqeq.symm
      have hright :
          (Γ k).vertices[s + 1] ∈
            openSegment ℝ (Γ k).vertices[s] (Γ k).vertices[s + 1] := by
        simpa [hp_eq] using hpopen
      exact hend_ne (right_mem_openSegment_iff.mp hright)
    exact (Γ k).vertices_avoid_nonincident_interiors hs hq_lt hqs hqs1
      (by simpa [hqeq] using hpopen)
  have hp_not_i : p ∉ (Γ i).vertices := hnot_vertex i m hm hpm
  have hp_not_j : p ∉ (Γ j).vertices := hnot_vertex j n hn hpn
  let Edge := Σ k : ι, Fin ((Γ k).vertices.length - 1)
  let : Fintype Edge := Sigma.instFintype
  let edgeSet : Edge → Set (EuclideanSpace ℝ (Fin 2)) := fun e =>
    segment ℝ
      ((Γ e.1).vertices.get ⟨e.2.1, by have := e.2.2; omega⟩)
      ((Γ e.1).vertices.get ⟨e.2.1 + 1, by have := e.2.2; omega⟩)
  let ei : Edge := ⟨i, ⟨m, by omega⟩⟩
  let ej : Edge := ⟨j, ⟨n, by omega⟩⟩
  let other : Finset Edge := (Finset.univ.erase ei).erase ej
  let forbidden : Set (EuclideanSpace ℝ (Fin 2)) :=
    ⋃ e ∈ other, edgeSet e
  have hedge_closed : ∀ e : Edge, IsClosed (edgeSet e) := by
    intro e
    dsimp [edgeSet]
    rw [← convexHull_pair]
    exact ((Set.finite_singleton _).insert _).isClosed_convexHull ℝ
  have hforbidden_closed : IsClosed forbidden := by
    exact isClosed_biUnion_finset (fun e _ => hedge_closed e)
  have hp_not_forbidden : p ∉ forbidden := by
    intro hpF
    simp only [forbidden, Set.mem_iUnion] at hpF
    obtain ⟨e, he⟩ := hpF
    obtain ⟨he_other, hp_edge⟩ := he
    have he_ne_i : e ≠ ei := by
      intro heq
      subst e
      simpa [other] using he_other
    have he_ne_j : e ≠ ej := by
      intro heq
      subst e
      simpa [other] using he_other
    rcases e with ⟨k, eidx⟩
    have he_bound : eidx.1 + 1 < (Γ k).vertices.length := by
      have := eidx.2
      omega
    have hp_edge' :
        p ∈ segment ℝ (Γ k).vertices[eidx.1]
          (Γ k).vertices[eidx.1 + 1] := by
      simpa [edgeSet] using hp_edge
    by_cases hei : k = i
    · subst k
      have hem : eidx.1 ≠ m := by
        intro hem
        apply he_ne_i
        dsimp [ei]
        apply Sigma.ext
        · rfl
        have hfin : eidx = (⟨m, by omega⟩ : Fin ((Γ i).vertices.length - 1)) := by
          apply Fin.ext
          exact hem
        exact heq_of_eq hfin
      by_cases hlt : eidx.1 < m
      · have hinter := (Γ i).segment_intersections he_bound hm hlt
        have hp_inter :
            p ∈ segment ℝ (Γ i).vertices[eidx.1]
                (Γ i).vertices[eidx.1 + 1] ∩
              segment ℝ (Γ i).vertices[m] (Γ i).vertices[m + 1] :=
          ⟨hp_edge', openSegment_subset_segment ℝ _ _ hpm⟩
        rw [hinter] at hp_inter
        split at hp_inter
        · have hp_eq : p = (Γ i).vertices[m] := by simpa using hp_inter
          exact hp_not_i (by rw [hp_eq]; exact List.getElem_mem _)
        · exact hp_inter
      · have hmt : m < eidx.1 := by omega
        have hinter := (Γ i).segment_intersections hm he_bound hmt
        have hp_inter :
            p ∈ segment ℝ (Γ i).vertices[m] (Γ i).vertices[m + 1] ∩
              segment ℝ (Γ i).vertices[eidx.1]
                (Γ i).vertices[eidx.1 + 1] :=
          ⟨openSegment_subset_segment ℝ _ _ hpm, hp_edge'⟩
        rw [hinter] at hp_inter
        split at hp_inter
        · have hp_eq : p = (Γ i).vertices[eidx.1] := by simpa using hp_inter
          exact hp_not_i (by rw [hp_eq]; exact List.getElem_mem _)
        · exact hp_inter
    by_cases hej : k = j
    · subst k
      have hen : eidx.1 ≠ n := by
        intro hen
        apply he_ne_j
        dsimp [ej]
        apply Sigma.ext
        · rfl
        have hfin : eidx = (⟨n, by omega⟩ : Fin ((Γ j).vertices.length - 1)) := by
          apply Fin.ext
          exact hen
        exact heq_of_eq hfin
      by_cases hlt : eidx.1 < n
      · have hinter := (Γ j).segment_intersections he_bound hn hlt
        have hp_inter :
            p ∈ segment ℝ (Γ j).vertices[eidx.1]
                (Γ j).vertices[eidx.1 + 1] ∩
              segment ℝ (Γ j).vertices[n] (Γ j).vertices[n + 1] :=
          ⟨hp_edge', openSegment_subset_segment ℝ _ _ hpn⟩
        rw [hinter] at hp_inter
        split at hp_inter
        · have hp_eq : p = (Γ j).vertices[n] := by simpa using hp_inter
          exact hp_not_j (by rw [hp_eq]; exact List.getElem_mem _)
        · exact hp_inter
      · have hnt : n < eidx.1 := by omega
        have hinter := (Γ j).segment_intersections hn he_bound hnt
        have hp_inter :
            p ∈ segment ℝ (Γ j).vertices[n] (Γ j).vertices[n + 1] ∩
              segment ℝ (Γ j).vertices[eidx.1]
                (Γ j).vertices[eidx.1 + 1] :=
          ⟨openSegment_subset_segment ℝ _ _ hpn, hp_edge'⟩
        rw [hinter] at hp_inter
        split at hp_inter
        · have hp_eq : p = (Γ j).vertices[eidx.1] := by simpa using hp_inter
          exact hp_not_j (by rw [hp_eq]; exact List.getElem_mem _)
        · exact hp_inter
    have hp_carrier : p ∈ (Γ k).carrier := by
      rw [(Γ k).carrier_eq]
      exact ⟨eidx.1, he_bound, hp_edge'⟩
    have hp_ne_source : p ≠ (Γ k).source := (hendpoint_free k).1
    have hp_ne_target : p ≠ (Γ k).target := (hendpoint_free k).2
    have hp_rel_e : p ∈ (Γ k).relativeInterior := by
      rw [(Γ k).relativeInterior_eq]
      exact ⟨hp_carrier, by simp [hp_ne_source, hp_ne_target]⟩
    exact hnoTriple hij (Ne.symm hei) (Ne.symm hej) hpi hpj hp_rel_e
  have hopen_compl : IsOpen forbiddenᶜ := hforbidden_closed.isOpen_compl
  obtain ⟨ε, hεpos, hεsub⟩ := Metric.isOpen_iff.mp hopen_compl p hp_not_forbidden
  refine ⟨
    { firstIndex := m
      secondIndex := n
      firstIndex_valid := hm
      secondIndex_valid := hn
      first_open := hpm
      second_open := hpn
      first_not_vertex := hp_not_i
      second_not_vertex := hp_not_j
      directions_nonparallel := hnonparallel
      pair_unique := hunique
      radius := ε
      radius_pos := hεpos
      two_branch_neighborhood := ?_ }, rfl, rfl⟩
  ext q
  constructor
  · intro hq
    rcases hq with ⟨hqball, hqfamily⟩
    refine ⟨hqball, ?_⟩
    simp only [Set.mem_iUnion] at hqfamily
    obtain ⟨k, hqk⟩ := hqfamily
    rw [(Γ k).carrier_eq] at hqk
    obtain ⟨s, hs, hqseg⟩ := hqk
    let e : Edge := ⟨k, ⟨s, by omega⟩⟩
    by_cases hei : e = ei
    · left
      have hk : k = i := congrArg Sigma.fst hei
      subst k
      have hs_eq : s = m := congrArg (fun x : Edge => x.2.1) hei
      simpa [hs_eq] using hqseg
    by_cases hej : e = ej
    · right
      have hk : k = j := congrArg Sigma.fst hej
      subst k
      have hs_eq : s = n := congrArg (fun x : Edge => x.2.1) hej
      simpa [hs_eq] using hqseg
    have heother : e ∈ other := by simp [other, hei, hej]
    have hqF : q ∈ forbidden := by
      simp only [forbidden, Set.mem_iUnion]
      exact ⟨e, heother, by simpa [edgeSet, e] using hqseg⟩
    exact False.elim (hεsub hqball hqF)
  · intro hq
    rcases hq with ⟨hqball, hqsegments⟩
    refine ⟨hqball, ?_⟩
    simp only [Set.mem_iUnion]
    rcases hqsegments with hqi | hqj
    · refine ⟨i, ?_⟩
      rw [(Γ i).carrier_eq]
      exact ⟨m, hm, hqi⟩
    · refine ⟨j, ?_⟩
      rw [(Γ j).carrier_eq]
      exact ⟨n, hn, hqj⟩
