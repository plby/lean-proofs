import Util.IncidenceGeometry.PolygonalPath
import Util.IncidenceGeometry.FinitePolygonalSet
import Util.IncidenceGeometry.PolygonalPathInGeneralPosition
import Util.IncidenceGeometry.SingletonPathInGeneralPosition
import Util.IncidenceGeometry.FinitePointLineAvoidance
import Util.IncidenceGeometry.SingleVertexPolygonalScreening
import Util.IncidenceGeometry.FinalVertexPolygonalScreening
import Util.IncidenceGeometry.FiniteAnchorListPolygonalScreening
import Util.IncidenceGeometry.ScreenedVertexListPolygonalPath
import Util.IncidenceGeometry.LocalSubdivisionWindowControl

open Classical
noncomputable section

lemma FinitePolygonalPerturbation (K : FinitePolygonalSet)
    (U : Set (EuclideanSpace ℝ (Fin 2))) (γ : PolygonalPath)
    (A : Set (EuclideanSpace ℝ (Fin 2))) (δ : ℝ) :
    IsOpen U →
      γ.carrier ⊆ U →
        γ.source ∈ U \ K.carrier →
          γ.target ∈ U \ K.carrier →
            0 < δ →
              IsCompact A →
                A ⊆ Uᶜ →
                  ∃ γ' : PolygonalPath,
                    γ'.source = γ.source ∧
                      γ'.target = γ.target ∧
                        γ'.carrier ⊆ U ∧
                          γ'.carrier ⊆
                            {p : EuclideanSpace ℝ (Fin 2) |
                              ∃ q : EuclideanSpace ℝ (Fin 2), q ∈ γ.carrier ∧ dist p q < δ} ∧
                            PolygonalPathInGeneralPosition γ' K ∧
                              Disjoint γ'.carrier A := by
  intro hU hγU hsource htarget hδ hA hAU
  by_cases hsame : γ.source = γ.target
  · obtain ⟨γ', hγ'source, hγ'target, hγ'carrier, hγ'gp⟩ :=
      SingletonPathInGeneralPosition K γ.source hsource.2
    refine ⟨γ', hγ'source, ?_, ?_, ?_, hγ'gp, ?_⟩
    · rw [hγ'target, hsame]
    · rw [hγ'carrier]
      intro p hp
      simp only [Set.mem_singleton_iff] at hp
      exact hp ▸ hsource.1
    · rw [hγ'carrier]
      intro p hp
      simp only [Set.mem_singleton_iff] at hp
      subst p
      refine ⟨γ.source, ?_, ?_⟩
      · rw [γ.carrier_eq]
        left
        simp
      · simpa using hδ
    · rw [hγ'carrier]
      rw [Set.disjoint_left]
      intro p hp hpA
      simp only [Set.mem_singleton_iff] at hp
      have hpU : p ∈ U := hp ▸ hsource.1
      exact hAU hpA hpU
  · let E := EuclideanSpace ℝ (Fin 2)
    let vertexCarrier : List E → Set E := fun xs =>
      ({γ.source, γ.target} : Set E) ∪
        {p : E | ∃ i : ℕ, ∃ hi : i + 1 < xs.length,
          p ∈ segment ℝ xs[i] xs[i + 1]}
    let near : Set E :=
      {p : E | ∃ q : E, q ∈ γ.carrier ∧ dist p q < δ}
    have hlocal_screened :
        ∃ xs : List E,
          xs ≠ [] ∧
            xs.head? = some γ.source ∧
              xs.getLast? = some γ.target ∧
                (∀ v : E, v ∈ xs → v ∉ K.carrier) ∧
                  (∀ (i : ℕ) (hi : i + 1 < xs.length)
                      (p : E), p ∈ K.points → p ∉ segment ℝ xs[i] xs[i + 1]) ∧
                    (∀ (i : ℕ) (hi : i + 1 < xs.length)
                        (s : E × E), s ∈ K.segments →
                          ¬ ∃ p q : E, p ≠ q ∧
                            segment ℝ p q ⊆
                              segment ℝ xs[i] xs[i + 1] ∩ segment ℝ s.1 s.2) ∧
                      (∀ (i : ℕ) (hi : i + 1 < xs.length)
                          (s : E × E) (_hs : s ∈ K.segments) (p : E),
                          p ∈ openSegment ℝ xs[i] xs[i + 1] →
                            p ∈ openSegment ℝ s.1 s.2 →
                              ¬ ∃ c : ℝ,
                                s.2 - s.1 = c • (xs[i + 1] - xs[i])) ∧
                        vertexCarrier xs ⊆ U ∧
                          vertexCarrier xs ⊆ near := by
      -- This is the paper's local subdivision/window step, followed by the
      -- finite screening induction inside those windows.  The previous
      -- global-U four-vertex construction did not provide these controls.
      obtain ⟨ρ, hρpos, hwindowControl⟩ :=
        LocalSubdivisionWindowControl U γ δ hU hγU hδ
      have hseg_vertices :
          ∀ (i : ℕ) (hi : i + 1 < γ.vertices.length),
            segment ℝ γ.vertices[i] γ.vertices[i + 1] ⊆ γ.carrier := by
        intro i hi p hp
        rw [γ.carrier_eq]
        right
        exact ⟨i, hi, hp⟩
      have hanchors_exists :
          ∃ anchors : List E,
            anchors.head? = some γ.source ∧
              anchors.getLast? = some γ.target ∧
                3 ≤ anchors.length ∧
                  (∀ (i : ℕ) (hi : i + 1 < anchors.length),
                    segment ℝ anchors[i] anchors[i + 1] ⊆ γ.carrier) := by
        cases hverts : γ.vertices with
        | nil =>
            exact False.elim (γ.vertices_nonempty hverts)
        | cons v vs =>
            cases hvs : vs with
            | nil =>
                have hhead := γ.source_eq_head
                have hlast := γ.target_eq_last
                rw [hverts, hvs] at hhead hlast
                simp at hhead hlast
                exact False.elim (hsame (hhead.symm.trans hlast))
            | cons w ws =>
                cases hws : ws with
                | nil =>
                    let mid : E := ((1 / 2 : ℝ) • γ.source + (1 / 2 : ℝ) • γ.target)
                    refine ⟨[γ.source, mid, γ.target], ?_, ?_, ?_, ?_⟩
                    · simp
                    · simp
                    · simp
                    · intro i hi p hp
                      have hlen_small : i < 2 := by
                        have hi' : i + 1 < 3 := by simpa using hi
                        omega
                      interval_cases i
                      · have hsource_v : v = γ.source := by
                          have hhead := γ.source_eq_head
                          rw [hverts, hvs] at hhead
                          simp at hhead
                          exact hhead
                        have htarget_w : w = γ.target := by
                          have hlast := γ.target_eq_last
                          rw [hverts, hvs, hws] at hlast
                          simp at hlast
                          exact hlast
                        have hseg_st : segment ℝ γ.source γ.target ⊆ γ.carrier := by
                          intro q hq
                          rw [γ.carrier_eq]
                          right
                          refine ⟨0, ?_, ?_⟩
                          · rw [hverts, hvs, hws]
                            simp
                          · simpa [hverts, hvs, hws, hsource_v, htarget_w] using hq
                        apply hseg_st
                        have hmid : mid ∈ segment ℝ γ.source γ.target := by
                          refine ⟨(1 / 2 : ℝ), (1 / 2 : ℝ), by norm_num, by norm_num, ?_, rfl⟩
                          norm_num
                        exact (convex_segment γ.source γ.target).segment_subset
                          (left_mem_segment ℝ γ.source γ.target) hmid hp
                      · have hsource_v : v = γ.source := by
                          have hhead := γ.source_eq_head
                          rw [hverts, hvs] at hhead
                          simp at hhead
                          exact hhead
                        have htarget_w : w = γ.target := by
                          have hlast := γ.target_eq_last
                          rw [hverts, hvs, hws] at hlast
                          simp at hlast
                          exact hlast
                        have hseg_st : segment ℝ γ.source γ.target ⊆ γ.carrier := by
                          intro q hq
                          rw [γ.carrier_eq]
                          right
                          refine ⟨0, ?_, ?_⟩
                          · rw [hverts, hvs, hws]
                            simp
                          · simpa [hverts, hvs, hws, hsource_v, htarget_w] using hq
                        apply hseg_st
                        have hmid : mid ∈ segment ℝ γ.source γ.target := by
                          refine ⟨(1 / 2 : ℝ), (1 / 2 : ℝ), by norm_num, by norm_num, ?_, rfl⟩
                          norm_num
                        exact (convex_segment γ.source γ.target).segment_subset hmid
                          (right_mem_segment ℝ γ.source γ.target) hp
                | cons z zs =>
                    refine ⟨γ.vertices, γ.source_eq_head, γ.target_eq_last, ?_, hseg_vertices⟩
                    rw [hverts, hvs, hws]
                    simp
      obtain ⟨anchors, hanchors_head, hanchors_last, hanchors_len, hanchors_segments⟩ :=
        hanchors_exists
      have hfinite_screened :
          ∃ xs : List E,
            xs.length = anchors.length ∧
              xs.head? = some γ.source ∧
                xs.getLast? = some γ.target ∧
                  (∀ (i : ℕ) (hxi : i < xs.length) (hai : i < anchors.length),
                    dist xs[i] anchors[i] < ρ) ∧
                    (∀ v : E, v ∈ xs → v ∉ K.carrier) ∧
                      (∀ (i : ℕ) (hi : i + 1 < xs.length)
                          (p : E), p ∈ K.points → p ∉ segment ℝ xs[i] xs[i + 1]) ∧
                        (∀ (i : ℕ) (hi : i + 1 < xs.length)
                            (s : E × E), s ∈ K.segments →
                              ¬ ∃ p q : E, p ≠ q ∧
                                segment ℝ p q ⊆
                                  segment ℝ xs[i] xs[i + 1] ∩ segment ℝ s.1 s.2) ∧
                          (∀ (i : ℕ) (hi : i + 1 < xs.length)
                              (s : E × E) (_hs : s ∈ K.segments) (p : E),
                              p ∈ openSegment ℝ xs[i] xs[i + 1] →
                                p ∈ openSegment ℝ s.1 s.2 →
                                  ¬ ∃ c : ℝ,
                                    s.2 - s.1 = c • (xs[i + 1] - xs[i])) := by
        have hclose0 :
            ∀ _h : 0 < anchors.length, dist γ.source anchors[0] < ρ := by
          intro hlen_pos
          have hanchor0 : anchors[0] = γ.source := by
            cases anchors with
            | nil =>
                simp at hlen_pos
            | cons anchor0 rest =>
                simp at hanchors_head
                simpa using hanchors_head
          rw [hanchor0, dist_self]
          exact hρpos
        exact FiniteAnchorListPolygonalScreening K γ.source γ.target anchors ρ
          hρpos hsource.2 htarget.2 hclose0 hanchors_last hanchors_len
      obtain ⟨xs, hxs_len, hxs_head, hxs_last, hclose, hvertices, hpoints,
          hoverlap, htransverse⟩ := hfinite_screened
      obtain ⟨hxsU, hxsNear⟩ :=
        hwindowControl anchors xs hxs_len hanchors_segments hclose
      have hxs_nonempty : xs ≠ [] := by
        intro hnil
        have hxs_len_zero : xs.length = 0 := by simp [hnil]
        omega
      exact ⟨xs, hxs_nonempty, hxs_head, hxs_last, hvertices, hpoints, hoverlap,
        htransverse, hxsU, hxsNear⟩
    obtain ⟨xs, hxs_nonempty, hxs_head, hxs_last, hvertices, hpoints, hoverlap,
        htransverse, hxsU, hxsNear⟩ := hlocal_screened
    obtain ⟨γ', _hvertices, hγ'source, hγ'target, _hcarrier, hγ'gp⟩ :=
      ScreenedVertexListPolygonalPath K xs γ.source γ.target hxs_nonempty hxs_head hxs_last
        hsource.2 htarget.2 hvertices hpoints hoverlap htransverse
    have hγ'U : γ'.carrier ⊆ U := by
      rw [_hcarrier]
      simpa [vertexCarrier] using hxsU
    have hγ'near : γ'.carrier ⊆
        {p : EuclideanSpace ℝ (Fin 2) |
          ∃ q : EuclideanSpace ℝ (Fin 2), q ∈ γ.carrier ∧ dist p q < δ} := by
      rw [_hcarrier]
      simpa [vertexCarrier, near] using hxsNear
    refine ⟨γ', hγ'source, hγ'target, hγ'U, hγ'near, hγ'gp, ?_⟩
    rw [Set.disjoint_left]
    intro p hpγ hpA
    exact hAU hpA (hγ'U hpγ)
