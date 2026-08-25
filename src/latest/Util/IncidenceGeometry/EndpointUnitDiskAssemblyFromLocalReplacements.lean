import Util.IncidenceGeometry.EndpointUnitChordMultiplePointControl
import Util.IncidenceGeometry.EndpointUnitDiskChordEndpointParameters
import Util.IncidenceGeometry.EndpointUnitDiskChordCenterParameterList
import Util.IncidenceGeometry.EndpointUnitDiskAlternatingVertexListArc
import Util.IncidenceGeometry.EndpointUnitDiskLocalPieceMeetsOnlyIncidentChord
import Util.IncidenceGeometry.EndpointUnitDiskLocalPiecesSameCenter
import Util.IncidenceGeometry.EndpointUnitDiskTriplePointInChosenDisk
import Util.IncidenceGeometry.EndpointUnitMultiplePointDisks
import Util.IncidenceGeometry.PolygonalReplacementStraightSegmentDisjointCutOrder
import Util.IncidenceGeometry.EndpointUnitDiskChordSubsegmentUnitContainment
import Util.IncidenceGeometry.PolygonalArcVertexMemCarrier
import Util.IncidenceGeometry.EndpointUnitDiskAlternatingVertexListEdgeRoles
import Util.IncidenceGeometry.EndpointUnitDiskAlternatingVertexListEdgeEndpointRoles
import Util.IncidenceGeometry.EndpointUnitDiskAlternatingVertexListNodup
import Util.IncidenceGeometry.EndpointUnitDiskOrderedGapDiskIntersections
import Util.IncidenceGeometry.EndpointUnitDiskChordGapCutDiskIntersections
import Util.IncidenceGeometry.OrdinaryCleanLocalCrossingOfOpenSegments


open Classical
noncomputable section

private lemma endpointUnitDiskAssembly_indexUnique
    (Q : PolygonalArc) (q : EuclideanSpace ℝ (Fin 2)) (s t : ℕ)
    (hs : s + 1 < Q.vertices.length)
    (ht : t + 1 < Q.vertices.length)
    (hqopen : q ∈ openSegment ℝ Q.vertices[s] Q.vertices[s + 1])
    (hqseg : q ∈ segment ℝ Q.vertices[t] Q.vertices[t + 1]) :
    s = t := by
  have hq_not_vertex : q ∉ Q.vertices := by
    intro hqmem
    obtain ⟨k, hk, hkeq⟩ := List.mem_iff_getElem.mp hqmem
    have hend_ne : Q.vertices[s] ≠ Q.vertices[s + 1] := by
      have hrel := Q.simple_vertices.rel_get_of_lt
        (a := ⟨s, by omega⟩) (b := ⟨s + 1, by omega⟩) (by simp)
      simpa [List.get_eq_getElem] using hrel
    by_cases hks : k = s
    · have hqeq : q = Q.vertices[s] := by simpa [hks] using hkeq.symm
      have hleft : Q.vertices[s] ∈ openSegment ℝ Q.vertices[s] Q.vertices[s + 1] := by
        simpa [hqeq] using hqopen
      exact hend_ne (left_mem_openSegment_iff.mp hleft)
    by_cases hks1 : k = s + 1
    · have hqeq : q = Q.vertices[s + 1] := by simpa [hks1] using hkeq.symm
      have hright : Q.vertices[s + 1] ∈ openSegment ℝ Q.vertices[s] Q.vertices[s + 1] := by
        simpa [hqeq] using hqopen
      exact hend_ne (right_mem_openSegment_iff.mp hright)
    exact Q.vertices_avoid_nonincident_interiors hs hk hks hks1
      (by simpa [hkeq] using hqopen)
  by_contra hst
  rcases lt_or_gt_of_ne hst with hlt | hgt
  · have hinter := Q.segment_intersections hs ht hlt
    have hqinter :
        q ∈ segment ℝ Q.vertices[s] Q.vertices[s + 1] ∩
          segment ℝ Q.vertices[t] Q.vertices[t + 1] :=
      ⟨openSegment_subset_segment ℝ _ _ hqopen, hqseg⟩
    rw [hinter] at hqinter
    split at hqinter
    · have hqeq : q = Q.vertices[t] := by simpa using hqinter
      exact hq_not_vertex (by rw [hqeq]; exact List.getElem_mem _)
    · exact hqinter
  · have hinter := Q.segment_intersections ht hs hgt
    have hqinter :
        q ∈ segment ℝ Q.vertices[t] Q.vertices[t + 1] ∩
          segment ℝ Q.vertices[s] Q.vertices[s + 1] :=
      ⟨hqseg, openSegment_subset_segment ℝ _ _ hqopen⟩
    rw [hinter] at hqinter
    split at hqinter
    · have hqeq : q = Q.vertices[s] := by simpa using hqinter
      exact hq_not_vertex (by rw [hqeq]; exact List.getElem_mem _)
    · exact hqinter

private lemma endpointUnitDiskAssembly_localEdgeAvoid
    {L : List (EuclideanSpace ℝ (Fin 2))} {Q : PolygonalArc}
    {m k q : ℕ}
    (hm : m + 1 < L.length)
    (hk : k < L.length)
    (hq : q + 1 < Q.vertices.length)
    (hleft : L[m] = Q.vertices[q])
    (hright : L[m + 1] = Q.vertices[q + 1])
    (havoid : L[k] ∉ openSegment ℝ Q.vertices[q] Q.vertices[q + 1])
    {p : EuclideanSpace ℝ (Fin 2)}
    (hp_def : L[k] = p)
    (hpopen : p ∈ openSegment ℝ L[m] L[m + 1]) : False := by
  have hpopen_original :
      L[k] ∈ openSegment ℝ L[m] L[m + 1] := by
    rw [hp_def]
    exact hpopen
  have hpopen_local :
      L[k] ∈ openSegment ℝ Q.vertices[q] Q.vertices[q + 1] := by
    rw [← hleft, ← hright]
    exact hpopen_original
  exact havoid hpopen_local

private lemma endpointUnitDiskAssembly_initialGapAvoidsLaterCarrier
    (A B entry entry' p : EuclideanSpace ℝ (Fin 2))
    (laterArc : PolygonalArc)
    (e t e' sExit sEntry : ℝ)
    (hAB : A ≠ B)
    (he_pos : 0 < e)
    (he_lt_t : e < t)
    (ht_sExit : t < sExit)
    (hsExitEntry : sExit < sEntry)
    (hentry : entry = AffineMap.lineMap A B e)
    (hentry' : entry' = AffineMap.lineMap A B e')
    (hentry_order : entry' = AffineMap.lineMap A B sEntry)
    (hpseg_gap : p ∈ segment ℝ A entry)
    (hp_carrier : p ∈ laterArc.carrier)
    (hposition :
      ∀ ⦃q : EuclideanSpace ℝ (Fin 2)⦄,
        q ∈ segment ℝ (AffineMap.lineMap A B (0 : ℝ))
            (AffineMap.lineMap A B e) →
          q ∈ laterArc.carrier → e < e' → False) : False := by
  have hf : Function.Injective (AffineMap.lineMap A B) :=
    AffineMap.lineMap_injective (k := ℝ) hAB
  have he'_eq : e' = sEntry := by
    exact hf (by rw [← hentry', ← hentry_order])
  have he_lt_e' : e < e' := by
    linarith
  have hpseg_param :
      p ∈ segment ℝ (AffineMap.lineMap A B (0 : ℝ))
          (AffineMap.lineMap A B e) := by
    simpa [hentry] using hpseg_gap
  exact hposition hpseg_param hp_carrier he_lt_e'

private lemma endpointUnitDiskAssembly_assembledVerticesAvoid
    {ι : Type*} [Fintype ι]
    (a b : ι → EuclideanSpace ℝ (Fin 2))
    (centerParams : ι → List ℝ)
    (localArcAtParam :
      ∀ i, {t : ℝ // t ∈ centerParams i} → PolygonalArc)
    (entryPoint exitPoint :
      ∀ i, {t : ℝ // t ∈ centerParams i} → EuclideanSpace ℝ (Fin 2))
    (assembledVertices : ι → List (EuclideanSpace ℝ (Fin 2)))
    (hassembledVertices : ∀ i,
      assembledVertices i =
        [a i] ++
          ((((centerParams i).attach.map
            (fun t => (localArcAtParam i t).vertices)).flatten) ++ [b i]))
    (hendpoint_ne : ∀ i, a i ≠ b i)
    (hcenterParams_sorted : ∀ i, (centerParams i).SortedLT)
    (hentryExitParameters :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}),
        (∃ s : ℝ, 0 < s ∧ s < t.1 ∧
          entryPoint i t = AffineMap.lineMap (a i) (b i) s) ∧
          (∃ s : ℝ, t.1 < s ∧ s < 1 ∧
            exitPoint i t = AffineMap.lineMap (a i) (b i) s))
    (hlocalArcAtParam_endpoints :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}),
        (localArcAtParam i t).source = entryPoint i t ∧
          (localArcAtParam i t).target = exitPoint i t)
    (horderedCutSeparation :
      ∀ i (t1 t2 : {t : ℝ // t ∈ centerParams i}),
        t1.1 < t2.1 →
          ∃ sExit sEntry : ℝ,
            t1.1 < sExit ∧
              sExit < sEntry ∧
                sEntry < t2.1 ∧
                  exitPoint i t1 = AffineMap.lineMap (a i) (b i) sExit ∧
                    entryPoint i t2 = AffineMap.lineMap (a i) (b i) sEntry)
    (hchordGapLocalCarrierPosition :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}) {α β e x : ℝ},
        entryPoint i t = AffineMap.lineMap (a i) (b i) e →
          exitPoint i t = AffineMap.lineMap (a i) (b i) x →
            0 ≤ α → α ≤ β → β ≤ 1 → e < x →
              (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
                p ∈ segment ℝ (AffineMap.lineMap (a i) (b i) α)
                    (AffineMap.lineMap (a i) (b i) β) →
                  p ∈ (localArcAtParam i t).carrier →
                    β < e → False) ∧
                (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
                  p ∈ segment ℝ (AffineMap.lineMap (a i) (b i) α)
                      (AffineMap.lineMap (a i) (b i) β) →
                    p ∈ (localArcAtParam i t).carrier →
                      β = e → p = entryPoint i t) ∧
                  (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
                    p ∈ segment ℝ (AffineMap.lineMap (a i) (b i) α)
                        (AffineMap.lineMap (a i) (b i) β) →
                      p ∈ (localArcAtParam i t).carrier →
                        x < α → False) ∧
                    (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
                      p ∈ segment ℝ (AffineMap.lineMap (a i) (b i) α)
                          (AffineMap.lineMap (a i) (b i) β) →
                        p ∈ (localArcAtParam i t).carrier →
                          x = α → p = exitPoint i t))
    (hinitialGapMeetsLocalCarrierOnly :
      ∀ i (t : {t : ℝ // t ∈ centerParams i})
        ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        p ∈ segment ℝ (a i) (entryPoint i t) →
          p ∈ (localArcAtParam i t).carrier → p = entryPoint i t)
    (hterminalGapMeetsLocalCarrierOnly :
      ∀ i (t : {t : ℝ // t ∈ centerParams i})
        ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        p ∈ segment ℝ (exitPoint i t) (b i) →
          p ∈ (localArcAtParam i t).carrier → p = exitPoint i t)
    (horderedOutsideGapMeetsNeighboringLocalCarriersOnly :
      ∀ i (t1 t2 : {t : ℝ // t ∈ centerParams i}),
        t1.1 < t2.1 →
          (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
            p ∈ segment ℝ (exitPoint i t1) (entryPoint i t2) →
              p ∈ (localArcAtParam i t1).carrier → p = exitPoint i t1) ∧
            (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
              p ∈ segment ℝ (exitPoint i t1) (entryPoint i t2) →
                p ∈ (localArcAtParam i t2).carrier → p = entryPoint i t2))
    (hassembledVertices_nodup : ∀ i, (assembledVertices i).Nodup)
    (hlocalEdgeAvoidsAssembledVertices :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}) ⦃q : ℕ⦄,
        (hq : q + 1 < (localArcAtParam i t).vertices.length) →
          ∀ ⦃k : ℕ⦄, (hk : k < (assembledVertices i).length) →
            (assembledVertices i)[k] ∉
              openSegment ℝ (localArcAtParam i t).vertices[q]
                (localArcAtParam i t).vertices[q + 1])
    (hassembledEdgeEndpointRoles :
      ∀ i ⦃m : ℕ⦄,
        (hm : m + 1 < (assembledVertices i).length) →
          ((centerParams i).attach = [] ∧
              (assembledVertices i)[m] = a i ∧
                (assembledVertices i)[m + 1] = b i) ∨
            (∃ t ts X,
              (centerParams i).attach = t :: ts ∧
                (localArcAtParam i t).vertices.head? = some X ∧
                  (assembledVertices i)[m] = a i ∧
                    (assembledVertices i)[m + 1] = X) ∨
            (∃ (pre : List {t : ℝ // t ∈ centerParams i})
                (t : {t : ℝ // t ∈ centerParams i})
                (post : List {t : ℝ // t ∈ centerParams i}) (q : ℕ),
              ∃ hq : q + 1 < (localArcAtParam i t).vertices.length,
                (centerParams i).attach = pre ++ t :: post ∧
                  (assembledVertices i)[m] = (localArcAtParam i t).vertices[q] ∧
                    (assembledVertices i)[m + 1] =
                      (localArcAtParam i t).vertices[q + 1]) ∨
            (∃ (pre : List {t : ℝ // t ∈ centerParams i})
                (t1 : {t : ℝ // t ∈ centerParams i})
                (t2 : {t : ℝ // t ∈ centerParams i})
                (post : List {t : ℝ // t ∈ centerParams i})
                (X Y : EuclideanSpace ℝ (Fin 2)),
              (centerParams i).attach = pre ++ t1 :: t2 :: post ∧
                (localArcAtParam i t1).vertices.getLast? = some X ∧
                  (localArcAtParam i t2).vertices.head? = some Y ∧
                    (assembledVertices i)[m] = X ∧
                      (assembledVertices i)[m + 1] = Y) ∨
            (∃ (pre : List {t : ℝ // t ∈ centerParams i})
                (t : {t : ℝ // t ∈ centerParams i})
                (X : EuclideanSpace ℝ (Fin 2)),
              (centerParams i).attach = pre ++ [t] ∧
                (localArcAtParam i t).vertices.getLast? = some X ∧
                  (assembledVertices i)[m] = X ∧
                    (assembledVertices i)[m + 1] = b i)) :
    ∀ i ⦃m k : ℕ⦄,
      (hm : m + 1 < (assembledVertices i).length) →
        (hk : k < (assembledVertices i).length) →
          k ≠ m → k ≠ m + 1 →
            (assembledVertices i)[k] ∉
              openSegment ℝ (assembledVertices i)[m]
                (assembledVertices i)[m + 1] := by
  intro i m k hm hk hkm hkm1 hpopen
  let f : ℝ →ᵃ[ℝ] EuclideanSpace ℝ (Fin 2) :=
    AffineMap.lineMap (a i) (b i)
  have hf : Function.Injective f :=
    AffineMap.lineMap_injective (k := ℝ) (hendpoint_ne i)
  have hline_segment_param :
      ∀ {α β : ℝ} {p : EuclideanSpace ℝ (Fin 2)},
        α ≤ β →
          p ∈ segment ℝ (f α) (f β) →
            ∃ s : ℝ, α ≤ s ∧ s ≤ β ∧ p = f s := by
    intro α β p hαβ hp
    have hseg : segment ℝ (f α) (f β) = f '' segment ℝ α β := by
      simp [f]
    rw [hseg] at hp
    rcases hp with ⟨s, hs, hsp⟩
    have hsIcc : s ∈ Set.Icc α β := by
      simpa [segment_eq_Icc hαβ] using hs
    exact ⟨s, hsIcc.1, hsIcc.2, hsp.symm⟩
  have ha_not_mem_param_segment :
      ∀ {α β : ℝ},
        α ≤ β →
          0 < α →
            a i ∉ segment ℝ (f α) (f β) := by
    intro α β hαβ hαpos ha_mem
    rcases hline_segment_param hαβ ha_mem with ⟨s, hαs, _hsβ, hs⟩
    have hs0 : s = 0 := by
      exact hf (by simpa [f] using hs.symm)
    linarith
  have hb_not_mem_param_segment :
      ∀ {α β : ℝ},
        α ≤ β →
          β < 1 →
            b i ∉ segment ℝ (f α) (f β) := by
    intro α β hαβ hβlt hb_mem
    rcases hline_segment_param hαβ hb_mem with ⟨s, _hαs, hsβ, hs⟩
    have hs1 : s = 1 := by
      exact hf (by simpa [f] using hs.symm)
    linarith
  have hentry_ne_left :
      ∀ t : {t : ℝ // t ∈ centerParams i}, a i ≠ entryPoint i t := by
    intro t h
    rcases hentryExitParameters i t with
      ⟨⟨e, he_pos, _he_lt_t, hentry⟩, _⟩
    have he0 : e = 0 := by
      exact hf (by simpa [f, hentry] using h.symm)
    linarith
  have hexit_ne_right :
      ∀ t : {t : ℝ // t ∈ centerParams i}, exitPoint i t ≠ b i := by
    intro t h
    rcases hentryExitParameters i t with
      ⟨_, ⟨x, _ht_lt_x, hx_lt_one, hexit⟩⟩
    have hx1 : x = 1 := by
      exact hf (by simpa [f, hexit] using h)
    linarith
  have hattach_pairwise_lt :
      (centerParams i).attach.Pairwise
        (fun t1 t2 : {t : ℝ // t ∈ centerParams i} => t1.1 < t2.1) := by
    have hmap :
        ((centerParams i).attach.map
            (fun t : {t : ℝ // t ∈ centerParams i} => t.1)).Pairwise
          (fun x y : ℝ => x < y) := by
      simpa [List.attach_map_subtype_val] using
        (List.sortedLT_iff_pairwise.mp (hcenterParams_sorted i))
    rw [List.pairwise_map] at hmap
    exact hmap
  generalize hp_def : (assembledVertices i)[k] = p at hpopen
  have hp_mem : p ∈ assembledVertices i := by
    rw [← hp_def]
    exact List.getElem_mem hk
  have hp_edge_segment :
      p ∈ segment ℝ (assembledVertices i)[m] (assembledVertices i)[m + 1] :=
    openSegment_subset_segment ℝ
      (assembledVertices i)[m] (assembledVertices i)[m + 1] hpopen
  rcases hassembledEdgeEndpointRoles i hm with hnodisks | hroles
  · rcases hnodisks with ⟨hitems, hleft, hright⟩
    have hp_cases := hp_mem
    simp [hassembledVertices i, hitems] at hp_cases
    have hpopenAB : p ∈ openSegment ℝ (a i) (b i) := by
      simpa [hleft, hright] using hpopen
    rcases hp_cases with hpA | hpB
    · rw [hpA] at hpopenAB
      exact (hendpoint_ne i)
        ((left_mem_openSegment_iff (𝕜 := ℝ) (x := a i) (y := b i)).1
          hpopenAB)
    · rw [hpB] at hpopenAB
      exact (hendpoint_ne i)
        ((right_mem_openSegment_iff (𝕜 := ℝ) (x := a i) (y := b i)).1
          hpopenAB)
  rcases hroles with hinitial | hroles
  · rcases hinitial with ⟨t, ts, X, hitems, hhead, hleft, hright⟩
    have hsource_entry :
        (localArcAtParam i t).vertices.head? = some (entryPoint i t) := by
      have hsource := (localArcAtParam i t).source_eq_head
      rw [(hlocalArcAtParam_endpoints i t).1] at hsource
      exact hsource
    have hX : X = entryPoint i t := by
      exact (Option.some.inj (hsource_entry.symm.trans hhead)).symm
    have hpopen_gap : p ∈ openSegment ℝ (a i) (entryPoint i t) := by
      simpa [hleft, hright, hX] using hpopen
    have hpseg_gap : p ∈ segment ℝ (a i) (entryPoint i t) :=
      openSegment_subset_segment ℝ (a i) (entryPoint i t) hpopen_gap
    rcases hentryExitParameters i t with
      ⟨⟨e, he_pos, he_lt_t, hentry⟩,
        ⟨x, ht_lt_x, hx_lt_one, hexit⟩⟩
    have hp_cases := hp_mem
    simp [hassembledVertices i] at hp_cases
    rcases hp_cases with hpA | hp_cases
    · rw [hpA] at hpopen_gap
      exact hentry_ne_left t
        ((left_mem_openSegment_iff (𝕜 := ℝ)
          (x := a i) (y := entryPoint i t)).1 hpopen_gap)
    rcases hp_cases with hp_local | hpB
    · rcases hp_local with ⟨s, hs, hpV⟩
      let t' : {t : ℝ // t ∈ centerParams i} := ⟨s, hs⟩
      have ht'_attach : t' ∈ (centerParams i).attach := by
        simp [t']
      have hpV' : p ∈ (localArcAtParam i t').vertices := by
        simpa [t'] using hpV
      have hp_carrier' :
          p ∈ (localArcAtParam i t').carrier :=
        PolygonalArcVertexMemCarrier (localArcAtParam i t') hpV'
      by_cases ht_eq : t' = t
      · have hp_carrier_t :
            p ∈ (localArcAtParam i t).carrier := by
          simpa [ht_eq] using hp_carrier'
        have hp_eq_entry :
            p = entryPoint i t :=
          hinitialGapMeetsLocalCarrierOnly i t hpseg_gap hp_carrier_t
        have hpopen_entry :
            entryPoint i t ∈ openSegment ℝ (a i) (entryPoint i t) := by
          simpa [hp_eq_entry] using hpopen_gap
        exact hentry_ne_left t
          ((right_mem_openSegment_iff (𝕜 := ℝ)
            (x := a i) (y := entryPoint i t)).1 hpopen_entry)
      · have ht'_tail : t' ∈ ts := by
          have ht'_mem : t' = t ∨ t' ∈ ts := by
            simpa [hitems] using ht'_attach
          exact ht'_mem.resolve_left ht_eq
        have ht_lt_t' : t.1 < t'.1 := by
          have hpair := hattach_pairwise_lt
          rw [hitems] at hpair
          exact (List.pairwise_cons.1 hpair).1 t' ht'_tail
        rcases hentryExitParameters i t' with
          ⟨⟨e', he'_pos, he'_lt_t', hentry'⟩,
            ⟨x', ht'_lt_x', hx'_lt_one, hexit'⟩⟩
        rcases horderedCutSeparation i t t' ht_lt_t' with
          ⟨sExit, sEntry, ht_sExit, hsExitEntry, _hsEntry_t',
            _hexit_order, hentry_order⟩
        exact endpointUnitDiskAssembly_initialGapAvoidsLaterCarrier
          (A := a i) (B := b i) (entry := entryPoint i t)
          (entry' := entryPoint i t') (p := p)
          (laterArc := localArcAtParam i t')
          (e := e) (t := t.1) (e' := e')
          (sExit := sExit) (sEntry := sEntry)
          (hendpoint_ne i) he_pos he_lt_t ht_sExit hsExitEntry
          hentry hentry' hentry_order hpseg_gap hp_carrier'
          (hchordGapLocalCarrierPosition i t'
            (α := (0 : ℝ)) (β := e) (e := e') (x := x')
            hentry' hexit' (by norm_num) (le_of_lt he_pos)
            (by linarith) (by linarith)).1
    · rw [hpB] at hpseg_gap
      have hbseg :
          b i ∈ segment ℝ (f (0 : ℝ)) (f e) := by
        simpa [f, hentry] using hpseg_gap
      exact hb_not_mem_param_segment
        (α := (0 : ℝ)) (β := e) (le_of_lt he_pos)
        (by linarith) hbseg
  rcases hroles with hlocal | hroles
  · rcases hlocal with ⟨_pre, t, _post, q, hq, _hitems, hleft, hright⟩
    exact endpointUnitDiskAssembly_localEdgeAvoid hm hk hq hleft hright
      (hlocalEdgeAvoidsAssembledVertices i t hq hk) hp_def hpopen
  rcases hroles with hbridge | hterminal
  · rcases hbridge with ⟨pre, t1, t2, post, X, Y, hitems, hlast, hhead,
      hleft, hright⟩
    have hlast_exit :
        (localArcAtParam i t1).vertices.getLast? = some (exitPoint i t1) := by
      have htarget := (localArcAtParam i t1).target_eq_last
      rw [(hlocalArcAtParam_endpoints i t1).2] at htarget
      exact htarget
    have hX : X = exitPoint i t1 := by
      exact (Option.some.inj (hlast_exit.symm.trans hlast)).symm
    have hhead_entry :
        (localArcAtParam i t2).vertices.head? = some (entryPoint i t2) := by
      have hsource := (localArcAtParam i t2).source_eq_head
      rw [(hlocalArcAtParam_endpoints i t2).1] at hsource
      exact hsource
    have hY : Y = entryPoint i t2 := by
      exact (Option.some.inj (hhead_entry.symm.trans hhead)).symm
    have hpair_bridge := hattach_pairwise_lt
    rw [hitems] at hpair_bridge
    have htail_pair :
        (t1 :: t2 :: post).Pairwise
          (fun u v : {t : ℝ // t ∈ centerParams i} => u.1 < v.1) :=
      (List.pairwise_append.1 hpair_bridge).2.1
    have ht12 : t1.1 < t2.1 :=
      (List.pairwise_cons.1 htail_pair).1 t2 (by simp)
    rcases hentryExitParameters i t1 with
      ⟨⟨e1, he1_pos, he1_lt_t1, hentry1⟩,
        ⟨x1, ht1_lt_x1, hx1_lt_one, hexit1⟩⟩
    rcases hentryExitParameters i t2 with
      ⟨⟨e2, he2_pos, he2_lt_t2, hentry2⟩,
        ⟨x2, ht2_lt_x2, hx2_lt_one, hexit2⟩⟩
    rcases horderedCutSeparation i t1 t2 ht12 with
      ⟨sExit, sEntry, _ht1_sExit, hsExitEntry, _hsEntry_t2,
        hexit_order, hentry_order⟩
    have hx1_eq : x1 = sExit := by
      exact hf (by rw [← hexit1, ← hexit_order])
    have he2_eq : e2 = sEntry := by
      exact hf (by rw [← hentry2, ← hentry_order])
    have hx1_lt_e2 : x1 < e2 := by
      linarith
    have hpopen_gap :
        p ∈ openSegment ℝ (exitPoint i t1) (entryPoint i t2) := by
      simpa [hleft, hright, hX, hY] using hpopen
    have hpseg_gap :
        p ∈ segment ℝ (exitPoint i t1) (entryPoint i t2) :=
      openSegment_subset_segment ℝ (exitPoint i t1) (entryPoint i t2)
        hpopen_gap
    have hgap_end_ne : exitPoint i t1 ≠ entryPoint i t2 := by
      intro hsame
      have hparam_same : x1 = e2 := by
        exact hf (by simpa [f, hexit1, hentry2] using hsame)
      linarith
    have hp_cases := hp_mem
    simp [hassembledVertices i] at hp_cases
    rcases hp_cases with hpA | hp_cases
    · rw [hpA] at hpseg_gap
      have hseg_param :
          a i ∈ segment ℝ (f x1) (f e2) := by
        simpa [f, hexit1, hentry2] using hpseg_gap
      exact ha_not_mem_param_segment hx1_lt_e2.le (by linarith) hseg_param
    rcases hp_cases with hp_local | hpB
    · rcases hp_local with ⟨s, hs, hpV⟩
      let t' : {t : ℝ // t ∈ centerParams i} := ⟨s, hs⟩
      have ht'_attach : t' ∈ (centerParams i).attach := by
        simp [t']
      have hpV' : p ∈ (localArcAtParam i t').vertices := by
        simpa [t'] using hpV
      have hp_carrier' :
          p ∈ (localArcAtParam i t').carrier :=
        PolygonalArcVertexMemCarrier (localArcAtParam i t') hpV'
      have ht'_decomp :
          t' ∈ pre ∨ t' = t1 ∨ t' = t2 ∨ t' ∈ post := by
        have ht'_mem : t' ∈ pre ++ t1 :: t2 :: post := by
          simpa [hitems] using ht'_attach
        simpa [List.mem_append, List.mem_cons] using ht'_mem
      rcases ht'_decomp with ht'_pre | ht'_decomp
      · have ht'_lt_t1 : t'.1 < t1.1 :=
          (List.pairwise_append.1 hpair_bridge).2.2 t' ht'_pre t1 (by simp)
        rcases hentryExitParameters i t' with
          ⟨⟨e', he'_pos, he'_lt_t', hentry'⟩,
            ⟨x', ht'_lt_x', hx'_lt_one, hexit'⟩⟩
        rcases horderedCutSeparation i t' t1 ht'_lt_t1 with
          ⟨sExit', sEntry', _ht'_sExit', hsExitEntry',
            _hsEntry_t1, hexit_order', hentry_order'⟩
        have hx'_eq : x' = sExit' := by
          exact hf (by rw [← hexit', ← hexit_order'])
        have he1_eq : e1 = sEntry' := by
          exact hf (by rw [← hentry1, ← hentry_order'])
        have hx'_lt_x1 : x' < x1 := by
          linarith
        have hpseg_param :
            p ∈ segment ℝ (AffineMap.lineMap (a i) (b i) x1)
                (AffineMap.lineMap (a i) (b i) e2) := by
          simpa [f, hexit1, hentry2] using hpseg_gap
        exact (hchordGapLocalCarrierPosition i t'
          (α := x1) (β := e2) (e := e') (x := x')
          hentry' hexit' (by linarith) hx1_lt_e2.le
          (by linarith) (by linarith)).2.2.1
            hpseg_param hp_carrier' hx'_lt_x1
      rcases ht'_decomp with ht'_eq1 | ht'_decomp
      · have hp_carrier_t1 :
            p ∈ (localArcAtParam i t1).carrier := by
          simpa [ht'_eq1] using hp_carrier'
        have hp_eq_exit :
            p = exitPoint i t1 :=
          (horderedOutsideGapMeetsNeighboringLocalCarriersOnly i t1 t2 ht12).1
            hpseg_gap hp_carrier_t1
        have hpopen_exit :
            exitPoint i t1 ∈
              openSegment ℝ (exitPoint i t1) (entryPoint i t2) := by
          simpa [hp_eq_exit] using hpopen_gap
        exact hgap_end_ne
          ((left_mem_openSegment_iff (𝕜 := ℝ)
            (x := exitPoint i t1) (y := entryPoint i t2)).1 hpopen_exit)
      rcases ht'_decomp with ht'_eq2 | ht'_post
      · have hp_carrier_t2 :
            p ∈ (localArcAtParam i t2).carrier := by
          simpa [ht'_eq2] using hp_carrier'
        have hp_eq_entry :
            p = entryPoint i t2 :=
          (horderedOutsideGapMeetsNeighboringLocalCarriersOnly i t1 t2 ht12).2
            hpseg_gap hp_carrier_t2
        have hpopen_entry :
            entryPoint i t2 ∈
              openSegment ℝ (exitPoint i t1) (entryPoint i t2) := by
          simpa [hp_eq_entry] using hpopen_gap
        exact hgap_end_ne
          ((right_mem_openSegment_iff (𝕜 := ℝ)
            (x := exitPoint i t1) (y := entryPoint i t2)).1 hpopen_entry)
      · have hprefix_pair :
          ((pre ++ [t1, t2]) ++ post).Pairwise
            (fun u v : {t : ℝ // t ∈ centerParams i} => u.1 < v.1) := by
          simpa [List.append_assoc] using hpair_bridge
        have ht2_lt_t' : t2.1 < t'.1 :=
          (List.pairwise_append.1 hprefix_pair).2.2 t2 (by simp) t' ht'_post
        rcases hentryExitParameters i t' with
          ⟨⟨e', he'_pos, he'_lt_t', hentry'⟩,
            ⟨x', ht'_lt_x', hx'_lt_one, hexit'⟩⟩
        rcases horderedCutSeparation i t2 t' ht2_lt_t' with
          ⟨sExit', sEntry', _ht2_sExit', hsExitEntry',
            _hsEntry_t', _hexit_order', hentry_order'⟩
        have he'_eq : e' = sEntry' := by
          exact hf (by rw [← hentry', ← hentry_order'])
        have he2_lt_e' : e2 < e' := by
          linarith
        have hpseg_param :
            p ∈ segment ℝ (AffineMap.lineMap (a i) (b i) x1)
                (AffineMap.lineMap (a i) (b i) e2) := by
          simpa [f, hexit1, hentry2] using hpseg_gap
        exact (hchordGapLocalCarrierPosition i t'
          (α := x1) (β := e2) (e := e') (x := x')
          hentry' hexit' (by linarith) hx1_lt_e2.le
          (by linarith) (by linarith)).1
            hpseg_param hp_carrier' he2_lt_e'
    · rw [hpB] at hpseg_gap
      have hseg_param :
          b i ∈ segment ℝ (f x1) (f e2) := by
        simpa [f, hexit1, hentry2] using hpseg_gap
      exact hb_not_mem_param_segment hx1_lt_e2.le (by linarith) hseg_param
  · rcases hterminal with ⟨pre, t, X, hitems, hlast, hleft, hright⟩
    have hlast_exit :
        (localArcAtParam i t).vertices.getLast? = some (exitPoint i t) := by
      have htarget := (localArcAtParam i t).target_eq_last
      rw [(hlocalArcAtParam_endpoints i t).2] at htarget
      exact htarget
    have hX : X = exitPoint i t := by
      exact (Option.some.inj (hlast_exit.symm.trans hlast)).symm
    have hpopen_gap : p ∈ openSegment ℝ (exitPoint i t) (b i) := by
      simpa [hleft, hright, hX] using hpopen
    have hpseg_gap : p ∈ segment ℝ (exitPoint i t) (b i) :=
      openSegment_subset_segment ℝ (exitPoint i t) (b i) hpopen_gap
    rcases hentryExitParameters i t with
      ⟨⟨e, he_pos, he_lt_t, hentry⟩,
        ⟨x, ht_lt_x, hx_lt_one, hexit⟩⟩
    have hp_cases := hp_mem
    simp [hassembledVertices i] at hp_cases
    rcases hp_cases with hpA | hp_cases
    · rw [hpA] at hpseg_gap
      have haseg :
          a i ∈ segment ℝ (f x) (f (1 : ℝ)) := by
        simpa [f, hexit] using hpseg_gap
      exact ha_not_mem_param_segment (by linarith) (by linarith) haseg
    rcases hp_cases with hp_local | hpB
    · rcases hp_local with ⟨s, hs, hpV⟩
      let t' : {t : ℝ // t ∈ centerParams i} := ⟨s, hs⟩
      have ht'_attach : t' ∈ (centerParams i).attach := by
        simp [t']
      have hpV' : p ∈ (localArcAtParam i t').vertices := by
        simpa [t'] using hpV
      have hp_carrier' :
          p ∈ (localArcAtParam i t').carrier :=
        PolygonalArcVertexMemCarrier (localArcAtParam i t') hpV'
      by_cases ht_eq : t' = t
      · have hp_carrier_t :
            p ∈ (localArcAtParam i t).carrier := by
          simpa [ht_eq] using hp_carrier'
        have hp_eq_exit :
            p = exitPoint i t :=
          hterminalGapMeetsLocalCarrierOnly i t hpseg_gap hp_carrier_t
        have hpopen_exit :
            exitPoint i t ∈ openSegment ℝ (exitPoint i t) (b i) := by
          simpa [hp_eq_exit] using hpopen_gap
        exact hexit_ne_right t
          ((left_mem_openSegment_iff (𝕜 := ℝ)
            (x := exitPoint i t) (y := b i)).1 hpopen_exit)
      · have ht'_pre : t' ∈ pre := by
          have ht'_mem : t' ∈ pre ∨ t' ∈ [t] := by
            simpa [hitems, List.mem_append] using ht'_attach
          rcases ht'_mem with ht'_pre | ht'_last
          · exact ht'_pre
          · have ht'_eq_t : t' = t := by
              simpa using ht'_last
            exact (ht_eq ht'_eq_t).elim
        have ht'_lt_t : t'.1 < t.1 := by
          have hpair := hattach_pairwise_lt
          rw [hitems] at hpair
          exact (List.pairwise_append.1 hpair).2.2 t' ht'_pre t (by simp)
        rcases hentryExitParameters i t' with
          ⟨⟨e', he'_pos, he'_lt_t', hentry'⟩,
            ⟨x', ht'_lt_x', hx'_lt_one, hexit'⟩⟩
        rcases horderedCutSeparation i t' t ht'_lt_t with
          ⟨sExit, sEntry, _ht'_sExit, hsExitEntry, _hsEntry_t,
            hexit_order, hentry_order⟩
        have hx'_eq : x' = sExit := by
          exact hf (by rw [← hexit', ← hexit_order])
        have he_eq : e = sEntry := by
          exact hf (by rw [← hentry, ← hentry_order])
        have hx'_lt_x : x' < x := by
          linarith
        have hpseg_param :
            p ∈ segment ℝ (AffineMap.lineMap (a i) (b i) x)
                (AffineMap.lineMap (a i) (b i) (1 : ℝ)) := by
          simpa [f, hexit] using hpseg_gap
        exact (hchordGapLocalCarrierPosition i t'
          (α := x) (β := (1 : ℝ)) (e := e') (x := x')
          hentry' hexit' (by linarith) (by linarith)
          (by norm_num) (by linarith)).2.2.1
            hpseg_param hp_carrier' hx'_lt_x
    · rw [hpB] at hpopen_gap
      exact hexit_ne_right t
        ((right_mem_openSegment_iff (𝕜 := ℝ)
          (x := exitPoint i t) (y := b i)).1 hpopen_gap)


private abbrev endpointUnitDiskAssembly_initialRole
    {ι : Type*} (a : ι → EuclideanSpace ℝ (Fin 2))
    (centerParams : ι → List ℝ)
    (localArcAtParam : ∀ i, {t : ℝ // t ∈ centerParams i} → PolygonalArc)
    (assembledVertices : ι → List (EuclideanSpace ℝ (Fin 2)))
    (i : ι) (m : ℕ)
    (hm : m + 1 < (assembledVertices i).length) : Prop :=
  ∃ t ts X,
    (centerParams i).attach = t :: ts ∧
      (localArcAtParam i t).vertices.head? = some X ∧
        (assembledVertices i)[m] = a i ∧
          (assembledVertices i)[m + 1] = X

private abbrev endpointUnitDiskAssembly_localRole
    {ι : Type*} (centerParams : ι → List ℝ)
    (localArcAtParam : ∀ i, {t : ℝ // t ∈ centerParams i} → PolygonalArc)
    (assembledVertices : ι → List (EuclideanSpace ℝ (Fin 2)))
    (i : ι) (m : ℕ)
    (hm : m + 1 < (assembledVertices i).length) : Prop :=
  ∃ (pre : List {t : ℝ // t ∈ centerParams i})
      (t : {t : ℝ // t ∈ centerParams i})
      (post : List {t : ℝ // t ∈ centerParams i}) (q : ℕ),
    ∃ hq : q + 1 < (localArcAtParam i t).vertices.length,
      (centerParams i).attach = pre ++ t :: post ∧
        (assembledVertices i)[m] = (localArcAtParam i t).vertices[q] ∧
          (assembledVertices i)[m + 1] =
            (localArcAtParam i t).vertices[q + 1]

private abbrev endpointUnitDiskAssembly_bridgeRole
    {ι : Type*} (centerParams : ι → List ℝ)
    (localArcAtParam : ∀ i, {t : ℝ // t ∈ centerParams i} → PolygonalArc)
    (assembledVertices : ι → List (EuclideanSpace ℝ (Fin 2)))
    (i : ι) (m : ℕ)
    (hm : m + 1 < (assembledVertices i).length) : Prop :=
  ∃ (pre : List {t : ℝ // t ∈ centerParams i})
      (t1 t2 : {t : ℝ // t ∈ centerParams i})
      (post : List {t : ℝ // t ∈ centerParams i})
      (X Y : EuclideanSpace ℝ (Fin 2)),
    (centerParams i).attach = pre ++ t1 :: t2 :: post ∧
      (localArcAtParam i t1).vertices.getLast? = some X ∧
        (localArcAtParam i t2).vertices.head? = some Y ∧
          (assembledVertices i)[m] = X ∧
            (assembledVertices i)[m + 1] = Y

private abbrev endpointUnitDiskAssembly_terminalRole
    {ι : Type*} (b : ι → EuclideanSpace ℝ (Fin 2))
    (centerParams : ι → List ℝ)
    (localArcAtParam : ∀ i, {t : ℝ // t ∈ centerParams i} → PolygonalArc)
    (assembledVertices : ι → List (EuclideanSpace ℝ (Fin 2)))
    (i : ι) (m : ℕ)
    (hm : m + 1 < (assembledVertices i).length) : Prop :=
  ∃ (pre : List {t : ℝ // t ∈ centerParams i})
      (t : {t : ℝ // t ∈ centerParams i})
      (X : EuclideanSpace ℝ (Fin 2)),
    (centerParams i).attach = pre ++ [t] ∧
      (localArcAtParam i t).vertices.getLast? = some X ∧
        (assembledVertices i)[m] = X ∧
          (assembledVertices i)[m + 1] = b i

private abbrev endpointUnitDiskAssembly_noninitialRole
    {ι : Type*} (b : ι → EuclideanSpace ℝ (Fin 2))
    (centerParams : ι → List ℝ)
    (localArcAtParam : ∀ i, {t : ℝ // t ∈ centerParams i} → PolygonalArc)
    (assembledVertices : ι → List (EuclideanSpace ℝ (Fin 2)))
    (i : ι) (m : ℕ)
    (hm : m + 1 < (assembledVertices i).length) : Prop :=
  endpointUnitDiskAssembly_localRole centerParams localArcAtParam
      assembledVertices i m hm ∨
    endpointUnitDiskAssembly_bridgeRole centerParams localArcAtParam
        assembledVertices i m hm ∨
      endpointUnitDiskAssembly_terminalRole b centerParams localArcAtParam
        assembledVertices i m hm

private abbrev endpointUnitDiskAssembly_nonemptyRole
    {ι : Type*} (a b : ι → EuclideanSpace ℝ (Fin 2))
    (centerParams : ι → List ℝ)
    (localArcAtParam : ∀ i, {t : ℝ // t ∈ centerParams i} → PolygonalArc)
    (assembledVertices : ι → List (EuclideanSpace ℝ (Fin 2)))
    (i : ι) (m : ℕ)
    (hm : m + 1 < (assembledVertices i).length) : Prop :=
  endpointUnitDiskAssembly_initialRole a centerParams localArcAtParam
      assembledVertices i m hm ∨
    endpointUnitDiskAssembly_noninitialRole b centerParams localArcAtParam
      assembledVertices i m hm

private lemma endpointUnitDiskAssembly_segments_initial
    {ι : Type*} [Fintype ι]
    (a b : ι → EuclideanSpace ℝ (Fin 2))
    (T : Finset (EuclideanSpace ℝ (Fin 2)))
    (r : EuclideanSpace ℝ (Fin 2) → ℝ)
    (centerParams : ι → List ℝ)
    (centerOfParam :
      ∀ i, {t : ℝ // t ∈ centerParams i} → EuclideanSpace ℝ (Fin 2))
    (hcenterOfParam_def :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}),
        centerOfParam i t = AffineMap.lineMap (a i) (b i) t.1)
    (localArcAtParam :
      ∀ i, {t : ℝ // t ∈ centerParams i} → PolygonalArc)
    (entryPoint exitPoint :
      ∀ i, {t : ℝ // t ∈ centerParams i} → EuclideanSpace ℝ (Fin 2))
    (orderedLocalVertexBlocks :
      ∀ i, List (List (EuclideanSpace ℝ (Fin 2))))
    (assembledVertices : ι → List (EuclideanSpace ℝ (Fin 2)))
    (horderedLocalVertexBlocks_def : ∀ i,
      orderedLocalVertexBlocks i =
        (centerParams i).attach.map
          (fun t => (localArcAtParam i t).vertices))
    (hassembledVertices_def : ∀ i,
      assembledVertices i =
        EndpointUnitDiskAlternatingVertexList
          (a i) (b i) (orderedLocalVertexBlocks i))
    (hendpoint_ne : ∀ i, a i ≠ b i)
    (hcenterParams_sorted : ∀ i, (centerParams i).SortedLT)
    (hcenterOfParam_T :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}), centerOfParam i t ∈ T)
    (hlocalArcAtParam_props :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}),
        (localArcAtParam i t).source = entryPoint i t ∧
          (localArcAtParam i t).target = exitPoint i t ∧
            (localArcAtParam i t).carrier ⊆
              Metric.closedBall (centerOfParam i t) (r (centerOfParam i t)) ∧
              (localArcAtParam i t).relativeInterior ⊆
                Metric.ball (centerOfParam i t) (r (centerOfParam i t)))
    (hentryExitParameters :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}),
        (∃ s : ℝ, 0 < s ∧ s < t.1 ∧
          entryPoint i t = AffineMap.lineMap (a i) (b i) s) ∧
          (∃ s : ℝ, t.1 < s ∧ s < 1 ∧
            exitPoint i t = AffineMap.lineMap (a i) (b i) s))
    (horderedCutSeparation :
      ∀ i (t1 t2 : {t : ℝ // t ∈ centerParams i}),
        t1.1 < t2.1 →
          ∃ sExit sEntry : ℝ,
            t1.1 < sExit ∧
              sExit < sEntry ∧
                sEntry < t2.1 ∧
                  exitPoint i t1 = AffineMap.lineMap (a i) (b i) sExit ∧
                    entryPoint i t2 = AffineMap.lineMap (a i) (b i) sEntry)
    (hchordGapLocalCarrierPosition :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}) {α β e x : ℝ},
        entryPoint i t = AffineMap.lineMap (a i) (b i) e →
          exitPoint i t = AffineMap.lineMap (a i) (b i) x →
            0 ≤ α → α ≤ β → β ≤ 1 → e < x →
              (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
                p ∈ segment ℝ (AffineMap.lineMap (a i) (b i) α)
                    (AffineMap.lineMap (a i) (b i) β) →
                  p ∈ (localArcAtParam i t).carrier →
                    β < e → False) ∧
                (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
                  p ∈ segment ℝ (AffineMap.lineMap (a i) (b i) α)
                      (AffineMap.lineMap (a i) (b i) β) →
                    p ∈ (localArcAtParam i t).carrier →
                      β = e → p = entryPoint i t) ∧
                  (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
                    p ∈ segment ℝ (AffineMap.lineMap (a i) (b i) α)
                        (AffineMap.lineMap (a i) (b i) β) →
                      p ∈ (localArcAtParam i t).carrier →
                        x < α → False) ∧
                    (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
                      p ∈ segment ℝ (AffineMap.lineMap (a i) (b i) α)
                          (AffineMap.lineMap (a i) (b i) β) →
                        p ∈ (localArcAtParam i t).carrier →
                          x = α → p = exitPoint i t))
    (hinitialGapMeetsLocalCarrierOnly :
      ∀ i (t : {t : ℝ // t ∈ centerParams i})
        ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        p ∈ segment ℝ (a i) (entryPoint i t) →
          p ∈ (localArcAtParam i t).carrier → p = entryPoint i t)
    (hterminalGapMeetsLocalCarrierOnly :
      ∀ i (t : {t : ℝ // t ∈ centerParams i})
        ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        p ∈ segment ℝ (exitPoint i t) (b i) →
          p ∈ (localArcAtParam i t).carrier → p = exitPoint i t)
    (horderedOutsideGapMeetsNeighboringLocalCarriersOnly :
      ∀ i (t1 t2 : {t : ℝ // t ∈ centerParams i}),
        t1.1 < t2.1 →
          (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
            p ∈ segment ℝ (exitPoint i t1) (entryPoint i t2) →
              p ∈ (localArcAtParam i t1).carrier → p = exitPoint i t1) ∧
            (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
              p ∈ segment ℝ (exitPoint i t1) (entryPoint i t2) →
                p ∈ (localArcAtParam i t2).carrier → p = entryPoint i t2))
    (hdisjoint : ∀ ⦃z w : EuclideanSpace ℝ (Fin 2)⦄,
      z ∈ T → w ∈ T → z ≠ w →
        Disjoint (Metric.closedBall z (r z)) (Metric.closedBall w (r w)))
    (hassembledVertices_nodup : ∀ i, (assembledVertices i).Nodup)
    (hassembledVertices_avoid :
      ∀ i ⦃m k : ℕ⦄,
        (hm : m + 1 < (assembledVertices i).length) →
          (hk : k < (assembledVertices i).length) →
            k ≠ m → k ≠ m + 1 →
              (assembledVertices i)[k] ∉
                openSegment ℝ
                  (assembledVertices i)[m] (assembledVertices i)[m + 1])
    (hassembledEdgeEndpointRoles :
      ∀ i ⦃m : ℕ⦄,
        (hm : m + 1 < (assembledVertices i).length) →
          ((centerParams i).attach = [] ∧
              (assembledVertices i)[m] = a i ∧
                (assembledVertices i)[m + 1] = b i) ∨
            (∃ t ts X,
              (centerParams i).attach = t :: ts ∧
                (localArcAtParam i t).vertices.head? = some X ∧
                  (assembledVertices i)[m] = a i ∧
                    (assembledVertices i)[m + 1] = X) ∨
            (∃ (pre : List {t : ℝ // t ∈ centerParams i})
                (t : {t : ℝ // t ∈ centerParams i})
                (post : List {t : ℝ // t ∈ centerParams i}) (q : ℕ),
              ∃ hq : q + 1 < (localArcAtParam i t).vertices.length,
                (centerParams i).attach = pre ++ t :: post ∧
                  (assembledVertices i)[m] =
                    (localArcAtParam i t).vertices[q] ∧
                    (assembledVertices i)[m + 1] =
                      (localArcAtParam i t).vertices[q + 1]) ∨
            (∃ (pre : List {t : ℝ // t ∈ centerParams i})
                (t1 : {t : ℝ // t ∈ centerParams i})
                (t2 : {t : ℝ // t ∈ centerParams i})
                (post : List {t : ℝ // t ∈ centerParams i})
                (X Y : EuclideanSpace ℝ (Fin 2)),
              (centerParams i).attach = pre ++ t1 :: t2 :: post ∧
                (localArcAtParam i t1).vertices.getLast? = some X ∧
                  (localArcAtParam i t2).vertices.head? = some Y ∧
                    (assembledVertices i)[m] = X ∧
                      (assembledVertices i)[m + 1] = Y) ∨
            (∃ (pre : List {t : ℝ // t ∈ centerParams i})
                (t : {t : ℝ // t ∈ centerParams i})
                (X : EuclideanSpace ℝ (Fin 2)),
              (centerParams i).attach = pre ++ [t] ∧
                (localArcAtParam i t).vertices.getLast? = some X ∧
                  (assembledVertices i)[m] = X ∧
                    (assembledVertices i)[m + 1] = b i))
    (hlineSegmentInterSeparated :
      ∀ i {α β γ δ : ℝ}, α ≤ β → γ ≤ δ → β < γ →
        segment ℝ (AffineMap.lineMap (a i) (b i) α)
            (AffineMap.lineMap (a i) (b i) β) ∩
          segment ℝ (AffineMap.lineMap (a i) (b i) γ)
            (AffineMap.lineMap (a i) (b i) δ) =
        (∅ : Set (EuclideanSpace ℝ (Fin 2))))
    (i : ι) {m n : ℕ}
    (hm : m + 1 < (assembledVertices i).length)
    (hn : n + 1 < (assembledVertices i).length)
    (hmn : m < n)
    (hinitialIndexZero :
      ∀ ⦃k : ℕ⦄,
        (hk : k + 1 < (assembledVertices i).length) →
          endpointUnitDiskAssembly_initialRole a centerParams localArcAtParam
              assembledVertices i k hk →
            k = 0)
    (hterminalNoLater :
      ∀ ⦃k l : ℕ⦄,
        (hk : k + 1 < (assembledVertices i).length) →
        (hl : l + 1 < (assembledVertices i).length) →
        k < l →
          endpointUnitDiskAssembly_terminalRole b centerParams localArcAtParam
              assembledVertices i k hk →
            False)
    (hinter_of_forall_eq_right :
      (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        p ∈ segment ℝ (assembledVertices i)[m] (assembledVertices i)[m + 1] →
        p ∈ segment ℝ (assembledVertices i)[n] (assembledVertices i)[n + 1] →
          p = (assembledVertices i)[m + 1]) →
      (segment ℝ (assembledVertices i)[m] (assembledVertices i)[m + 1] ∩
          segment ℝ (assembledVertices i)[n] (assembledVertices i)[n + 1]) =
        if n = m + 1 then {(assembledVertices i)[n]} else ∅)
    (hattach_pairwise_lt :
      (centerParams i).attach.Pairwise
        (fun t1 t2 : {t : ℝ // t ∈ centerParams i} => t1.1 < t2.1))
    (hinitial_m :
      endpointUnitDiskAssembly_initialRole a centerParams localArcAtParam
        assembledVertices i m hm)
    (hroles_n :
      endpointUnitDiskAssembly_nonemptyRole a b centerParams localArcAtParam
        assembledVertices i n hn) :
    (segment ℝ (assembledVertices i)[m] (assembledVertices i)[m + 1] ∩
        segment ℝ (assembledVertices i)[n] (assembledVertices i)[n + 1]) =
      if n = m + 1 then {(assembledVertices i)[n]} else ∅ := by
  rcases hroles_n with hinitial_n | hroles_n
  · rcases hinitial_m with
      ⟨t_m, ts_m, X_m, _hitems_m, _hhead_m, hleft_m, _hright_m⟩
    rcases hinitial_n with
      ⟨t_n, ts_n, X_n, _hitems_n, _hhead_n, hleft_n, _hright_n⟩
    have hm_lt : m < (assembledVertices i).length :=
      Nat.lt_trans (Nat.lt_succ_self m) hm
    have hn_lt : n < (assembledVertices i).length :=
      Nat.lt_trans (Nat.lt_succ_self n) hn
    have hmn_eq : m = n := by
      have hval : (assembledVertices i)[m] = (assembledVertices i)[n] := by
        rw [hleft_m, hleft_n]
      exact ((hassembledVertices_nodup i).getElem_inj_iff).1 hval
    exact False.elim (by omega)
  · rcases hroles_n with hlocal_n | hroles_n
    · rcases hinitial_m with
        ⟨t0, ts0, X0, hitems_m, hhead_m, hleft_m, hright_m⟩
      rcases hlocal_n with
        ⟨pre, t, post, q, hq, hitems_n, hleft_n, hright_n⟩
      have hsource_entry :
          (localArcAtParam i t0).vertices.head? = some (entryPoint i t0) := by
        have hsource := (localArcAtParam i t0).source_eq_head
        rw [(hlocalArcAtParam_props i t0).1] at hsource
        exact hsource
      have hX : X0 = entryPoint i t0 := by
        exact (Option.some.inj (hsource_entry.symm.trans hhead_m)).symm
      exact hinter_of_forall_eq_right (by
        intro p hp_initial hp_local
        have hp_gap :
            p ∈ segment ℝ (a i) (entryPoint i t0) := by
          simpa [hleft_m, hright_m, hX] using hp_initial
        have hp_carrier :
            p ∈ (localArcAtParam i t).carrier := by
          rw [(localArcAtParam i t).carrier_eq]
          exact ⟨q, hq, by simpa [hleft_n, hright_n] using hp_local⟩
        have ht_attach : t ∈ (centerParams i).attach := by
          rw [hitems_n]
          simp
        have ht_decomp : t = t0 ∨ t ∈ ts0 := by
          simpa [hitems_m] using ht_attach
        rcases ht_decomp with ht_eq | ht_tail
        · subst t
          have hp_eq_entry :
              p = entryPoint i t0 :=
            hinitialGapMeetsLocalCarrierOnly i t0 hp_gap hp_carrier
          simpa [hright_m, hX] using hp_eq_entry
        · let f : ℝ →ᵃ[ℝ] EuclideanSpace ℝ (Fin 2) :=
            AffineMap.lineMap (a i) (b i)
          have hf : Function.Injective f :=
            AffineMap.lineMap_injective (k := ℝ) (hendpoint_ne i)
          have ht0_lt_t : t0.1 < t.1 := by
            have hpair := hattach_pairwise_lt
            rw [hitems_m] at hpair
            exact (List.pairwise_cons.1 hpair).1 t ht_tail
          rcases hentryExitParameters i t0 with
            ⟨⟨e0, he0_pos, _he0_lt_t0, hentry0⟩, _⟩
          rcases hentryExitParameters i t with
            ⟨⟨e, he_pos, he_lt_t, hentry⟩,
              ⟨x, ht_lt_x, hx_lt_one, hexit⟩⟩
          rcases horderedCutSeparation i t0 t ht0_lt_t with
            ⟨sExit, sEntry, _ht0_sExit, hsExitEntry, _hsEntry_t,
              _hexit_order, hentry_order⟩
          have he_eq : e = sEntry := by
            exact hf (by rw [← hentry, ← hentry_order])
          have he0_lt_e : e0 < e := by
            linarith
          have hpseg_param :
              p ∈ segment ℝ (AffineMap.lineMap (a i) (b i) (0 : ℝ))
                  (AffineMap.lineMap (a i) (b i) e0) := by
            simpa [f, hentry0] using hp_gap
          exact False.elim
            ((hchordGapLocalCarrierPosition i t
              (α := (0 : ℝ)) (β := e0) (e := e) (x := x)
              hentry hexit (by norm_num) (le_of_lt he0_pos)
              (by linarith) (by linarith)).1
                hpseg_param hp_carrier he0_lt_e))
    · rcases hroles_n with hbridge_n | hterminal_n
      · rcases hinitial_m with
          ⟨t0, ts0, X0, hitems_m, hhead_m, hleft_m, hright_m⟩
        rcases hbridge_n with
          ⟨pre, t1, t2, post, X1, Y2, hitems_n, hlast_n,
            hhead_n, hleft_n, hright_n⟩
        have hsource_entry0 :
            (localArcAtParam i t0).vertices.head? = some (entryPoint i t0) := by
          have hsource := (localArcAtParam i t0).source_eq_head
          rw [(hlocalArcAtParam_props i t0).1] at hsource
          exact hsource
        have hX0 : X0 = entryPoint i t0 := by
          exact (Option.some.inj (hsource_entry0.symm.trans hhead_m)).symm
        have hlast_exit1 :
            (localArcAtParam i t1).vertices.getLast? = some (exitPoint i t1) := by
          have htarget := (localArcAtParam i t1).target_eq_last
          rw [(hlocalArcAtParam_props i t1).2.1] at htarget
          exact htarget
        have hX1 : X1 = exitPoint i t1 := by
          exact (Option.some.inj (hlast_exit1.symm.trans hlast_n)).symm
        have hhead_entry2 :
            (localArcAtParam i t2).vertices.head? = some (entryPoint i t2) := by
          have hsource := (localArcAtParam i t2).source_eq_head
          rw [(hlocalArcAtParam_props i t2).1] at hsource
          exact hsource
        have hY2 : Y2 = entryPoint i t2 := by
          exact (Option.some.inj (hhead_entry2.symm.trans hhead_n)).symm
        have hpair_bridge := hattach_pairwise_lt
        rw [hitems_n] at hpair_bridge
        have htail_pair :
            (t1 :: t2 :: post).Pairwise
              (fun u v : {t : ℝ // t ∈ centerParams i} => u.1 < v.1) :=
          (List.pairwise_append.1 hpair_bridge).2.1
        have ht12 : t1.1 < t2.1 :=
          (List.pairwise_cons.1 htail_pair).1 t2 (by simp)
        have ht1_attach : t1 ∈ (centerParams i).attach := by
          rw [hitems_n]
          simp
        have ht1_decomp : t1 = t0 ∨ t1 ∈ ts0 := by
          simpa [hitems_m] using ht1_attach
        rcases hentryExitParameters i t0 with
          ⟨⟨e0, he0_pos, he0_lt_t0, hentry0⟩, _⟩
        rcases hentryExitParameters i t1 with
          ⟨_, ⟨x1, ht1_lt_x1, _hx1_lt_one, hexit1⟩⟩
        rcases hentryExitParameters i t2 with
          ⟨⟨e2, _he2_pos, _he2_lt_t2, hentry2⟩, _⟩
        rcases horderedCutSeparation i t1 t2 ht12 with
          ⟨sExit, sEntry, _ht1_sExit, hsExitEntry, _hsEntry_t2,
            hexit_order, hentry_order⟩
        let f : ℝ →ᵃ[ℝ] EuclideanSpace ℝ (Fin 2) :=
          AffineMap.lineMap (a i) (b i)
        have hf : Function.Injective f :=
          AffineMap.lineMap_injective (k := ℝ) (hendpoint_ne i)
        have hx1_eq : x1 = sExit := by
          exact hf (by rw [← hexit1, ← hexit_order])
        have he2_eq : e2 = sEntry := by
          exact hf (by rw [← hentry2, ← hentry_order])
        have hx1_lt_e2 : x1 < e2 := by
          linarith
        have he0_lt_x1 : e0 < x1 := by
          rcases ht1_decomp with ht1_eq | ht1_tail
          · subst t1
            linarith
          · have ht0_lt_t1 : t0.1 < t1.1 := by
              have hpair := hattach_pairwise_lt
              rw [hitems_m] at hpair
              exact (List.pairwise_cons.1 hpair).1 t1 ht1_tail
            linarith
        have hdisjoint_initial_bridge :
            segment ℝ (a i) (entryPoint i t0) ∩
                segment ℝ (exitPoint i t1) (entryPoint i t2) =
              (∅ : Set (EuclideanSpace ℝ (Fin 2))) := by
          simpa [f, hentry0, hexit1, hentry2] using
            (hlineSegmentInterSeparated i
              (α := (0 : ℝ)) (β := e0) (γ := x1) (δ := e2)
              (le_of_lt he0_pos) (le_of_lt hx1_lt_e2) he0_lt_x1)
        exact hinter_of_forall_eq_right (by
          intro p hp_initial hp_bridge
          have hp_initial' :
              p ∈ segment ℝ (a i) (entryPoint i t0) := by
            simpa [hleft_m, hright_m, hX0] using hp_initial
          have hp_bridge' :
              p ∈ segment ℝ (exitPoint i t1) (entryPoint i t2) := by
            simpa [hleft_n, hright_n, hX1, hY2] using hp_bridge
          have hp_empty :
              p ∈ (∅ : Set (EuclideanSpace ℝ (Fin 2))) := by
            simpa [hdisjoint_initial_bridge] using
              (show p ∈ segment ℝ (a i) (entryPoint i t0) ∩
                  segment ℝ (exitPoint i t1) (entryPoint i t2) from
                ⟨hp_initial', hp_bridge'⟩)
          exact False.elim hp_empty)
      · rcases hinitial_m with
          ⟨t0, ts0, X0, hitems_m, hhead_m, hleft_m, hright_m⟩
        rcases hterminal_n with
          ⟨pre, t, X, hitems_n, hlast_n, hleft_n, hright_n⟩
        have hsource_entry0 :
            (localArcAtParam i t0).vertices.head? = some (entryPoint i t0) := by
          have hsource := (localArcAtParam i t0).source_eq_head
          rw [(hlocalArcAtParam_props i t0).1] at hsource
          exact hsource
        have hX0 : X0 = entryPoint i t0 := by
          exact (Option.some.inj (hsource_entry0.symm.trans hhead_m)).symm
        have hlast_exit :
            (localArcAtParam i t).vertices.getLast? = some (exitPoint i t) := by
          have htarget := (localArcAtParam i t).target_eq_last
          rw [(hlocalArcAtParam_props i t).2.1] at htarget
          exact htarget
        have hX : X = exitPoint i t := by
          exact (Option.some.inj (hlast_exit.symm.trans hlast_n)).symm
        have ht_attach : t ∈ (centerParams i).attach := by
          rw [hitems_n]
          simp
        have ht_decomp : t = t0 ∨ t ∈ ts0 := by
          simpa [hitems_m] using ht_attach
        rcases hentryExitParameters i t0 with
          ⟨⟨e0, he0_pos, he0_lt_t0, hentry0⟩, _⟩
        rcases hentryExitParameters i t with
          ⟨_, ⟨x, ht_lt_x, hx_lt_one, hexit⟩⟩
        have he0_lt_x : e0 < x := by
          rcases ht_decomp with ht_eq | ht_tail
          · subst t
            linarith
          · have ht0_lt_t : t0.1 < t.1 := by
              have hpair := hattach_pairwise_lt
              rw [hitems_m] at hpair
              exact (List.pairwise_cons.1 hpair).1 t ht_tail
            linarith
        have hdisjoint_initial_terminal :
            segment ℝ (a i) (entryPoint i t0) ∩
                segment ℝ (exitPoint i t) (b i) =
              (∅ : Set (EuclideanSpace ℝ (Fin 2))) := by
          simpa [hentry0, hexit] using
            (hlineSegmentInterSeparated i
              (α := (0 : ℝ)) (β := e0) (γ := x) (δ := (1 : ℝ))
              (le_of_lt he0_pos) (by linarith) he0_lt_x)
        exact hinter_of_forall_eq_right (by
          intro p hp_initial hp_terminal
          have hp_initial' :
              p ∈ segment ℝ (a i) (entryPoint i t0) := by
            simpa [hleft_m, hright_m, hX0] using hp_initial
          have hp_terminal' :
              p ∈ segment ℝ (exitPoint i t) (b i) := by
            simpa [hleft_n, hright_n, hX] using hp_terminal
          have hp_empty :
              p ∈ (∅ : Set (EuclideanSpace ℝ (Fin 2))) := by
            simpa [hdisjoint_initial_terminal] using
              (show p ∈ segment ℝ (a i) (entryPoint i t0) ∩
                  segment ℝ (exitPoint i t) (b i) from
                ⟨hp_initial', hp_terminal'⟩)
          exact False.elim hp_empty)

private lemma endpointUnitDiskAssembly_segments_local_initial
    {ι : Type*} [Fintype ι]
    (a b : ι → EuclideanSpace ℝ (Fin 2))
    (T : Finset (EuclideanSpace ℝ (Fin 2)))
    (r : EuclideanSpace ℝ (Fin 2) → ℝ)
    (centerParams : ι → List ℝ)
    (centerOfParam :
      ∀ i, {t : ℝ // t ∈ centerParams i} → EuclideanSpace ℝ (Fin 2))
    (hcenterOfParam_def :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}),
        centerOfParam i t = AffineMap.lineMap (a i) (b i) t.1)
    (localArcAtParam :
      ∀ i, {t : ℝ // t ∈ centerParams i} → PolygonalArc)
    (entryPoint exitPoint :
      ∀ i, {t : ℝ // t ∈ centerParams i} → EuclideanSpace ℝ (Fin 2))
    (orderedLocalVertexBlocks :
      ∀ i, List (List (EuclideanSpace ℝ (Fin 2))))
    (assembledVertices : ι → List (EuclideanSpace ℝ (Fin 2)))
    (horderedLocalVertexBlocks_def : ∀ i,
      orderedLocalVertexBlocks i =
        (centerParams i).attach.map
          (fun t => (localArcAtParam i t).vertices))
    (hassembledVertices_def : ∀ i,
      assembledVertices i =
        EndpointUnitDiskAlternatingVertexList
          (a i) (b i) (orderedLocalVertexBlocks i))
    (hendpoint_ne : ∀ i, a i ≠ b i)
    (hcenterParams_sorted : ∀ i, (centerParams i).SortedLT)
    (hcenterOfParam_T :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}), centerOfParam i t ∈ T)
    (hlocalArcAtParam_props :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}),
        (localArcAtParam i t).source = entryPoint i t ∧
          (localArcAtParam i t).target = exitPoint i t ∧
            (localArcAtParam i t).carrier ⊆
              Metric.closedBall (centerOfParam i t) (r (centerOfParam i t)) ∧
              (localArcAtParam i t).relativeInterior ⊆
                Metric.ball (centerOfParam i t) (r (centerOfParam i t)))
    (hentryExitParameters :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}),
        (∃ s : ℝ, 0 < s ∧ s < t.1 ∧
          entryPoint i t = AffineMap.lineMap (a i) (b i) s) ∧
          (∃ s : ℝ, t.1 < s ∧ s < 1 ∧
            exitPoint i t = AffineMap.lineMap (a i) (b i) s))
    (horderedCutSeparation :
      ∀ i (t1 t2 : {t : ℝ // t ∈ centerParams i}),
        t1.1 < t2.1 →
          ∃ sExit sEntry : ℝ,
            t1.1 < sExit ∧
              sExit < sEntry ∧
                sEntry < t2.1 ∧
                  exitPoint i t1 = AffineMap.lineMap (a i) (b i) sExit ∧
                    entryPoint i t2 = AffineMap.lineMap (a i) (b i) sEntry)
    (hchordGapLocalCarrierPosition :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}) {α β e x : ℝ},
        entryPoint i t = AffineMap.lineMap (a i) (b i) e →
          exitPoint i t = AffineMap.lineMap (a i) (b i) x →
            0 ≤ α → α ≤ β → β ≤ 1 → e < x →
              (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
                p ∈ segment ℝ (AffineMap.lineMap (a i) (b i) α)
                    (AffineMap.lineMap (a i) (b i) β) →
                  p ∈ (localArcAtParam i t).carrier →
                    β < e → False) ∧
                (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
                  p ∈ segment ℝ (AffineMap.lineMap (a i) (b i) α)
                      (AffineMap.lineMap (a i) (b i) β) →
                    p ∈ (localArcAtParam i t).carrier →
                      β = e → p = entryPoint i t) ∧
                  (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
                    p ∈ segment ℝ (AffineMap.lineMap (a i) (b i) α)
                        (AffineMap.lineMap (a i) (b i) β) →
                      p ∈ (localArcAtParam i t).carrier →
                        x < α → False) ∧
                    (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
                      p ∈ segment ℝ (AffineMap.lineMap (a i) (b i) α)
                          (AffineMap.lineMap (a i) (b i) β) →
                        p ∈ (localArcAtParam i t).carrier →
                          x = α → p = exitPoint i t))
    (hinitialGapMeetsLocalCarrierOnly :
      ∀ i (t : {t : ℝ // t ∈ centerParams i})
        ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        p ∈ segment ℝ (a i) (entryPoint i t) →
          p ∈ (localArcAtParam i t).carrier → p = entryPoint i t)
    (hterminalGapMeetsLocalCarrierOnly :
      ∀ i (t : {t : ℝ // t ∈ centerParams i})
        ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        p ∈ segment ℝ (exitPoint i t) (b i) →
          p ∈ (localArcAtParam i t).carrier → p = exitPoint i t)
    (horderedOutsideGapMeetsNeighboringLocalCarriersOnly :
      ∀ i (t1 t2 : {t : ℝ // t ∈ centerParams i}),
        t1.1 < t2.1 →
          (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
            p ∈ segment ℝ (exitPoint i t1) (entryPoint i t2) →
              p ∈ (localArcAtParam i t1).carrier → p = exitPoint i t1) ∧
            (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
              p ∈ segment ℝ (exitPoint i t1) (entryPoint i t2) →
                p ∈ (localArcAtParam i t2).carrier → p = entryPoint i t2))
    (hdisjoint : ∀ ⦃z w : EuclideanSpace ℝ (Fin 2)⦄,
      z ∈ T → w ∈ T → z ≠ w →
        Disjoint (Metric.closedBall z (r z)) (Metric.closedBall w (r w)))
    (hassembledVertices_nodup : ∀ i, (assembledVertices i).Nodup)
    (hassembledVertices_avoid :
      ∀ i ⦃m k : ℕ⦄,
        (hm : m + 1 < (assembledVertices i).length) →
          (hk : k < (assembledVertices i).length) →
            k ≠ m → k ≠ m + 1 →
              (assembledVertices i)[k] ∉
                openSegment ℝ
                  (assembledVertices i)[m] (assembledVertices i)[m + 1])
    (hassembledEdgeEndpointRoles :
      ∀ i ⦃m : ℕ⦄,
        (hm : m + 1 < (assembledVertices i).length) →
          ((centerParams i).attach = [] ∧
              (assembledVertices i)[m] = a i ∧
                (assembledVertices i)[m + 1] = b i) ∨
            (∃ t ts X,
              (centerParams i).attach = t :: ts ∧
                (localArcAtParam i t).vertices.head? = some X ∧
                  (assembledVertices i)[m] = a i ∧
                    (assembledVertices i)[m + 1] = X) ∨
            (∃ (pre : List {t : ℝ // t ∈ centerParams i})
                (t : {t : ℝ // t ∈ centerParams i})
                (post : List {t : ℝ // t ∈ centerParams i}) (q : ℕ),
              ∃ hq : q + 1 < (localArcAtParam i t).vertices.length,
                (centerParams i).attach = pre ++ t :: post ∧
                  (assembledVertices i)[m] =
                    (localArcAtParam i t).vertices[q] ∧
                    (assembledVertices i)[m + 1] =
                      (localArcAtParam i t).vertices[q + 1]) ∨
            (∃ (pre : List {t : ℝ // t ∈ centerParams i})
                (t1 : {t : ℝ // t ∈ centerParams i})
                (t2 : {t : ℝ // t ∈ centerParams i})
                (post : List {t : ℝ // t ∈ centerParams i})
                (X Y : EuclideanSpace ℝ (Fin 2)),
              (centerParams i).attach = pre ++ t1 :: t2 :: post ∧
                (localArcAtParam i t1).vertices.getLast? = some X ∧
                  (localArcAtParam i t2).vertices.head? = some Y ∧
                    (assembledVertices i)[m] = X ∧
                      (assembledVertices i)[m + 1] = Y) ∨
            (∃ (pre : List {t : ℝ // t ∈ centerParams i})
                (t : {t : ℝ // t ∈ centerParams i})
                (X : EuclideanSpace ℝ (Fin 2)),
              (centerParams i).attach = pre ++ [t] ∧
                (localArcAtParam i t).vertices.getLast? = some X ∧
                  (assembledVertices i)[m] = X ∧
                    (assembledVertices i)[m + 1] = b i))
    (hlineSegmentInterSeparated :
      ∀ i {α β γ δ : ℝ}, α ≤ β → γ ≤ δ → β < γ →
        segment ℝ (AffineMap.lineMap (a i) (b i) α)
            (AffineMap.lineMap (a i) (b i) β) ∩
          segment ℝ (AffineMap.lineMap (a i) (b i) γ)
            (AffineMap.lineMap (a i) (b i) δ) =
        (∅ : Set (EuclideanSpace ℝ (Fin 2))))
    (i : ι) {m n : ℕ}
    (hm : m + 1 < (assembledVertices i).length)
    (hn : n + 1 < (assembledVertices i).length)
    (hmn : m < n)
    (hinitialIndexZero :
      ∀ ⦃k : ℕ⦄,
        (hk : k + 1 < (assembledVertices i).length) →
          endpointUnitDiskAssembly_initialRole a centerParams localArcAtParam
              assembledVertices i k hk →
            k = 0)
    (hterminalNoLater :
      ∀ ⦃k l : ℕ⦄,
        (hk : k + 1 < (assembledVertices i).length) →
        (hl : l + 1 < (assembledVertices i).length) →
        k < l →
          endpointUnitDiskAssembly_terminalRole b centerParams localArcAtParam
              assembledVertices i k hk →
            False)
    (hinter_of_forall_eq_right :
      (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        p ∈ segment ℝ (assembledVertices i)[m] (assembledVertices i)[m + 1] →
        p ∈ segment ℝ (assembledVertices i)[n] (assembledVertices i)[n + 1] →
          p = (assembledVertices i)[m + 1]) →
      (segment ℝ (assembledVertices i)[m] (assembledVertices i)[m + 1] ∩
          segment ℝ (assembledVertices i)[n] (assembledVertices i)[n + 1]) =
        if n = m + 1 then {(assembledVertices i)[n]} else ∅)
    (hattach_pairwise_lt :
      (centerParams i).attach.Pairwise
        (fun t1 t2 : {t : ℝ // t ∈ centerParams i} => t1.1 < t2.1))
    (hlocal_m :
      endpointUnitDiskAssembly_localRole centerParams localArcAtParam
        assembledVertices i m hm)
    (hinitial_n :
      endpointUnitDiskAssembly_initialRole a centerParams localArcAtParam
        assembledVertices i n hn) :
    (segment ℝ (assembledVertices i)[m] (assembledVertices i)[m + 1] ∩
        segment ℝ (assembledVertices i)[n] (assembledVertices i)[n + 1]) =
      if n = m + 1 then {(assembledVertices i)[n]} else ∅ := by
  exact False.elim (by
    have hn0 : n = 0 := hinitialIndexZero hn hinitial_n
    omega)

private lemma endpointUnitDiskAssembly_segments_local_local
    {ι : Type*} [Fintype ι]
    (a b : ι → EuclideanSpace ℝ (Fin 2))
    (T : Finset (EuclideanSpace ℝ (Fin 2)))
    (r : EuclideanSpace ℝ (Fin 2) → ℝ)
    (centerParams : ι → List ℝ)
    (centerOfParam :
      ∀ i, {t : ℝ // t ∈ centerParams i} → EuclideanSpace ℝ (Fin 2))
    (hcenterOfParam_def :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}),
        centerOfParam i t = AffineMap.lineMap (a i) (b i) t.1)
    (localArcAtParam :
      ∀ i, {t : ℝ // t ∈ centerParams i} → PolygonalArc)
    (entryPoint exitPoint :
      ∀ i, {t : ℝ // t ∈ centerParams i} → EuclideanSpace ℝ (Fin 2))
    (orderedLocalVertexBlocks :
      ∀ i, List (List (EuclideanSpace ℝ (Fin 2))))
    (assembledVertices : ι → List (EuclideanSpace ℝ (Fin 2)))
    (horderedLocalVertexBlocks_def : ∀ i,
      orderedLocalVertexBlocks i =
        (centerParams i).attach.map
          (fun t => (localArcAtParam i t).vertices))
    (hassembledVertices_def : ∀ i,
      assembledVertices i =
        EndpointUnitDiskAlternatingVertexList
          (a i) (b i) (orderedLocalVertexBlocks i))
    (hendpoint_ne : ∀ i, a i ≠ b i)
    (hcenterParams_sorted : ∀ i, (centerParams i).SortedLT)
    (hcenterOfParam_T :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}), centerOfParam i t ∈ T)
    (hlocalArcAtParam_props :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}),
        (localArcAtParam i t).source = entryPoint i t ∧
          (localArcAtParam i t).target = exitPoint i t ∧
            (localArcAtParam i t).carrier ⊆
              Metric.closedBall (centerOfParam i t) (r (centerOfParam i t)) ∧
              (localArcAtParam i t).relativeInterior ⊆
                Metric.ball (centerOfParam i t) (r (centerOfParam i t)))
    (hentryExitParameters :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}),
        (∃ s : ℝ, 0 < s ∧ s < t.1 ∧
          entryPoint i t = AffineMap.lineMap (a i) (b i) s) ∧
          (∃ s : ℝ, t.1 < s ∧ s < 1 ∧
            exitPoint i t = AffineMap.lineMap (a i) (b i) s))
    (horderedCutSeparation :
      ∀ i (t1 t2 : {t : ℝ // t ∈ centerParams i}),
        t1.1 < t2.1 →
          ∃ sExit sEntry : ℝ,
            t1.1 < sExit ∧
              sExit < sEntry ∧
                sEntry < t2.1 ∧
                  exitPoint i t1 = AffineMap.lineMap (a i) (b i) sExit ∧
                    entryPoint i t2 = AffineMap.lineMap (a i) (b i) sEntry)
    (hchordGapLocalCarrierPosition :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}) {α β e x : ℝ},
        entryPoint i t = AffineMap.lineMap (a i) (b i) e →
          exitPoint i t = AffineMap.lineMap (a i) (b i) x →
            0 ≤ α → α ≤ β → β ≤ 1 → e < x →
              (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
                p ∈ segment ℝ (AffineMap.lineMap (a i) (b i) α)
                    (AffineMap.lineMap (a i) (b i) β) →
                  p ∈ (localArcAtParam i t).carrier →
                    β < e → False) ∧
                (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
                  p ∈ segment ℝ (AffineMap.lineMap (a i) (b i) α)
                      (AffineMap.lineMap (a i) (b i) β) →
                    p ∈ (localArcAtParam i t).carrier →
                      β = e → p = entryPoint i t) ∧
                  (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
                    p ∈ segment ℝ (AffineMap.lineMap (a i) (b i) α)
                        (AffineMap.lineMap (a i) (b i) β) →
                      p ∈ (localArcAtParam i t).carrier →
                        x < α → False) ∧
                    (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
                      p ∈ segment ℝ (AffineMap.lineMap (a i) (b i) α)
                          (AffineMap.lineMap (a i) (b i) β) →
                        p ∈ (localArcAtParam i t).carrier →
                          x = α → p = exitPoint i t))
    (hinitialGapMeetsLocalCarrierOnly :
      ∀ i (t : {t : ℝ // t ∈ centerParams i})
        ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        p ∈ segment ℝ (a i) (entryPoint i t) →
          p ∈ (localArcAtParam i t).carrier → p = entryPoint i t)
    (hterminalGapMeetsLocalCarrierOnly :
      ∀ i (t : {t : ℝ // t ∈ centerParams i})
        ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        p ∈ segment ℝ (exitPoint i t) (b i) →
          p ∈ (localArcAtParam i t).carrier → p = exitPoint i t)
    (horderedOutsideGapMeetsNeighboringLocalCarriersOnly :
      ∀ i (t1 t2 : {t : ℝ // t ∈ centerParams i}),
        t1.1 < t2.1 →
          (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
            p ∈ segment ℝ (exitPoint i t1) (entryPoint i t2) →
              p ∈ (localArcAtParam i t1).carrier → p = exitPoint i t1) ∧
            (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
              p ∈ segment ℝ (exitPoint i t1) (entryPoint i t2) →
                p ∈ (localArcAtParam i t2).carrier → p = entryPoint i t2))
    (hdisjoint : ∀ ⦃z w : EuclideanSpace ℝ (Fin 2)⦄,
      z ∈ T → w ∈ T → z ≠ w →
        Disjoint (Metric.closedBall z (r z)) (Metric.closedBall w (r w)))
    (hassembledVertices_nodup : ∀ i, (assembledVertices i).Nodup)
    (hassembledVertices_avoid :
      ∀ i ⦃m k : ℕ⦄,
        (hm : m + 1 < (assembledVertices i).length) →
          (hk : k < (assembledVertices i).length) →
            k ≠ m → k ≠ m + 1 →
              (assembledVertices i)[k] ∉
                openSegment ℝ
                  (assembledVertices i)[m] (assembledVertices i)[m + 1])
    (hassembledEdgeEndpointRoles :
      ∀ i ⦃m : ℕ⦄,
        (hm : m + 1 < (assembledVertices i).length) →
          ((centerParams i).attach = [] ∧
              (assembledVertices i)[m] = a i ∧
                (assembledVertices i)[m + 1] = b i) ∨
            (∃ t ts X,
              (centerParams i).attach = t :: ts ∧
                (localArcAtParam i t).vertices.head? = some X ∧
                  (assembledVertices i)[m] = a i ∧
                    (assembledVertices i)[m + 1] = X) ∨
            (∃ (pre : List {t : ℝ // t ∈ centerParams i})
                (t : {t : ℝ // t ∈ centerParams i})
                (post : List {t : ℝ // t ∈ centerParams i}) (q : ℕ),
              ∃ hq : q + 1 < (localArcAtParam i t).vertices.length,
                (centerParams i).attach = pre ++ t :: post ∧
                  (assembledVertices i)[m] =
                    (localArcAtParam i t).vertices[q] ∧
                    (assembledVertices i)[m + 1] =
                      (localArcAtParam i t).vertices[q + 1]) ∨
            (∃ (pre : List {t : ℝ // t ∈ centerParams i})
                (t1 : {t : ℝ // t ∈ centerParams i})
                (t2 : {t : ℝ // t ∈ centerParams i})
                (post : List {t : ℝ // t ∈ centerParams i})
                (X Y : EuclideanSpace ℝ (Fin 2)),
              (centerParams i).attach = pre ++ t1 :: t2 :: post ∧
                (localArcAtParam i t1).vertices.getLast? = some X ∧
                  (localArcAtParam i t2).vertices.head? = some Y ∧
                    (assembledVertices i)[m] = X ∧
                      (assembledVertices i)[m + 1] = Y) ∨
            (∃ (pre : List {t : ℝ // t ∈ centerParams i})
                (t : {t : ℝ // t ∈ centerParams i})
                (X : EuclideanSpace ℝ (Fin 2)),
              (centerParams i).attach = pre ++ [t] ∧
                (localArcAtParam i t).vertices.getLast? = some X ∧
                  (assembledVertices i)[m] = X ∧
                    (assembledVertices i)[m + 1] = b i))
    (hlineSegmentInterSeparated :
      ∀ i {α β γ δ : ℝ}, α ≤ β → γ ≤ δ → β < γ →
        segment ℝ (AffineMap.lineMap (a i) (b i) α)
            (AffineMap.lineMap (a i) (b i) β) ∩
          segment ℝ (AffineMap.lineMap (a i) (b i) γ)
            (AffineMap.lineMap (a i) (b i) δ) =
        (∅ : Set (EuclideanSpace ℝ (Fin 2))))
    (i : ι) {m n : ℕ}
    (hm : m + 1 < (assembledVertices i).length)
    (hn : n + 1 < (assembledVertices i).length)
    (hmn : m < n)
    (hinitialIndexZero :
      ∀ ⦃k : ℕ⦄,
        (hk : k + 1 < (assembledVertices i).length) →
          endpointUnitDiskAssembly_initialRole a centerParams localArcAtParam
              assembledVertices i k hk →
            k = 0)
    (hterminalNoLater :
      ∀ ⦃k l : ℕ⦄,
        (hk : k + 1 < (assembledVertices i).length) →
        (hl : l + 1 < (assembledVertices i).length) →
        k < l →
          endpointUnitDiskAssembly_terminalRole b centerParams localArcAtParam
              assembledVertices i k hk →
            False)
    (hinter_of_forall_eq_right :
      (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        p ∈ segment ℝ (assembledVertices i)[m] (assembledVertices i)[m + 1] →
        p ∈ segment ℝ (assembledVertices i)[n] (assembledVertices i)[n + 1] →
          p = (assembledVertices i)[m + 1]) →
      (segment ℝ (assembledVertices i)[m] (assembledVertices i)[m + 1] ∩
          segment ℝ (assembledVertices i)[n] (assembledVertices i)[n + 1]) =
        if n = m + 1 then {(assembledVertices i)[n]} else ∅)
    (hattach_pairwise_lt :
      (centerParams i).attach.Pairwise
        (fun t1 t2 : {t : ℝ // t ∈ centerParams i} => t1.1 < t2.1))
    (hlocal_m :
      endpointUnitDiskAssembly_localRole centerParams localArcAtParam
        assembledVertices i m hm)
    (hlocal_n :
      endpointUnitDiskAssembly_localRole centerParams localArcAtParam
        assembledVertices i n hn) :
    (segment ℝ (assembledVertices i)[m] (assembledVertices i)[m + 1] ∩
        segment ℝ (assembledVertices i)[n] (assembledVertices i)[n + 1]) =
      if n = m + 1 then {(assembledVertices i)[n]} else ∅ := by
  rcases hlocal_m with
    ⟨pre_m, t_m, post_m, q_m, hq_m, hitems_m,
      hleft_m, hright_m⟩
  rcases hlocal_n with
    ⟨pre_n, t_n, post_n, q_n, hq_n, hitems_n,
      hleft_n, hright_n⟩
  exact hinter_of_forall_eq_right (by
    intro p hp_m hp_n
    have hp_m_local :
        p ∈ segment ℝ (localArcAtParam i t_m).vertices[q_m]
            (localArcAtParam i t_m).vertices[q_m + 1] := by
      simpa [hleft_m, hright_m] using hp_m
    have hp_n_local :
        p ∈ segment ℝ (localArcAtParam i t_n).vertices[q_n]
            (localArcAtParam i t_n).vertices[q_n + 1] := by
      simpa [hleft_n, hright_n] using hp_n
    have hp_carrier_m :
        p ∈ (localArcAtParam i t_m).carrier := by
      rw [(localArcAtParam i t_m).carrier_eq]
      exact ⟨q_m, hq_m, hp_m_local⟩
    have hp_carrier_n :
        p ∈ (localArcAtParam i t_n).carrier := by
      rw [(localArcAtParam i t_n).carrier_eq]
      exact ⟨q_n, hq_n, hp_n_local⟩
    by_cases ht_eq : t_m = t_n
    · subst t_n
      rcases lt_trichotomy q_m q_n with hqm_lt_qn | hqm_eq_qn | hqn_lt_qm
      · have hinter :=
          (localArcAtParam i t_m).segment_intersections hq_m hq_n hqm_lt_qn
        have hp_inter :
            p ∈ segment ℝ (localArcAtParam i t_m).vertices[q_m]
                (localArcAtParam i t_m).vertices[q_m + 1] ∩
              segment ℝ (localArcAtParam i t_m).vertices[q_n]
                (localArcAtParam i t_m).vertices[q_n + 1] :=
          ⟨hp_m_local, hp_n_local⟩
        by_cases hAdj : q_n = q_m + 1
        · have hp_single :
              p ∈ ({(localArcAtParam i t_m).vertices[q_m + 1]} :
                Set (EuclideanSpace ℝ (Fin 2))) := by
            subst q_n
            have hp_inter' := hp_inter
            rw [hinter] at hp_inter'
            simpa using hp_inter'
          have hp_eq :
              p = (localArcAtParam i t_m).vertices[q_m + 1] := by
            simpa using hp_single
          calc
            p = (localArcAtParam i t_m).vertices[q_m + 1] := hp_eq
            _ = (assembledVertices i)[m + 1] := by
              simpa using hright_m.symm
        · have hp_empty :
              p ∈ (∅ : Set (EuclideanSpace ℝ (Fin 2))) := by
            have hp_inter' := hp_inter
            rw [hinter] at hp_inter'
            simpa [hAdj] using hp_inter'
          exact False.elim hp_empty
      · subst q_n
        have hm_lt : m < (assembledVertices i).length :=
          Nat.lt_trans (Nat.lt_succ_self m) hm
        have hn_lt : n < (assembledVertices i).length :=
          Nat.lt_trans (Nat.lt_succ_self n) hn
        have hmn_eq : m = n := by
          have hval :
              (assembledVertices i)[m] =
                (assembledVertices i)[n] := by
            rw [hleft_m, hleft_n]
          exact ((hassembledVertices_nodup i).getElem_inj_iff).1 hval
        exact False.elim (by omega)
      · have hinter :=
          (localArcAtParam i t_m).segment_intersections hq_n hq_m hqn_lt_qm
        have hp_inter :
            p ∈ segment ℝ (localArcAtParam i t_m).vertices[q_n]
                (localArcAtParam i t_m).vertices[q_n + 1] ∩
              segment ℝ (localArcAtParam i t_m).vertices[q_m]
                (localArcAtParam i t_m).vertices[q_m + 1] :=
          ⟨hp_n_local, hp_m_local⟩
        by_cases hAdj : q_m = q_n + 1
        · subst q_m
          have hp_single :
              p ∈ ({(localArcAtParam i t_m).vertices[q_n + 1]} :
                Set (EuclideanSpace ℝ (Fin 2))) := by
            have hp_inter' := hp_inter
            rw [hinter] at hp_inter'
            simpa using hp_inter'
          have hp_eq :
              p = (localArcAtParam i t_m).vertices[q_n + 1] := by
            simpa using hp_single
          have hp_eq_m : p = (assembledVertices i)[m] := by
            simpa [hleft_m] using hp_eq
          have hm_lt : m < (assembledVertices i).length :=
            Nat.lt_trans (Nat.lt_succ_self m) hm
          have hleft_ne :
              (assembledVertices i)[n] ≠ (assembledVertices i)[m] := by
            intro hEq
            have hidx :=
              ((hassembledVertices_nodup i).getElem_inj_iff).1 hEq
            omega
          have hright_ne :
              (assembledVertices i)[n + 1] ≠
                (assembledVertices i)[m] := by
            intro hEq
            have hidx :=
              ((hassembledVertices_nodup i).getElem_inj_iff).1 hEq
            omega
          have hpseg_n :
              (assembledVertices i)[m] ∈
                segment ℝ (assembledVertices i)[n]
                  (assembledVertices i)[n + 1] := by
            simpa [hp_eq_m] using hp_n
          have hpopen_n :
              (assembledVertices i)[m] ∈
                openSegment ℝ (assembledVertices i)[n]
                  (assembledVertices i)[n + 1] :=
            mem_openSegment_of_ne_left_right (𝕜 := ℝ)
              hleft_ne hright_ne hpseg_n
          exact False.elim
            (hassembledVertices_avoid i hn hm_lt
              (by omega) (by omega) hpopen_n)
        · have hp_empty :
              p ∈ (∅ : Set (EuclideanSpace ℝ (Fin 2))) := by
            have hp_inter' := hp_inter
            rw [hinter] at hp_inter'
            simpa [hAdj] using hp_inter'
          exact False.elim hp_empty
    · have hcenter_ne :
        centerOfParam i t_m ≠ centerOfParam i t_n := by
        intro hcenter
        have hparam : t_m.1 = t_n.1 := by
          have hinj :=
            AffineMap.lineMap_injective (k := ℝ) (hendpoint_ne i)
          exact hinj (by
            rw [hcenterOfParam_def i t_m,
              hcenterOfParam_def i t_n] at hcenter
            exact hcenter)
        exact ht_eq (Subtype.ext hparam)
      have hp_closed_m :
          p ∈ Metric.closedBall (centerOfParam i t_m)
            (r (centerOfParam i t_m)) :=
        (hlocalArcAtParam_props i t_m).2.2.1 hp_carrier_m
      have hp_closed_n :
          p ∈ Metric.closedBall (centerOfParam i t_n)
            (r (centerOfParam i t_n)) :=
        (hlocalArcAtParam_props i t_n).2.2.1 hp_carrier_n
      exact False.elim
        ((Set.disjoint_left.mp
          (hdisjoint (hcenterOfParam_T i t_m)
            (hcenterOfParam_T i t_n) hcenter_ne))
          hp_closed_m hp_closed_n))

private lemma endpointUnitDiskAssembly_segments_local_bridge
    {ι : Type*} [Fintype ι]
    (a b : ι → EuclideanSpace ℝ (Fin 2))
    (T : Finset (EuclideanSpace ℝ (Fin 2)))
    (r : EuclideanSpace ℝ (Fin 2) → ℝ)
    (centerParams : ι → List ℝ)
    (centerOfParam :
      ∀ i, {t : ℝ // t ∈ centerParams i} → EuclideanSpace ℝ (Fin 2))
    (hcenterOfParam_def :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}),
        centerOfParam i t = AffineMap.lineMap (a i) (b i) t.1)
    (localArcAtParam :
      ∀ i, {t : ℝ // t ∈ centerParams i} → PolygonalArc)
    (entryPoint exitPoint :
      ∀ i, {t : ℝ // t ∈ centerParams i} → EuclideanSpace ℝ (Fin 2))
    (orderedLocalVertexBlocks :
      ∀ i, List (List (EuclideanSpace ℝ (Fin 2))))
    (assembledVertices : ι → List (EuclideanSpace ℝ (Fin 2)))
    (horderedLocalVertexBlocks_def : ∀ i,
      orderedLocalVertexBlocks i =
        (centerParams i).attach.map
          (fun t => (localArcAtParam i t).vertices))
    (hassembledVertices_def : ∀ i,
      assembledVertices i =
        EndpointUnitDiskAlternatingVertexList
          (a i) (b i) (orderedLocalVertexBlocks i))
    (hendpoint_ne : ∀ i, a i ≠ b i)
    (hcenterParams_sorted : ∀ i, (centerParams i).SortedLT)
    (hcenterOfParam_T :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}), centerOfParam i t ∈ T)
    (hlocalArcAtParam_props :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}),
        (localArcAtParam i t).source = entryPoint i t ∧
          (localArcAtParam i t).target = exitPoint i t ∧
            (localArcAtParam i t).carrier ⊆
              Metric.closedBall (centerOfParam i t) (r (centerOfParam i t)) ∧
              (localArcAtParam i t).relativeInterior ⊆
                Metric.ball (centerOfParam i t) (r (centerOfParam i t)))
    (hentryExitParameters :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}),
        (∃ s : ℝ, 0 < s ∧ s < t.1 ∧
          entryPoint i t = AffineMap.lineMap (a i) (b i) s) ∧
          (∃ s : ℝ, t.1 < s ∧ s < 1 ∧
            exitPoint i t = AffineMap.lineMap (a i) (b i) s))
    (horderedCutSeparation :
      ∀ i (t1 t2 : {t : ℝ // t ∈ centerParams i}),
        t1.1 < t2.1 →
          ∃ sExit sEntry : ℝ,
            t1.1 < sExit ∧
              sExit < sEntry ∧
                sEntry < t2.1 ∧
                  exitPoint i t1 = AffineMap.lineMap (a i) (b i) sExit ∧
                    entryPoint i t2 = AffineMap.lineMap (a i) (b i) sEntry)
    (hchordGapLocalCarrierPosition :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}) {α β e x : ℝ},
        entryPoint i t = AffineMap.lineMap (a i) (b i) e →
          exitPoint i t = AffineMap.lineMap (a i) (b i) x →
            0 ≤ α → α ≤ β → β ≤ 1 → e < x →
              (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
                p ∈ segment ℝ (AffineMap.lineMap (a i) (b i) α)
                    (AffineMap.lineMap (a i) (b i) β) →
                  p ∈ (localArcAtParam i t).carrier →
                    β < e → False) ∧
                (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
                  p ∈ segment ℝ (AffineMap.lineMap (a i) (b i) α)
                      (AffineMap.lineMap (a i) (b i) β) →
                    p ∈ (localArcAtParam i t).carrier →
                      β = e → p = entryPoint i t) ∧
                  (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
                    p ∈ segment ℝ (AffineMap.lineMap (a i) (b i) α)
                        (AffineMap.lineMap (a i) (b i) β) →
                      p ∈ (localArcAtParam i t).carrier →
                        x < α → False) ∧
                    (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
                      p ∈ segment ℝ (AffineMap.lineMap (a i) (b i) α)
                          (AffineMap.lineMap (a i) (b i) β) →
                        p ∈ (localArcAtParam i t).carrier →
                          x = α → p = exitPoint i t))
    (hinitialGapMeetsLocalCarrierOnly :
      ∀ i (t : {t : ℝ // t ∈ centerParams i})
        ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        p ∈ segment ℝ (a i) (entryPoint i t) →
          p ∈ (localArcAtParam i t).carrier → p = entryPoint i t)
    (hterminalGapMeetsLocalCarrierOnly :
      ∀ i (t : {t : ℝ // t ∈ centerParams i})
        ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        p ∈ segment ℝ (exitPoint i t) (b i) →
          p ∈ (localArcAtParam i t).carrier → p = exitPoint i t)
    (horderedOutsideGapMeetsNeighboringLocalCarriersOnly :
      ∀ i (t1 t2 : {t : ℝ // t ∈ centerParams i}),
        t1.1 < t2.1 →
          (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
            p ∈ segment ℝ (exitPoint i t1) (entryPoint i t2) →
              p ∈ (localArcAtParam i t1).carrier → p = exitPoint i t1) ∧
            (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
              p ∈ segment ℝ (exitPoint i t1) (entryPoint i t2) →
                p ∈ (localArcAtParam i t2).carrier → p = entryPoint i t2))
    (hdisjoint : ∀ ⦃z w : EuclideanSpace ℝ (Fin 2)⦄,
      z ∈ T → w ∈ T → z ≠ w →
        Disjoint (Metric.closedBall z (r z)) (Metric.closedBall w (r w)))
    (hassembledVertices_nodup : ∀ i, (assembledVertices i).Nodup)
    (hassembledVertices_avoid :
      ∀ i ⦃m k : ℕ⦄,
        (hm : m + 1 < (assembledVertices i).length) →
          (hk : k < (assembledVertices i).length) →
            k ≠ m → k ≠ m + 1 →
              (assembledVertices i)[k] ∉
                openSegment ℝ
                  (assembledVertices i)[m] (assembledVertices i)[m + 1])
    (hassembledEdgeEndpointRoles :
      ∀ i ⦃m : ℕ⦄,
        (hm : m + 1 < (assembledVertices i).length) →
          ((centerParams i).attach = [] ∧
              (assembledVertices i)[m] = a i ∧
                (assembledVertices i)[m + 1] = b i) ∨
            (∃ t ts X,
              (centerParams i).attach = t :: ts ∧
                (localArcAtParam i t).vertices.head? = some X ∧
                  (assembledVertices i)[m] = a i ∧
                    (assembledVertices i)[m + 1] = X) ∨
            (∃ (pre : List {t : ℝ // t ∈ centerParams i})
                (t : {t : ℝ // t ∈ centerParams i})
                (post : List {t : ℝ // t ∈ centerParams i}) (q : ℕ),
              ∃ hq : q + 1 < (localArcAtParam i t).vertices.length,
                (centerParams i).attach = pre ++ t :: post ∧
                  (assembledVertices i)[m] =
                    (localArcAtParam i t).vertices[q] ∧
                    (assembledVertices i)[m + 1] =
                      (localArcAtParam i t).vertices[q + 1]) ∨
            (∃ (pre : List {t : ℝ // t ∈ centerParams i})
                (t1 : {t : ℝ // t ∈ centerParams i})
                (t2 : {t : ℝ // t ∈ centerParams i})
                (post : List {t : ℝ // t ∈ centerParams i})
                (X Y : EuclideanSpace ℝ (Fin 2)),
              (centerParams i).attach = pre ++ t1 :: t2 :: post ∧
                (localArcAtParam i t1).vertices.getLast? = some X ∧
                  (localArcAtParam i t2).vertices.head? = some Y ∧
                    (assembledVertices i)[m] = X ∧
                      (assembledVertices i)[m + 1] = Y) ∨
            (∃ (pre : List {t : ℝ // t ∈ centerParams i})
                (t : {t : ℝ // t ∈ centerParams i})
                (X : EuclideanSpace ℝ (Fin 2)),
              (centerParams i).attach = pre ++ [t] ∧
                (localArcAtParam i t).vertices.getLast? = some X ∧
                  (assembledVertices i)[m] = X ∧
                    (assembledVertices i)[m + 1] = b i))
    (hlineSegmentInterSeparated :
      ∀ i {α β γ δ : ℝ}, α ≤ β → γ ≤ δ → β < γ →
        segment ℝ (AffineMap.lineMap (a i) (b i) α)
            (AffineMap.lineMap (a i) (b i) β) ∩
          segment ℝ (AffineMap.lineMap (a i) (b i) γ)
            (AffineMap.lineMap (a i) (b i) δ) =
        (∅ : Set (EuclideanSpace ℝ (Fin 2))))
    (i : ι) {m n : ℕ}
    (hm : m + 1 < (assembledVertices i).length)
    (hn : n + 1 < (assembledVertices i).length)
    (hmn : m < n)
    (hinitialIndexZero :
      ∀ ⦃k : ℕ⦄,
        (hk : k + 1 < (assembledVertices i).length) →
          endpointUnitDiskAssembly_initialRole a centerParams localArcAtParam
              assembledVertices i k hk →
            k = 0)
    (hterminalNoLater :
      ∀ ⦃k l : ℕ⦄,
        (hk : k + 1 < (assembledVertices i).length) →
        (hl : l + 1 < (assembledVertices i).length) →
        k < l →
          endpointUnitDiskAssembly_terminalRole b centerParams localArcAtParam
              assembledVertices i k hk →
            False)
    (hinter_of_forall_eq_right :
      (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        p ∈ segment ℝ (assembledVertices i)[m] (assembledVertices i)[m + 1] →
        p ∈ segment ℝ (assembledVertices i)[n] (assembledVertices i)[n + 1] →
          p = (assembledVertices i)[m + 1]) →
      (segment ℝ (assembledVertices i)[m] (assembledVertices i)[m + 1] ∩
          segment ℝ (assembledVertices i)[n] (assembledVertices i)[n + 1]) =
        if n = m + 1 then {(assembledVertices i)[n]} else ∅)
    (hattach_pairwise_lt :
      (centerParams i).attach.Pairwise
        (fun t1 t2 : {t : ℝ // t ∈ centerParams i} => t1.1 < t2.1))
    (hlocal_m :
      endpointUnitDiskAssembly_localRole centerParams localArcAtParam
        assembledVertices i m hm)
    (hbridge_n :
      endpointUnitDiskAssembly_bridgeRole centerParams localArcAtParam
        assembledVertices i n hn) :
    (segment ℝ (assembledVertices i)[m] (assembledVertices i)[m + 1] ∩
        segment ℝ (assembledVertices i)[n] (assembledVertices i)[n + 1]) =
      if n = m + 1 then {(assembledVertices i)[n]} else ∅ := by
  rcases hlocal_m with
    ⟨pre_m, t_m, post_m, q_m, hq_m, hitems_m,
      hleft_m, hright_m⟩
  rcases hbridge_n with
    ⟨pre_n, t1_n, t2_n, post_n, X_n, Y_n, hitems_n,
      hlast_n, hhead_n, hleft_n, hright_n⟩
  exact hinter_of_forall_eq_right (by
    intro p hp_local hp_bridge
    have hp_local' :
        p ∈ segment ℝ (localArcAtParam i t_m).vertices[q_m]
            (localArcAtParam i t_m).vertices[q_m + 1] := by
      simpa [hleft_m, hright_m] using hp_local
    have hp_carrier :
        p ∈ (localArcAtParam i t_m).carrier := by
      rw [(localArcAtParam i t_m).carrier_eq]
      exact ⟨q_m, hq_m, hp_local'⟩
    have hlast_exit_n :
        (localArcAtParam i t1_n).vertices.getLast? =
          some (exitPoint i t1_n) := by
      have htarget := (localArcAtParam i t1_n).target_eq_last
      rw [(hlocalArcAtParam_props i t1_n).2.1] at htarget
      exact htarget
    have hX_n : X_n = exitPoint i t1_n := by
      exact (Option.some.inj (hlast_exit_n.symm.trans hlast_n)).symm
    have hhead_entry_n :
        (localArcAtParam i t2_n).vertices.head? =
          some (entryPoint i t2_n) := by
      have hsource := (localArcAtParam i t2_n).source_eq_head
      rw [(hlocalArcAtParam_props i t2_n).1] at hsource
      exact hsource
    have hY_n : Y_n = entryPoint i t2_n := by
      exact (Option.some.inj (hhead_entry_n.symm.trans hhead_n)).symm
    have hp_bridge_gap :
        p ∈ segment ℝ (exitPoint i t1_n) (entryPoint i t2_n) := by
      simpa [hleft_n, hright_n, hX_n, hY_n] using hp_bridge
    have hpair_bridge := hattach_pairwise_lt
    rw [hitems_n] at hpair_bridge
    have htail_pair :
        (t1_n :: t2_n :: post_n).Pairwise
          (fun u v : {t : ℝ // t ∈ centerParams i} => u.1 < v.1) :=
      (List.pairwise_append.1 hpair_bridge).2.1
    have ht12 : t1_n.1 < t2_n.1 :=
      (List.pairwise_cons.1 htail_pair).1 t2_n (by simp)
    rcases hentryExitParameters i t1_n with
      ⟨⟨e1, he1_pos, he1_lt_t1, hentry1⟩,
        ⟨x1, ht1_lt_x1, hx1_lt_one, hexit1⟩⟩
    rcases hentryExitParameters i t2_n with
      ⟨⟨e2, he2_pos, he2_lt_t2, hentry2⟩,
        ⟨x2, ht2_lt_x2, hx2_lt_one, hexit2⟩⟩
    rcases horderedCutSeparation i t1_n t2_n ht12 with
      ⟨sExit, sEntry, _ht1_sExit, hsExitEntry, _hsEntry_t2,
        hexit_order, hentry_order⟩
    let f : ℝ →ᵃ[ℝ] EuclideanSpace ℝ (Fin 2) :=
      AffineMap.lineMap (a i) (b i)
    have hf : Function.Injective f :=
      AffineMap.lineMap_injective (k := ℝ) (hendpoint_ne i)
    have hx1_eq : x1 = sExit := by
      exact hf (by rw [← hexit1, ← hexit_order])
    have he2_eq : e2 = sEntry := by
      exact hf (by rw [← hentry2, ← hentry_order])
    have hx1_lt_e2 : x1 < e2 := by
      linarith
    have ht_m_attach : t_m ∈ (centerParams i).attach := by
      rw [hitems_m]
      simp
    have ht_cases :
        t_m ∈ pre_n ∨ t_m = t1_n ∨ t_m = t2_n ∨ t_m ∈ post_n := by
      have ht_mem : t_m ∈ pre_n ++ t1_n :: t2_n :: post_n := by
        simpa [hitems_n] using ht_m_attach
      simpa [List.mem_append, List.mem_cons] using ht_mem
    rcases ht_cases with ht_pre | ht_cases
    · have ht_m_lt_t1 : t_m.1 < t1_n.1 :=
        (List.pairwise_append.1 hpair_bridge).2.2
          t_m ht_pre t1_n (by simp)
      rcases hentryExitParameters i t_m with
        ⟨⟨e_m, he_m_pos, he_m_lt_t_m, hentry_m⟩,
          ⟨x_m, ht_m_lt_x_m, hx_m_lt_one, hexit_m⟩⟩
      rcases horderedCutSeparation i t_m t1_n ht_m_lt_t1 with
        ⟨sExit', sEntry', _ht_m_sExit', hsExitEntry',
          _hsEntry_t1, hexit_order', hentry_order'⟩
      have hx_m_eq : x_m = sExit' := by
        exact hf (by rw [← hexit_m, ← hexit_order'])
      have he1_eq : e1 = sEntry' := by
        exact hf (by rw [← hentry1, ← hentry_order'])
      have hx_m_lt_x1 : x_m < x1 := by
        linarith
      have hpseg_param :
          p ∈ segment ℝ (AffineMap.lineMap (a i) (b i) x1)
              (AffineMap.lineMap (a i) (b i) e2) := by
        simpa [f, hexit1, hentry2] using hp_bridge_gap
      exact False.elim
        ((hchordGapLocalCarrierPosition i t_m
          (α := x1) (β := e2) (e := e_m) (x := x_m)
          hentry_m hexit_m (by linarith) hx1_lt_e2.le
          (by linarith) (by linarith)).2.2.1
            hpseg_param hp_carrier hx_m_lt_x1)
    rcases ht_cases with ht_eq1 | ht_cases
    · subst t_m
      have hp_eq_exit :
          p = exitPoint i t1_n :=
        (horderedOutsideGapMeetsNeighboringLocalCarriersOnly
          i t1_n t2_n ht12).1 hp_bridge_gap hp_carrier
      have hlast_exit :
          (localArcAtParam i t1_n).vertices.getLast? =
            some (exitPoint i t1_n) := by
        have htarget := (localArcAtParam i t1_n).target_eq_last
        rw [(hlocalArcAtParam_props i t1_n).2.1] at htarget
        exact htarget
      by_cases hq_last :
          q_m + 1 = (localArcAtParam i t1_n).vertices.length - 1
      · have hlast_get :
            (localArcAtParam i t1_n).vertices.getLast? =
              some ((localArcAtParam i t1_n).vertices[q_m + 1]) := by
          rw [List.getLast?_eq_getElem?]
          rw [show (localArcAtParam i t1_n).vertices.length - 1 =
              q_m + 1 by omega]
          rw [List.getElem?_eq_getElem hq_m]
        have hright_exit :
            (localArcAtParam i t1_n).vertices[q_m + 1] =
              exitPoint i t1_n :=
          Option.some.inj (hlast_get.symm.trans hlast_exit)
        calc
          p = exitPoint i t1_n := hp_eq_exit
          _ = (localArcAtParam i t1_n).vertices[q_m + 1] :=
            hright_exit.symm
          _ = (assembledVertices i)[m + 1] := by
            simpa using hright_m.symm
      · have hlast_index :
            (localArcAtParam i t1_n).vertices.length - 1 <
              (localArcAtParam i t1_n).vertices.length := by
          have hlen := (localArcAtParam i t1_n).length_ge_two
          omega
        have hlast_get :
            (localArcAtParam i t1_n).vertices.getLast? =
              some (((localArcAtParam i t1_n).vertices)[
                (localArcAtParam i t1_n).vertices.length - 1]) := by
          rw [List.getLast?_eq_getElem?]
          rw [List.getElem?_eq_getElem hlast_index]
        have hlast_value :
            ((localArcAtParam i t1_n).vertices)[
                (localArcAtParam i t1_n).vertices.length - 1] =
              exitPoint i t1_n :=
          Option.some.inj (hlast_get.symm.trans hlast_exit)
        have hleft_ne :
            (localArcAtParam i t1_n).vertices[q_m] ≠
              exitPoint i t1_n := by
          intro hEq
          have hval :
              (localArcAtParam i t1_n).vertices[q_m] =
                ((localArcAtParam i t1_n).vertices)[
                  (localArcAtParam i t1_n).vertices.length - 1] := by
            rw [hEq, hlast_value]
          have hidx :=
            ((localArcAtParam i t1_n).simple_vertices.getElem_inj_iff).1 hval
          omega
        have hright_ne :
            (localArcAtParam i t1_n).vertices[q_m + 1] ≠
              exitPoint i t1_n := by
          intro hEq
          have hval :
              (localArcAtParam i t1_n).vertices[q_m + 1] =
                ((localArcAtParam i t1_n).vertices)[
                  (localArcAtParam i t1_n).vertices.length - 1] := by
            rw [hEq, hlast_value]
          have hidx :=
            ((localArcAtParam i t1_n).simple_vertices.getElem_inj_iff).1 hval
          omega
        have hpseg_exit :
            exitPoint i t1_n ∈
              segment ℝ (localArcAtParam i t1_n).vertices[q_m]
                (localArcAtParam i t1_n).vertices[q_m + 1] := by
          simpa [hp_eq_exit] using hp_local'
        have hpopen_exit :
            exitPoint i t1_n ∈
              openSegment ℝ (localArcAtParam i t1_n).vertices[q_m]
                (localArcAtParam i t1_n).vertices[q_m + 1] :=
          mem_openSegment_of_ne_left_right (𝕜 := ℝ)
            hleft_ne hright_ne hpseg_exit
        have hpopen_last :
            ((localArcAtParam i t1_n).vertices)[
                (localArcAtParam i t1_n).vertices.length - 1] ∈
              openSegment ℝ (localArcAtParam i t1_n).vertices[q_m]
                (localArcAtParam i t1_n).vertices[q_m + 1] := by
          simpa [hlast_value] using hpopen_exit
        exact False.elim
          ((localArcAtParam i t1_n).vertices_avoid_nonincident_interiors
            hq_m hlast_index (by omega) (by omega) hpopen_last)
    rcases ht_cases with ht_eq2 | ht_post
    · subst t_m
      have hp_eq_entry :
          p = entryPoint i t2_n :=
        (horderedOutsideGapMeetsNeighboringLocalCarriersOnly
          i t1_n t2_n ht12).2 hp_bridge_gap hp_carrier
      have hhead_entry :
          (localArcAtParam i t2_n).vertices.head? =
            some (entryPoint i t2_n) := by
        have hsource := (localArcAtParam i t2_n).source_eq_head
        rw [(hlocalArcAtParam_props i t2_n).1] at hsource
        exact hsource
      have hfirst_index :
          0 < (localArcAtParam i t2_n).vertices.length := by
        have hlen := (localArcAtParam i t2_n).length_ge_two
        omega
      have hfirst_get :
          (localArcAtParam i t2_n).vertices.head? =
            some ((localArcAtParam i t2_n).vertices[0]) := by
        rw [List.head?_eq_getElem?]
        rw [List.getElem?_eq_getElem hfirst_index]
      have hfirst_value :
          (localArcAtParam i t2_n).vertices[0] =
            entryPoint i t2_n :=
        Option.some.inj (hfirst_get.symm.trans hhead_entry)
      by_cases hq_zero : q_m = 0
      · have hval :
            (assembledVertices i)[m] =
              (assembledVertices i)[n + 1] := by
          rw [hleft_m, hright_n, hY_n]
          simpa [hq_zero, hfirst_value]
        have hm_lt : m < (assembledVertices i).length :=
          Nat.lt_trans (Nat.lt_succ_self m) hm
        have hidx :=
          ((hassembledVertices_nodup i).getElem_inj_iff).1 hval
        exact False.elim (by omega)
      · have hleft_ne :
            (localArcAtParam i t2_n).vertices[q_m] ≠
              entryPoint i t2_n := by
          intro hEq
          have hval :
              (localArcAtParam i t2_n).vertices[q_m] =
                (localArcAtParam i t2_n).vertices[0] := by
            rw [hEq, hfirst_value]
          have hq_left :
              q_m < (localArcAtParam i t2_n).vertices.length :=
            Nat.lt_trans (Nat.lt_succ_self q_m) hq_m
          have hidx :=
            ((localArcAtParam i t2_n).simple_vertices.getElem_inj_iff).1 hval
          exact hq_zero hidx
        have hright_ne :
            (localArcAtParam i t2_n).vertices[q_m + 1] ≠
              entryPoint i t2_n := by
          intro hEq
          have hval :
              (localArcAtParam i t2_n).vertices[q_m + 1] =
                (localArcAtParam i t2_n).vertices[0] := by
            rw [hEq, hfirst_value]
          have hidx :=
            ((localArcAtParam i t2_n).simple_vertices.getElem_inj_iff).1 hval
          omega
        have hpseg_entry :
            entryPoint i t2_n ∈
              segment ℝ (localArcAtParam i t2_n).vertices[q_m]
                (localArcAtParam i t2_n).vertices[q_m + 1] := by
          simpa [hp_eq_entry] using hp_local'
        have hpopen_entry :
            entryPoint i t2_n ∈
              openSegment ℝ (localArcAtParam i t2_n).vertices[q_m]
                (localArcAtParam i t2_n).vertices[q_m + 1] :=
          mem_openSegment_of_ne_left_right (𝕜 := ℝ)
            hleft_ne hright_ne hpseg_entry
        have hpopen_first :
            (localArcAtParam i t2_n).vertices[0] ∈
              openSegment ℝ (localArcAtParam i t2_n).vertices[q_m]
                (localArcAtParam i t2_n).vertices[q_m + 1] := by
          simpa [hfirst_value] using hpopen_entry
        exact False.elim
          ((localArcAtParam i t2_n).vertices_avoid_nonincident_interiors
            hq_m hfirst_index (by omega) (by omega) hpopen_first)
    · have hprefix_pair :
        ((pre_n ++ [t1_n, t2_n]) ++ post_n).Pairwise
          (fun u v : {t : ℝ // t ∈ centerParams i} => u.1 < v.1) := by
        simpa [List.append_assoc] using hpair_bridge
      have ht2_lt_tm : t2_n.1 < t_m.1 :=
        (List.pairwise_append.1 hprefix_pair).2.2
          t2_n (by simp) t_m ht_post
      rcases hentryExitParameters i t_m with
        ⟨⟨e_m, he_m_pos, he_m_lt_t_m, hentry_m⟩,
          ⟨x_m, ht_m_lt_x_m, hx_m_lt_one, hexit_m⟩⟩
      rcases horderedCutSeparation i t2_n t_m ht2_lt_tm with
        ⟨sExit', sEntry', _ht2_sExit', hsExitEntry',
          _hsEntry_tm, _hexit_order', hentry_order'⟩
      have he_m_eq : e_m = sEntry' := by
        exact hf (by rw [← hentry_m, ← hentry_order'])
      have he2_lt_e_m : e2 < e_m := by
        linarith
      have hpseg_param :
          p ∈ segment ℝ (AffineMap.lineMap (a i) (b i) x1)
              (AffineMap.lineMap (a i) (b i) e2) := by
        simpa [f, hexit1, hentry2] using hp_bridge_gap
      exact False.elim
        ((hchordGapLocalCarrierPosition i t_m
          (α := x1) (β := e2) (e := e_m) (x := x_m)
          hentry_m hexit_m (by linarith) hx1_lt_e2.le
          (by linarith) (by linarith)).1
            hpseg_param hp_carrier he2_lt_e_m))

private lemma endpointUnitDiskAssembly_segments_local_terminal
    {ι : Type*} [Fintype ι]
    (a b : ι → EuclideanSpace ℝ (Fin 2))
    (T : Finset (EuclideanSpace ℝ (Fin 2)))
    (r : EuclideanSpace ℝ (Fin 2) → ℝ)
    (centerParams : ι → List ℝ)
    (centerOfParam :
      ∀ i, {t : ℝ // t ∈ centerParams i} → EuclideanSpace ℝ (Fin 2))
    (hcenterOfParam_def :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}),
        centerOfParam i t = AffineMap.lineMap (a i) (b i) t.1)
    (localArcAtParam :
      ∀ i, {t : ℝ // t ∈ centerParams i} → PolygonalArc)
    (entryPoint exitPoint :
      ∀ i, {t : ℝ // t ∈ centerParams i} → EuclideanSpace ℝ (Fin 2))
    (orderedLocalVertexBlocks :
      ∀ i, List (List (EuclideanSpace ℝ (Fin 2))))
    (assembledVertices : ι → List (EuclideanSpace ℝ (Fin 2)))
    (horderedLocalVertexBlocks_def : ∀ i,
      orderedLocalVertexBlocks i =
        (centerParams i).attach.map
          (fun t => (localArcAtParam i t).vertices))
    (hassembledVertices_def : ∀ i,
      assembledVertices i =
        EndpointUnitDiskAlternatingVertexList
          (a i) (b i) (orderedLocalVertexBlocks i))
    (hendpoint_ne : ∀ i, a i ≠ b i)
    (hcenterParams_sorted : ∀ i, (centerParams i).SortedLT)
    (hcenterOfParam_T :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}), centerOfParam i t ∈ T)
    (hlocalArcAtParam_props :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}),
        (localArcAtParam i t).source = entryPoint i t ∧
          (localArcAtParam i t).target = exitPoint i t ∧
            (localArcAtParam i t).carrier ⊆
              Metric.closedBall (centerOfParam i t) (r (centerOfParam i t)) ∧
              (localArcAtParam i t).relativeInterior ⊆
                Metric.ball (centerOfParam i t) (r (centerOfParam i t)))
    (hentryExitParameters :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}),
        (∃ s : ℝ, 0 < s ∧ s < t.1 ∧
          entryPoint i t = AffineMap.lineMap (a i) (b i) s) ∧
          (∃ s : ℝ, t.1 < s ∧ s < 1 ∧
            exitPoint i t = AffineMap.lineMap (a i) (b i) s))
    (horderedCutSeparation :
      ∀ i (t1 t2 : {t : ℝ // t ∈ centerParams i}),
        t1.1 < t2.1 →
          ∃ sExit sEntry : ℝ,
            t1.1 < sExit ∧
              sExit < sEntry ∧
                sEntry < t2.1 ∧
                  exitPoint i t1 = AffineMap.lineMap (a i) (b i) sExit ∧
                    entryPoint i t2 = AffineMap.lineMap (a i) (b i) sEntry)
    (hchordGapLocalCarrierPosition :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}) {α β e x : ℝ},
        entryPoint i t = AffineMap.lineMap (a i) (b i) e →
          exitPoint i t = AffineMap.lineMap (a i) (b i) x →
            0 ≤ α → α ≤ β → β ≤ 1 → e < x →
              (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
                p ∈ segment ℝ (AffineMap.lineMap (a i) (b i) α)
                    (AffineMap.lineMap (a i) (b i) β) →
                  p ∈ (localArcAtParam i t).carrier →
                    β < e → False) ∧
                (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
                  p ∈ segment ℝ (AffineMap.lineMap (a i) (b i) α)
                      (AffineMap.lineMap (a i) (b i) β) →
                    p ∈ (localArcAtParam i t).carrier →
                      β = e → p = entryPoint i t) ∧
                  (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
                    p ∈ segment ℝ (AffineMap.lineMap (a i) (b i) α)
                        (AffineMap.lineMap (a i) (b i) β) →
                      p ∈ (localArcAtParam i t).carrier →
                        x < α → False) ∧
                    (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
                      p ∈ segment ℝ (AffineMap.lineMap (a i) (b i) α)
                          (AffineMap.lineMap (a i) (b i) β) →
                        p ∈ (localArcAtParam i t).carrier →
                          x = α → p = exitPoint i t))
    (hinitialGapMeetsLocalCarrierOnly :
      ∀ i (t : {t : ℝ // t ∈ centerParams i})
        ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        p ∈ segment ℝ (a i) (entryPoint i t) →
          p ∈ (localArcAtParam i t).carrier → p = entryPoint i t)
    (hterminalGapMeetsLocalCarrierOnly :
      ∀ i (t : {t : ℝ // t ∈ centerParams i})
        ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        p ∈ segment ℝ (exitPoint i t) (b i) →
          p ∈ (localArcAtParam i t).carrier → p = exitPoint i t)
    (horderedOutsideGapMeetsNeighboringLocalCarriersOnly :
      ∀ i (t1 t2 : {t : ℝ // t ∈ centerParams i}),
        t1.1 < t2.1 →
          (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
            p ∈ segment ℝ (exitPoint i t1) (entryPoint i t2) →
              p ∈ (localArcAtParam i t1).carrier → p = exitPoint i t1) ∧
            (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
              p ∈ segment ℝ (exitPoint i t1) (entryPoint i t2) →
                p ∈ (localArcAtParam i t2).carrier → p = entryPoint i t2))
    (hdisjoint : ∀ ⦃z w : EuclideanSpace ℝ (Fin 2)⦄,
      z ∈ T → w ∈ T → z ≠ w →
        Disjoint (Metric.closedBall z (r z)) (Metric.closedBall w (r w)))
    (hassembledVertices_nodup : ∀ i, (assembledVertices i).Nodup)
    (hassembledVertices_avoid :
      ∀ i ⦃m k : ℕ⦄,
        (hm : m + 1 < (assembledVertices i).length) →
          (hk : k < (assembledVertices i).length) →
            k ≠ m → k ≠ m + 1 →
              (assembledVertices i)[k] ∉
                openSegment ℝ
                  (assembledVertices i)[m] (assembledVertices i)[m + 1])
    (hassembledEdgeEndpointRoles :
      ∀ i ⦃m : ℕ⦄,
        (hm : m + 1 < (assembledVertices i).length) →
          ((centerParams i).attach = [] ∧
              (assembledVertices i)[m] = a i ∧
                (assembledVertices i)[m + 1] = b i) ∨
            (∃ t ts X,
              (centerParams i).attach = t :: ts ∧
                (localArcAtParam i t).vertices.head? = some X ∧
                  (assembledVertices i)[m] = a i ∧
                    (assembledVertices i)[m + 1] = X) ∨
            (∃ (pre : List {t : ℝ // t ∈ centerParams i})
                (t : {t : ℝ // t ∈ centerParams i})
                (post : List {t : ℝ // t ∈ centerParams i}) (q : ℕ),
              ∃ hq : q + 1 < (localArcAtParam i t).vertices.length,
                (centerParams i).attach = pre ++ t :: post ∧
                  (assembledVertices i)[m] =
                    (localArcAtParam i t).vertices[q] ∧
                    (assembledVertices i)[m + 1] =
                      (localArcAtParam i t).vertices[q + 1]) ∨
            (∃ (pre : List {t : ℝ // t ∈ centerParams i})
                (t1 : {t : ℝ // t ∈ centerParams i})
                (t2 : {t : ℝ // t ∈ centerParams i})
                (post : List {t : ℝ // t ∈ centerParams i})
                (X Y : EuclideanSpace ℝ (Fin 2)),
              (centerParams i).attach = pre ++ t1 :: t2 :: post ∧
                (localArcAtParam i t1).vertices.getLast? = some X ∧
                  (localArcAtParam i t2).vertices.head? = some Y ∧
                    (assembledVertices i)[m] = X ∧
                      (assembledVertices i)[m + 1] = Y) ∨
            (∃ (pre : List {t : ℝ // t ∈ centerParams i})
                (t : {t : ℝ // t ∈ centerParams i})
                (X : EuclideanSpace ℝ (Fin 2)),
              (centerParams i).attach = pre ++ [t] ∧
                (localArcAtParam i t).vertices.getLast? = some X ∧
                  (assembledVertices i)[m] = X ∧
                    (assembledVertices i)[m + 1] = b i))
    (hlineSegmentInterSeparated :
      ∀ i {α β γ δ : ℝ}, α ≤ β → γ ≤ δ → β < γ →
        segment ℝ (AffineMap.lineMap (a i) (b i) α)
            (AffineMap.lineMap (a i) (b i) β) ∩
          segment ℝ (AffineMap.lineMap (a i) (b i) γ)
            (AffineMap.lineMap (a i) (b i) δ) =
        (∅ : Set (EuclideanSpace ℝ (Fin 2))))
    (i : ι) {m n : ℕ}
    (hm : m + 1 < (assembledVertices i).length)
    (hn : n + 1 < (assembledVertices i).length)
    (hmn : m < n)
    (hinitialIndexZero :
      ∀ ⦃k : ℕ⦄,
        (hk : k + 1 < (assembledVertices i).length) →
          endpointUnitDiskAssembly_initialRole a centerParams localArcAtParam
              assembledVertices i k hk →
            k = 0)
    (hterminalNoLater :
      ∀ ⦃k l : ℕ⦄,
        (hk : k + 1 < (assembledVertices i).length) →
        (hl : l + 1 < (assembledVertices i).length) →
        k < l →
          endpointUnitDiskAssembly_terminalRole b centerParams localArcAtParam
              assembledVertices i k hk →
            False)
    (hinter_of_forall_eq_right :
      (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        p ∈ segment ℝ (assembledVertices i)[m] (assembledVertices i)[m + 1] →
        p ∈ segment ℝ (assembledVertices i)[n] (assembledVertices i)[n + 1] →
          p = (assembledVertices i)[m + 1]) →
      (segment ℝ (assembledVertices i)[m] (assembledVertices i)[m + 1] ∩
          segment ℝ (assembledVertices i)[n] (assembledVertices i)[n + 1]) =
        if n = m + 1 then {(assembledVertices i)[n]} else ∅)
    (hattach_pairwise_lt :
      (centerParams i).attach.Pairwise
        (fun t1 t2 : {t : ℝ // t ∈ centerParams i} => t1.1 < t2.1))
    (hlocal_m :
      endpointUnitDiskAssembly_localRole centerParams localArcAtParam
        assembledVertices i m hm)
    (hterminal_n :
      endpointUnitDiskAssembly_terminalRole b centerParams localArcAtParam
        assembledVertices i n hn) :
    (segment ℝ (assembledVertices i)[m] (assembledVertices i)[m + 1] ∩
        segment ℝ (assembledVertices i)[n] (assembledVertices i)[n + 1]) =
      if n = m + 1 then {(assembledVertices i)[n]} else ∅ := by
  rcases hlocal_m with
    ⟨pre_m, t_m, post_m, q_m, hq_m, hitems_m,
      hleft_m, hright_m⟩
  rcases hterminal_n with
    ⟨pre_n, t_n, X_n, hitems_n, hlast_n, hleft_n, hright_n⟩
  exact hinter_of_forall_eq_right (by
    intro p hp_local hp_terminal
    have hp_local' :
        p ∈ segment ℝ (localArcAtParam i t_m).vertices[q_m]
            (localArcAtParam i t_m).vertices[q_m + 1] := by
      simpa [hleft_m, hright_m] using hp_local
    have hp_carrier :
        p ∈ (localArcAtParam i t_m).carrier := by
      rw [(localArcAtParam i t_m).carrier_eq]
      exact ⟨q_m, hq_m, hp_local'⟩
    have hlast_exit_n :
        (localArcAtParam i t_n).vertices.getLast? =
          some (exitPoint i t_n) := by
      have htarget := (localArcAtParam i t_n).target_eq_last
      rw [(hlocalArcAtParam_props i t_n).2.1] at htarget
      exact htarget
    have hX_n : X_n = exitPoint i t_n := by
      exact (Option.some.inj (hlast_exit_n.symm.trans hlast_n)).symm
    have hp_terminal_gap :
        p ∈ segment ℝ (exitPoint i t_n) (b i) := by
      simpa [hleft_n, hright_n, hX_n] using hp_terminal
    have ht_m_attach : t_m ∈ (centerParams i).attach := by
      rw [hitems_m]
      simp
    have ht_cases : t_m ∈ pre_n ∨ t_m = t_n := by
      have ht_mem : t_m ∈ pre_n ∨ t_m ∈ [t_n] := by
        simpa [hitems_n, List.mem_append] using ht_m_attach
      rcases ht_mem with ht_pre | ht_last
      · exact Or.inl ht_pre
      · exact Or.inr (by simpa using ht_last)
    rcases ht_cases with ht_pre | ht_eq
    · have ht_m_lt_t_n : t_m.1 < t_n.1 := by
        have hpair := hattach_pairwise_lt
        rw [hitems_n] at hpair
        exact (List.pairwise_append.1 hpair).2.2
          t_m ht_pre t_n (by simp)
      rcases hentryExitParameters i t_m with
        ⟨⟨e_m, he_m_pos, he_m_lt_t_m, hentry_m⟩,
          ⟨x_m, ht_m_lt_x_m, hx_m_lt_one, hexit_m⟩⟩
      rcases hentryExitParameters i t_n with
        ⟨⟨e_n, he_n_pos, he_n_lt_t_n, hentry_n⟩,
          ⟨x_n, ht_n_lt_x_n, hx_n_lt_one, hexit_n⟩⟩
      rcases horderedCutSeparation i t_m t_n ht_m_lt_t_n with
        ⟨sExit, sEntry, _ht_m_sExit, hsExitEntry, _hsEntry_t_n,
          hexit_order, hentry_order⟩
      let f : ℝ →ᵃ[ℝ] EuclideanSpace ℝ (Fin 2) :=
        AffineMap.lineMap (a i) (b i)
      have hf : Function.Injective f :=
        AffineMap.lineMap_injective (k := ℝ) (hendpoint_ne i)
      have hx_m_eq : x_m = sExit := by
        exact hf (by rw [← hexit_m, ← hexit_order])
      have he_n_eq : e_n = sEntry := by
        exact hf (by rw [← hentry_n, ← hentry_order])
      have hx_m_lt_x_n : x_m < x_n := by
        linarith
      have hpseg_param :
          p ∈ segment ℝ (AffineMap.lineMap (a i) (b i) x_n)
              (AffineMap.lineMap (a i) (b i) (1 : ℝ)) := by
        simpa [f, hexit_n] using hp_terminal_gap
      exact False.elim
        ((hchordGapLocalCarrierPosition i t_m
          (α := x_n) (β := (1 : ℝ)) (e := e_m) (x := x_m)
          hentry_m hexit_m (by linarith) (by linarith)
          (by norm_num) (by linarith)).2.2.1
            hpseg_param hp_carrier hx_m_lt_x_n)
    · subst t_n
      have hp_eq_exit :
          p = exitPoint i t_m :=
        hterminalGapMeetsLocalCarrierOnly i t_m
          hp_terminal_gap hp_carrier
      have hlast_exit :
          (localArcAtParam i t_m).vertices.getLast? =
            some (exitPoint i t_m) := by
        have htarget := (localArcAtParam i t_m).target_eq_last
        rw [(hlocalArcAtParam_props i t_m).2.1] at htarget
        exact htarget
      by_cases hq_last :
          q_m + 1 = (localArcAtParam i t_m).vertices.length - 1
      · have hlast_get :
            (localArcAtParam i t_m).vertices.getLast? =
              some ((localArcAtParam i t_m).vertices[q_m + 1]) := by
          rw [List.getLast?_eq_getElem?]
          rw [show (localArcAtParam i t_m).vertices.length - 1 =
              q_m + 1 by omega]
          rw [List.getElem?_eq_getElem hq_m]
        have hright_exit :
            (localArcAtParam i t_m).vertices[q_m + 1] =
              exitPoint i t_m :=
          Option.some.inj (hlast_get.symm.trans hlast_exit)
        calc
          p = exitPoint i t_m := hp_eq_exit
          _ = (localArcAtParam i t_m).vertices[q_m + 1] :=
            hright_exit.symm
          _ = (assembledVertices i)[m + 1] := by
            simpa using hright_m.symm
      · have hlast_index :
            (localArcAtParam i t_m).vertices.length - 1 <
              (localArcAtParam i t_m).vertices.length := by
          have hlen := (localArcAtParam i t_m).length_ge_two
          omega
        have hlast_get :
            (localArcAtParam i t_m).vertices.getLast? =
              some (((localArcAtParam i t_m).vertices)[
                (localArcAtParam i t_m).vertices.length - 1]) := by
          rw [List.getLast?_eq_getElem?]
          rw [List.getElem?_eq_getElem hlast_index]
        have hlast_value :
            ((localArcAtParam i t_m).vertices)[
                (localArcAtParam i t_m).vertices.length - 1] =
              exitPoint i t_m :=
          Option.some.inj (hlast_get.symm.trans hlast_exit)
        have hq_left : q_m < (localArcAtParam i t_m).vertices.length :=
          Nat.lt_trans (Nat.lt_succ_self q_m) hq_m
        have hleft_ne :
            (localArcAtParam i t_m).vertices[q_m] ≠
              exitPoint i t_m := by
          intro hEq
          have hval :
              (localArcAtParam i t_m).vertices[q_m] =
                ((localArcAtParam i t_m).vertices)[
                  (localArcAtParam i t_m).vertices.length - 1] := by
            rw [hEq, hlast_value]
          have hidx :=
            ((localArcAtParam i t_m).simple_vertices.getElem_inj_iff).1 hval
          omega
        have hright_ne :
            (localArcAtParam i t_m).vertices[q_m + 1] ≠
              exitPoint i t_m := by
          intro hEq
          have hval :
              (localArcAtParam i t_m).vertices[q_m + 1] =
                ((localArcAtParam i t_m).vertices)[
                  (localArcAtParam i t_m).vertices.length - 1] := by
            rw [hEq, hlast_value]
          have hidx :=
            ((localArcAtParam i t_m).simple_vertices.getElem_inj_iff).1 hval
          omega
        have hpseg_exit :
            exitPoint i t_m ∈
              segment ℝ (localArcAtParam i t_m).vertices[q_m]
                (localArcAtParam i t_m).vertices[q_m + 1] := by
          simpa [hp_eq_exit] using hp_local'
        have hpopen_exit :
            exitPoint i t_m ∈
              openSegment ℝ (localArcAtParam i t_m).vertices[q_m]
                (localArcAtParam i t_m).vertices[q_m + 1] :=
          mem_openSegment_of_ne_left_right (𝕜 := ℝ)
            hleft_ne hright_ne hpseg_exit
        have hpopen_last :
            ((localArcAtParam i t_m).vertices)[
                (localArcAtParam i t_m).vertices.length - 1] ∈
              openSegment ℝ (localArcAtParam i t_m).vertices[q_m]
                (localArcAtParam i t_m).vertices[q_m + 1] := by
          simpa [hlast_value] using hpopen_exit
        exact False.elim
          ((localArcAtParam i t_m).vertices_avoid_nonincident_interiors
            hq_m hlast_index (by omega) (by omega) hpopen_last))

private lemma endpointUnitDiskAssembly_segments_local
    {ι : Type*} [Fintype ι]
    (a b : ι → EuclideanSpace ℝ (Fin 2))
    (T : Finset (EuclideanSpace ℝ (Fin 2)))
    (r : EuclideanSpace ℝ (Fin 2) → ℝ)
    (centerParams : ι → List ℝ)
    (centerOfParam :
      ∀ i, {t : ℝ // t ∈ centerParams i} → EuclideanSpace ℝ (Fin 2))
    (hcenterOfParam_def :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}),
        centerOfParam i t = AffineMap.lineMap (a i) (b i) t.1)
    (localArcAtParam :
      ∀ i, {t : ℝ // t ∈ centerParams i} → PolygonalArc)
    (entryPoint exitPoint :
      ∀ i, {t : ℝ // t ∈ centerParams i} → EuclideanSpace ℝ (Fin 2))
    (orderedLocalVertexBlocks :
      ∀ i, List (List (EuclideanSpace ℝ (Fin 2))))
    (assembledVertices : ι → List (EuclideanSpace ℝ (Fin 2)))
    (horderedLocalVertexBlocks_def : ∀ i,
      orderedLocalVertexBlocks i =
        (centerParams i).attach.map
          (fun t => (localArcAtParam i t).vertices))
    (hassembledVertices_def : ∀ i,
      assembledVertices i =
        EndpointUnitDiskAlternatingVertexList
          (a i) (b i) (orderedLocalVertexBlocks i))
    (hendpoint_ne : ∀ i, a i ≠ b i)
    (hcenterParams_sorted : ∀ i, (centerParams i).SortedLT)
    (hcenterOfParam_T :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}), centerOfParam i t ∈ T)
    (hlocalArcAtParam_props :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}),
        (localArcAtParam i t).source = entryPoint i t ∧
          (localArcAtParam i t).target = exitPoint i t ∧
            (localArcAtParam i t).carrier ⊆
              Metric.closedBall (centerOfParam i t) (r (centerOfParam i t)) ∧
              (localArcAtParam i t).relativeInterior ⊆
                Metric.ball (centerOfParam i t) (r (centerOfParam i t)))
    (hentryExitParameters :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}),
        (∃ s : ℝ, 0 < s ∧ s < t.1 ∧
          entryPoint i t = AffineMap.lineMap (a i) (b i) s) ∧
          (∃ s : ℝ, t.1 < s ∧ s < 1 ∧
            exitPoint i t = AffineMap.lineMap (a i) (b i) s))
    (horderedCutSeparation :
      ∀ i (t1 t2 : {t : ℝ // t ∈ centerParams i}),
        t1.1 < t2.1 →
          ∃ sExit sEntry : ℝ,
            t1.1 < sExit ∧
              sExit < sEntry ∧
                sEntry < t2.1 ∧
                  exitPoint i t1 = AffineMap.lineMap (a i) (b i) sExit ∧
                    entryPoint i t2 = AffineMap.lineMap (a i) (b i) sEntry)
    (hchordGapLocalCarrierPosition :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}) {α β e x : ℝ},
        entryPoint i t = AffineMap.lineMap (a i) (b i) e →
          exitPoint i t = AffineMap.lineMap (a i) (b i) x →
            0 ≤ α → α ≤ β → β ≤ 1 → e < x →
              (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
                p ∈ segment ℝ (AffineMap.lineMap (a i) (b i) α)
                    (AffineMap.lineMap (a i) (b i) β) →
                  p ∈ (localArcAtParam i t).carrier →
                    β < e → False) ∧
                (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
                  p ∈ segment ℝ (AffineMap.lineMap (a i) (b i) α)
                      (AffineMap.lineMap (a i) (b i) β) →
                    p ∈ (localArcAtParam i t).carrier →
                      β = e → p = entryPoint i t) ∧
                  (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
                    p ∈ segment ℝ (AffineMap.lineMap (a i) (b i) α)
                        (AffineMap.lineMap (a i) (b i) β) →
                      p ∈ (localArcAtParam i t).carrier →
                        x < α → False) ∧
                    (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
                      p ∈ segment ℝ (AffineMap.lineMap (a i) (b i) α)
                          (AffineMap.lineMap (a i) (b i) β) →
                        p ∈ (localArcAtParam i t).carrier →
                          x = α → p = exitPoint i t))
    (hinitialGapMeetsLocalCarrierOnly :
      ∀ i (t : {t : ℝ // t ∈ centerParams i})
        ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        p ∈ segment ℝ (a i) (entryPoint i t) →
          p ∈ (localArcAtParam i t).carrier → p = entryPoint i t)
    (hterminalGapMeetsLocalCarrierOnly :
      ∀ i (t : {t : ℝ // t ∈ centerParams i})
        ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        p ∈ segment ℝ (exitPoint i t) (b i) →
          p ∈ (localArcAtParam i t).carrier → p = exitPoint i t)
    (horderedOutsideGapMeetsNeighboringLocalCarriersOnly :
      ∀ i (t1 t2 : {t : ℝ // t ∈ centerParams i}),
        t1.1 < t2.1 →
          (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
            p ∈ segment ℝ (exitPoint i t1) (entryPoint i t2) →
              p ∈ (localArcAtParam i t1).carrier → p = exitPoint i t1) ∧
            (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
              p ∈ segment ℝ (exitPoint i t1) (entryPoint i t2) →
                p ∈ (localArcAtParam i t2).carrier → p = entryPoint i t2))
    (hdisjoint : ∀ ⦃z w : EuclideanSpace ℝ (Fin 2)⦄,
      z ∈ T → w ∈ T → z ≠ w →
        Disjoint (Metric.closedBall z (r z)) (Metric.closedBall w (r w)))
    (hassembledVertices_nodup : ∀ i, (assembledVertices i).Nodup)
    (hassembledVertices_avoid :
      ∀ i ⦃m k : ℕ⦄,
        (hm : m + 1 < (assembledVertices i).length) →
          (hk : k < (assembledVertices i).length) →
            k ≠ m → k ≠ m + 1 →
              (assembledVertices i)[k] ∉
                openSegment ℝ
                  (assembledVertices i)[m] (assembledVertices i)[m + 1])
    (hassembledEdgeEndpointRoles :
      ∀ i ⦃m : ℕ⦄,
        (hm : m + 1 < (assembledVertices i).length) →
          ((centerParams i).attach = [] ∧
              (assembledVertices i)[m] = a i ∧
                (assembledVertices i)[m + 1] = b i) ∨
            (∃ t ts X,
              (centerParams i).attach = t :: ts ∧
                (localArcAtParam i t).vertices.head? = some X ∧
                  (assembledVertices i)[m] = a i ∧
                    (assembledVertices i)[m + 1] = X) ∨
            (∃ (pre : List {t : ℝ // t ∈ centerParams i})
                (t : {t : ℝ // t ∈ centerParams i})
                (post : List {t : ℝ // t ∈ centerParams i}) (q : ℕ),
              ∃ hq : q + 1 < (localArcAtParam i t).vertices.length,
                (centerParams i).attach = pre ++ t :: post ∧
                  (assembledVertices i)[m] =
                    (localArcAtParam i t).vertices[q] ∧
                    (assembledVertices i)[m + 1] =
                      (localArcAtParam i t).vertices[q + 1]) ∨
            (∃ (pre : List {t : ℝ // t ∈ centerParams i})
                (t1 : {t : ℝ // t ∈ centerParams i})
                (t2 : {t : ℝ // t ∈ centerParams i})
                (post : List {t : ℝ // t ∈ centerParams i})
                (X Y : EuclideanSpace ℝ (Fin 2)),
              (centerParams i).attach = pre ++ t1 :: t2 :: post ∧
                (localArcAtParam i t1).vertices.getLast? = some X ∧
                  (localArcAtParam i t2).vertices.head? = some Y ∧
                    (assembledVertices i)[m] = X ∧
                      (assembledVertices i)[m + 1] = Y) ∨
            (∃ (pre : List {t : ℝ // t ∈ centerParams i})
                (t : {t : ℝ // t ∈ centerParams i})
                (X : EuclideanSpace ℝ (Fin 2)),
              (centerParams i).attach = pre ++ [t] ∧
                (localArcAtParam i t).vertices.getLast? = some X ∧
                  (assembledVertices i)[m] = X ∧
                    (assembledVertices i)[m + 1] = b i))
    (hlineSegmentInterSeparated :
      ∀ i {α β γ δ : ℝ}, α ≤ β → γ ≤ δ → β < γ →
        segment ℝ (AffineMap.lineMap (a i) (b i) α)
            (AffineMap.lineMap (a i) (b i) β) ∩
          segment ℝ (AffineMap.lineMap (a i) (b i) γ)
            (AffineMap.lineMap (a i) (b i) δ) =
        (∅ : Set (EuclideanSpace ℝ (Fin 2))))
    (i : ι) {m n : ℕ}
    (hm : m + 1 < (assembledVertices i).length)
    (hn : n + 1 < (assembledVertices i).length)
    (hmn : m < n)
    (hinitialIndexZero :
      ∀ ⦃k : ℕ⦄,
        (hk : k + 1 < (assembledVertices i).length) →
          endpointUnitDiskAssembly_initialRole a centerParams localArcAtParam
              assembledVertices i k hk →
            k = 0)
    (hterminalNoLater :
      ∀ ⦃k l : ℕ⦄,
        (hk : k + 1 < (assembledVertices i).length) →
        (hl : l + 1 < (assembledVertices i).length) →
        k < l →
          endpointUnitDiskAssembly_terminalRole b centerParams localArcAtParam
              assembledVertices i k hk →
            False)
    (hinter_of_forall_eq_right :
      (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        p ∈ segment ℝ (assembledVertices i)[m] (assembledVertices i)[m + 1] →
        p ∈ segment ℝ (assembledVertices i)[n] (assembledVertices i)[n + 1] →
          p = (assembledVertices i)[m + 1]) →
      (segment ℝ (assembledVertices i)[m] (assembledVertices i)[m + 1] ∩
          segment ℝ (assembledVertices i)[n] (assembledVertices i)[n + 1]) =
        if n = m + 1 then {(assembledVertices i)[n]} else ∅)
    (hattach_pairwise_lt :
      (centerParams i).attach.Pairwise
        (fun t1 t2 : {t : ℝ // t ∈ centerParams i} => t1.1 < t2.1))
    (hlocal_m :
      endpointUnitDiskAssembly_localRole centerParams localArcAtParam
        assembledVertices i m hm)
    (hroles_n :
      endpointUnitDiskAssembly_nonemptyRole a b centerParams localArcAtParam
        assembledVertices i n hn) :
    (segment ℝ (assembledVertices i)[m] (assembledVertices i)[m + 1] ∩
        segment ℝ (assembledVertices i)[n] (assembledVertices i)[n + 1]) =
      if n = m + 1 then {(assembledVertices i)[n]} else ∅ := by
  rcases hroles_n with hinitial_n | hroles_n
  · exact endpointUnitDiskAssembly_segments_local_initial
      a b T r centerParams centerOfParam hcenterOfParam_def
        localArcAtParam entryPoint exitPoint orderedLocalVertexBlocks
        assembledVertices horderedLocalVertexBlocks_def hassembledVertices_def
        hendpoint_ne hcenterParams_sorted hcenterOfParam_T
        hlocalArcAtParam_props hentryExitParameters horderedCutSeparation
        hchordGapLocalCarrierPosition hinitialGapMeetsLocalCarrierOnly
        hterminalGapMeetsLocalCarrierOnly
        horderedOutsideGapMeetsNeighboringLocalCarriersOnly hdisjoint
        hassembledVertices_nodup hassembledVertices_avoid
        hassembledEdgeEndpointRoles hlineSegmentInterSeparated i hm hn hmn
        hinitialIndexZero hterminalNoLater hinter_of_forall_eq_right
        hattach_pairwise_lt hlocal_m hinitial_n
  · rcases hroles_n with hlocal_n | hroles_n
    · exact endpointUnitDiskAssembly_segments_local_local
        a b T r centerParams centerOfParam hcenterOfParam_def
        localArcAtParam entryPoint exitPoint orderedLocalVertexBlocks
        assembledVertices horderedLocalVertexBlocks_def hassembledVertices_def
        hendpoint_ne hcenterParams_sorted hcenterOfParam_T
        hlocalArcAtParam_props hentryExitParameters horderedCutSeparation
        hchordGapLocalCarrierPosition hinitialGapMeetsLocalCarrierOnly
        hterminalGapMeetsLocalCarrierOnly
        horderedOutsideGapMeetsNeighboringLocalCarriersOnly hdisjoint
        hassembledVertices_nodup hassembledVertices_avoid
        hassembledEdgeEndpointRoles hlineSegmentInterSeparated i hm hn hmn
        hinitialIndexZero hterminalNoLater hinter_of_forall_eq_right
        hattach_pairwise_lt hlocal_m hlocal_n
    · rcases hroles_n with hbridge_n | hterminal_n
      · exact endpointUnitDiskAssembly_segments_local_bridge
          a b T r centerParams centerOfParam hcenterOfParam_def
          localArcAtParam entryPoint exitPoint orderedLocalVertexBlocks
          assembledVertices horderedLocalVertexBlocks_def hassembledVertices_def
          hendpoint_ne hcenterParams_sorted hcenterOfParam_T
          hlocalArcAtParam_props hentryExitParameters horderedCutSeparation
          hchordGapLocalCarrierPosition hinitialGapMeetsLocalCarrierOnly
          hterminalGapMeetsLocalCarrierOnly
          horderedOutsideGapMeetsNeighboringLocalCarriersOnly hdisjoint
          hassembledVertices_nodup hassembledVertices_avoid
          hassembledEdgeEndpointRoles hlineSegmentInterSeparated i hm hn hmn
          hinitialIndexZero hterminalNoLater hinter_of_forall_eq_right
          hattach_pairwise_lt hlocal_m hbridge_n
      · exact endpointUnitDiskAssembly_segments_local_terminal
          a b T r centerParams centerOfParam hcenterOfParam_def
          localArcAtParam entryPoint exitPoint orderedLocalVertexBlocks
          assembledVertices horderedLocalVertexBlocks_def hassembledVertices_def
          hendpoint_ne hcenterParams_sorted hcenterOfParam_T
          hlocalArcAtParam_props hentryExitParameters horderedCutSeparation
          hchordGapLocalCarrierPosition hinitialGapMeetsLocalCarrierOnly
          hterminalGapMeetsLocalCarrierOnly
          horderedOutsideGapMeetsNeighboringLocalCarriersOnly hdisjoint
          hassembledVertices_nodup hassembledVertices_avoid
          hassembledEdgeEndpointRoles hlineSegmentInterSeparated i hm hn hmn
          hinitialIndexZero hterminalNoLater hinter_of_forall_eq_right
          hattach_pairwise_lt hlocal_m hterminal_n

private lemma endpointUnitDiskAssembly_segments_bridge_initial
    {ι : Type*} [Fintype ι]
    (a b : ι → EuclideanSpace ℝ (Fin 2))
    (T : Finset (EuclideanSpace ℝ (Fin 2)))
    (r : EuclideanSpace ℝ (Fin 2) → ℝ)
    (centerParams : ι → List ℝ)
    (centerOfParam :
      ∀ i, {t : ℝ // t ∈ centerParams i} → EuclideanSpace ℝ (Fin 2))
    (hcenterOfParam_def :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}),
        centerOfParam i t = AffineMap.lineMap (a i) (b i) t.1)
    (localArcAtParam :
      ∀ i, {t : ℝ // t ∈ centerParams i} → PolygonalArc)
    (entryPoint exitPoint :
      ∀ i, {t : ℝ // t ∈ centerParams i} → EuclideanSpace ℝ (Fin 2))
    (orderedLocalVertexBlocks :
      ∀ i, List (List (EuclideanSpace ℝ (Fin 2))))
    (assembledVertices : ι → List (EuclideanSpace ℝ (Fin 2)))
    (horderedLocalVertexBlocks_def : ∀ i,
      orderedLocalVertexBlocks i =
        (centerParams i).attach.map
          (fun t => (localArcAtParam i t).vertices))
    (hassembledVertices_def : ∀ i,
      assembledVertices i =
        EndpointUnitDiskAlternatingVertexList
          (a i) (b i) (orderedLocalVertexBlocks i))
    (hendpoint_ne : ∀ i, a i ≠ b i)
    (hcenterParams_sorted : ∀ i, (centerParams i).SortedLT)
    (hcenterOfParam_T :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}), centerOfParam i t ∈ T)
    (hlocalArcAtParam_props :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}),
        (localArcAtParam i t).source = entryPoint i t ∧
          (localArcAtParam i t).target = exitPoint i t ∧
            (localArcAtParam i t).carrier ⊆
              Metric.closedBall (centerOfParam i t) (r (centerOfParam i t)) ∧
              (localArcAtParam i t).relativeInterior ⊆
                Metric.ball (centerOfParam i t) (r (centerOfParam i t)))
    (hentryExitParameters :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}),
        (∃ s : ℝ, 0 < s ∧ s < t.1 ∧
          entryPoint i t = AffineMap.lineMap (a i) (b i) s) ∧
          (∃ s : ℝ, t.1 < s ∧ s < 1 ∧
            exitPoint i t = AffineMap.lineMap (a i) (b i) s))
    (horderedCutSeparation :
      ∀ i (t1 t2 : {t : ℝ // t ∈ centerParams i}),
        t1.1 < t2.1 →
          ∃ sExit sEntry : ℝ,
            t1.1 < sExit ∧
              sExit < sEntry ∧
                sEntry < t2.1 ∧
                  exitPoint i t1 = AffineMap.lineMap (a i) (b i) sExit ∧
                    entryPoint i t2 = AffineMap.lineMap (a i) (b i) sEntry)
    (hchordGapLocalCarrierPosition :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}) {α β e x : ℝ},
        entryPoint i t = AffineMap.lineMap (a i) (b i) e →
          exitPoint i t = AffineMap.lineMap (a i) (b i) x →
            0 ≤ α → α ≤ β → β ≤ 1 → e < x →
              (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
                p ∈ segment ℝ (AffineMap.lineMap (a i) (b i) α)
                    (AffineMap.lineMap (a i) (b i) β) →
                  p ∈ (localArcAtParam i t).carrier →
                    β < e → False) ∧
                (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
                  p ∈ segment ℝ (AffineMap.lineMap (a i) (b i) α)
                      (AffineMap.lineMap (a i) (b i) β) →
                    p ∈ (localArcAtParam i t).carrier →
                      β = e → p = entryPoint i t) ∧
                  (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
                    p ∈ segment ℝ (AffineMap.lineMap (a i) (b i) α)
                        (AffineMap.lineMap (a i) (b i) β) →
                      p ∈ (localArcAtParam i t).carrier →
                        x < α → False) ∧
                    (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
                      p ∈ segment ℝ (AffineMap.lineMap (a i) (b i) α)
                          (AffineMap.lineMap (a i) (b i) β) →
                        p ∈ (localArcAtParam i t).carrier →
                          x = α → p = exitPoint i t))
    (hinitialGapMeetsLocalCarrierOnly :
      ∀ i (t : {t : ℝ // t ∈ centerParams i})
        ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        p ∈ segment ℝ (a i) (entryPoint i t) →
          p ∈ (localArcAtParam i t).carrier → p = entryPoint i t)
    (hterminalGapMeetsLocalCarrierOnly :
      ∀ i (t : {t : ℝ // t ∈ centerParams i})
        ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        p ∈ segment ℝ (exitPoint i t) (b i) →
          p ∈ (localArcAtParam i t).carrier → p = exitPoint i t)
    (horderedOutsideGapMeetsNeighboringLocalCarriersOnly :
      ∀ i (t1 t2 : {t : ℝ // t ∈ centerParams i}),
        t1.1 < t2.1 →
          (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
            p ∈ segment ℝ (exitPoint i t1) (entryPoint i t2) →
              p ∈ (localArcAtParam i t1).carrier → p = exitPoint i t1) ∧
            (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
              p ∈ segment ℝ (exitPoint i t1) (entryPoint i t2) →
                p ∈ (localArcAtParam i t2).carrier → p = entryPoint i t2))
    (hdisjoint : ∀ ⦃z w : EuclideanSpace ℝ (Fin 2)⦄,
      z ∈ T → w ∈ T → z ≠ w →
        Disjoint (Metric.closedBall z (r z)) (Metric.closedBall w (r w)))
    (hassembledVertices_nodup : ∀ i, (assembledVertices i).Nodup)
    (hassembledVertices_avoid :
      ∀ i ⦃m k : ℕ⦄,
        (hm : m + 1 < (assembledVertices i).length) →
          (hk : k < (assembledVertices i).length) →
            k ≠ m → k ≠ m + 1 →
              (assembledVertices i)[k] ∉
                openSegment ℝ
                  (assembledVertices i)[m] (assembledVertices i)[m + 1])
    (hassembledEdgeEndpointRoles :
      ∀ i ⦃m : ℕ⦄,
        (hm : m + 1 < (assembledVertices i).length) →
          ((centerParams i).attach = [] ∧
              (assembledVertices i)[m] = a i ∧
                (assembledVertices i)[m + 1] = b i) ∨
            (∃ t ts X,
              (centerParams i).attach = t :: ts ∧
                (localArcAtParam i t).vertices.head? = some X ∧
                  (assembledVertices i)[m] = a i ∧
                    (assembledVertices i)[m + 1] = X) ∨
            (∃ (pre : List {t : ℝ // t ∈ centerParams i})
                (t : {t : ℝ // t ∈ centerParams i})
                (post : List {t : ℝ // t ∈ centerParams i}) (q : ℕ),
              ∃ hq : q + 1 < (localArcAtParam i t).vertices.length,
                (centerParams i).attach = pre ++ t :: post ∧
                  (assembledVertices i)[m] =
                    (localArcAtParam i t).vertices[q] ∧
                    (assembledVertices i)[m + 1] =
                      (localArcAtParam i t).vertices[q + 1]) ∨
            (∃ (pre : List {t : ℝ // t ∈ centerParams i})
                (t1 : {t : ℝ // t ∈ centerParams i})
                (t2 : {t : ℝ // t ∈ centerParams i})
                (post : List {t : ℝ // t ∈ centerParams i})
                (X Y : EuclideanSpace ℝ (Fin 2)),
              (centerParams i).attach = pre ++ t1 :: t2 :: post ∧
                (localArcAtParam i t1).vertices.getLast? = some X ∧
                  (localArcAtParam i t2).vertices.head? = some Y ∧
                    (assembledVertices i)[m] = X ∧
                      (assembledVertices i)[m + 1] = Y) ∨
            (∃ (pre : List {t : ℝ // t ∈ centerParams i})
                (t : {t : ℝ // t ∈ centerParams i})
                (X : EuclideanSpace ℝ (Fin 2)),
              (centerParams i).attach = pre ++ [t] ∧
                (localArcAtParam i t).vertices.getLast? = some X ∧
                  (assembledVertices i)[m] = X ∧
                    (assembledVertices i)[m + 1] = b i))
    (hlineSegmentInterSeparated :
      ∀ i {α β γ δ : ℝ}, α ≤ β → γ ≤ δ → β < γ →
        segment ℝ (AffineMap.lineMap (a i) (b i) α)
            (AffineMap.lineMap (a i) (b i) β) ∩
          segment ℝ (AffineMap.lineMap (a i) (b i) γ)
            (AffineMap.lineMap (a i) (b i) δ) =
        (∅ : Set (EuclideanSpace ℝ (Fin 2))))
    (i : ι) {m n : ℕ}
    (hm : m + 1 < (assembledVertices i).length)
    (hn : n + 1 < (assembledVertices i).length)
    (hmn : m < n)
    (hinitialIndexZero :
      ∀ ⦃k : ℕ⦄,
        (hk : k + 1 < (assembledVertices i).length) →
          endpointUnitDiskAssembly_initialRole a centerParams localArcAtParam
              assembledVertices i k hk →
            k = 0)
    (hterminalNoLater :
      ∀ ⦃k l : ℕ⦄,
        (hk : k + 1 < (assembledVertices i).length) →
        (hl : l + 1 < (assembledVertices i).length) →
        k < l →
          endpointUnitDiskAssembly_terminalRole b centerParams localArcAtParam
              assembledVertices i k hk →
            False)
    (hinter_of_forall_eq_right :
      (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        p ∈ segment ℝ (assembledVertices i)[m] (assembledVertices i)[m + 1] →
        p ∈ segment ℝ (assembledVertices i)[n] (assembledVertices i)[n + 1] →
          p = (assembledVertices i)[m + 1]) →
      (segment ℝ (assembledVertices i)[m] (assembledVertices i)[m + 1] ∩
          segment ℝ (assembledVertices i)[n] (assembledVertices i)[n + 1]) =
        if n = m + 1 then {(assembledVertices i)[n]} else ∅)
    (hattach_pairwise_lt :
      (centerParams i).attach.Pairwise
        (fun t1 t2 : {t : ℝ // t ∈ centerParams i} => t1.1 < t2.1))
    (hbridge_m :
      endpointUnitDiskAssembly_bridgeRole centerParams localArcAtParam
        assembledVertices i m hm)
    (hinitial_n :
      endpointUnitDiskAssembly_initialRole a centerParams localArcAtParam
        assembledVertices i n hn) :
    (segment ℝ (assembledVertices i)[m] (assembledVertices i)[m + 1] ∩
        segment ℝ (assembledVertices i)[n] (assembledVertices i)[n + 1]) =
      if n = m + 1 then {(assembledVertices i)[n]} else ∅ := by
  exact False.elim (by
    have hn0 : n = 0 := hinitialIndexZero hn hinitial_n
    omega)

private lemma endpointUnitDiskAssembly_segments_bridge_local
    {ι : Type*} [Fintype ι]
    (a b : ι → EuclideanSpace ℝ (Fin 2))
    (T : Finset (EuclideanSpace ℝ (Fin 2)))
    (r : EuclideanSpace ℝ (Fin 2) → ℝ)
    (centerParams : ι → List ℝ)
    (centerOfParam :
      ∀ i, {t : ℝ // t ∈ centerParams i} → EuclideanSpace ℝ (Fin 2))
    (hcenterOfParam_def :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}),
        centerOfParam i t = AffineMap.lineMap (a i) (b i) t.1)
    (localArcAtParam :
      ∀ i, {t : ℝ // t ∈ centerParams i} → PolygonalArc)
    (entryPoint exitPoint :
      ∀ i, {t : ℝ // t ∈ centerParams i} → EuclideanSpace ℝ (Fin 2))
    (orderedLocalVertexBlocks :
      ∀ i, List (List (EuclideanSpace ℝ (Fin 2))))
    (assembledVertices : ι → List (EuclideanSpace ℝ (Fin 2)))
    (horderedLocalVertexBlocks_def : ∀ i,
      orderedLocalVertexBlocks i =
        (centerParams i).attach.map
          (fun t => (localArcAtParam i t).vertices))
    (hassembledVertices_def : ∀ i,
      assembledVertices i =
        EndpointUnitDiskAlternatingVertexList
          (a i) (b i) (orderedLocalVertexBlocks i))
    (hendpoint_ne : ∀ i, a i ≠ b i)
    (hcenterParams_sorted : ∀ i, (centerParams i).SortedLT)
    (hcenterOfParam_T :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}), centerOfParam i t ∈ T)
    (hlocalArcAtParam_props :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}),
        (localArcAtParam i t).source = entryPoint i t ∧
          (localArcAtParam i t).target = exitPoint i t ∧
            (localArcAtParam i t).carrier ⊆
              Metric.closedBall (centerOfParam i t) (r (centerOfParam i t)) ∧
              (localArcAtParam i t).relativeInterior ⊆
                Metric.ball (centerOfParam i t) (r (centerOfParam i t)))
    (hentryExitParameters :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}),
        (∃ s : ℝ, 0 < s ∧ s < t.1 ∧
          entryPoint i t = AffineMap.lineMap (a i) (b i) s) ∧
          (∃ s : ℝ, t.1 < s ∧ s < 1 ∧
            exitPoint i t = AffineMap.lineMap (a i) (b i) s))
    (horderedCutSeparation :
      ∀ i (t1 t2 : {t : ℝ // t ∈ centerParams i}),
        t1.1 < t2.1 →
          ∃ sExit sEntry : ℝ,
            t1.1 < sExit ∧
              sExit < sEntry ∧
                sEntry < t2.1 ∧
                  exitPoint i t1 = AffineMap.lineMap (a i) (b i) sExit ∧
                    entryPoint i t2 = AffineMap.lineMap (a i) (b i) sEntry)
    (hchordGapLocalCarrierPosition :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}) {α β e x : ℝ},
        entryPoint i t = AffineMap.lineMap (a i) (b i) e →
          exitPoint i t = AffineMap.lineMap (a i) (b i) x →
            0 ≤ α → α ≤ β → β ≤ 1 → e < x →
              (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
                p ∈ segment ℝ (AffineMap.lineMap (a i) (b i) α)
                    (AffineMap.lineMap (a i) (b i) β) →
                  p ∈ (localArcAtParam i t).carrier →
                    β < e → False) ∧
                (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
                  p ∈ segment ℝ (AffineMap.lineMap (a i) (b i) α)
                      (AffineMap.lineMap (a i) (b i) β) →
                    p ∈ (localArcAtParam i t).carrier →
                      β = e → p = entryPoint i t) ∧
                  (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
                    p ∈ segment ℝ (AffineMap.lineMap (a i) (b i) α)
                        (AffineMap.lineMap (a i) (b i) β) →
                      p ∈ (localArcAtParam i t).carrier →
                        x < α → False) ∧
                    (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
                      p ∈ segment ℝ (AffineMap.lineMap (a i) (b i) α)
                          (AffineMap.lineMap (a i) (b i) β) →
                        p ∈ (localArcAtParam i t).carrier →
                          x = α → p = exitPoint i t))
    (hinitialGapMeetsLocalCarrierOnly :
      ∀ i (t : {t : ℝ // t ∈ centerParams i})
        ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        p ∈ segment ℝ (a i) (entryPoint i t) →
          p ∈ (localArcAtParam i t).carrier → p = entryPoint i t)
    (hterminalGapMeetsLocalCarrierOnly :
      ∀ i (t : {t : ℝ // t ∈ centerParams i})
        ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        p ∈ segment ℝ (exitPoint i t) (b i) →
          p ∈ (localArcAtParam i t).carrier → p = exitPoint i t)
    (horderedOutsideGapMeetsNeighboringLocalCarriersOnly :
      ∀ i (t1 t2 : {t : ℝ // t ∈ centerParams i}),
        t1.1 < t2.1 →
          (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
            p ∈ segment ℝ (exitPoint i t1) (entryPoint i t2) →
              p ∈ (localArcAtParam i t1).carrier → p = exitPoint i t1) ∧
            (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
              p ∈ segment ℝ (exitPoint i t1) (entryPoint i t2) →
                p ∈ (localArcAtParam i t2).carrier → p = entryPoint i t2))
    (hdisjoint : ∀ ⦃z w : EuclideanSpace ℝ (Fin 2)⦄,
      z ∈ T → w ∈ T → z ≠ w →
        Disjoint (Metric.closedBall z (r z)) (Metric.closedBall w (r w)))
    (hassembledVertices_nodup : ∀ i, (assembledVertices i).Nodup)
    (hassembledVertices_avoid :
      ∀ i ⦃m k : ℕ⦄,
        (hm : m + 1 < (assembledVertices i).length) →
          (hk : k < (assembledVertices i).length) →
            k ≠ m → k ≠ m + 1 →
              (assembledVertices i)[k] ∉
                openSegment ℝ
                  (assembledVertices i)[m] (assembledVertices i)[m + 1])
    (hassembledEdgeEndpointRoles :
      ∀ i ⦃m : ℕ⦄,
        (hm : m + 1 < (assembledVertices i).length) →
          ((centerParams i).attach = [] ∧
              (assembledVertices i)[m] = a i ∧
                (assembledVertices i)[m + 1] = b i) ∨
            (∃ t ts X,
              (centerParams i).attach = t :: ts ∧
                (localArcAtParam i t).vertices.head? = some X ∧
                  (assembledVertices i)[m] = a i ∧
                    (assembledVertices i)[m + 1] = X) ∨
            (∃ (pre : List {t : ℝ // t ∈ centerParams i})
                (t : {t : ℝ // t ∈ centerParams i})
                (post : List {t : ℝ // t ∈ centerParams i}) (q : ℕ),
              ∃ hq : q + 1 < (localArcAtParam i t).vertices.length,
                (centerParams i).attach = pre ++ t :: post ∧
                  (assembledVertices i)[m] =
                    (localArcAtParam i t).vertices[q] ∧
                    (assembledVertices i)[m + 1] =
                      (localArcAtParam i t).vertices[q + 1]) ∨
            (∃ (pre : List {t : ℝ // t ∈ centerParams i})
                (t1 : {t : ℝ // t ∈ centerParams i})
                (t2 : {t : ℝ // t ∈ centerParams i})
                (post : List {t : ℝ // t ∈ centerParams i})
                (X Y : EuclideanSpace ℝ (Fin 2)),
              (centerParams i).attach = pre ++ t1 :: t2 :: post ∧
                (localArcAtParam i t1).vertices.getLast? = some X ∧
                  (localArcAtParam i t2).vertices.head? = some Y ∧
                    (assembledVertices i)[m] = X ∧
                      (assembledVertices i)[m + 1] = Y) ∨
            (∃ (pre : List {t : ℝ // t ∈ centerParams i})
                (t : {t : ℝ // t ∈ centerParams i})
                (X : EuclideanSpace ℝ (Fin 2)),
              (centerParams i).attach = pre ++ [t] ∧
                (localArcAtParam i t).vertices.getLast? = some X ∧
                  (assembledVertices i)[m] = X ∧
                    (assembledVertices i)[m + 1] = b i))
    (hlineSegmentInterSeparated :
      ∀ i {α β γ δ : ℝ}, α ≤ β → γ ≤ δ → β < γ →
        segment ℝ (AffineMap.lineMap (a i) (b i) α)
            (AffineMap.lineMap (a i) (b i) β) ∩
          segment ℝ (AffineMap.lineMap (a i) (b i) γ)
            (AffineMap.lineMap (a i) (b i) δ) =
        (∅ : Set (EuclideanSpace ℝ (Fin 2))))
    (i : ι) {m n : ℕ}
    (hm : m + 1 < (assembledVertices i).length)
    (hn : n + 1 < (assembledVertices i).length)
    (hmn : m < n)
    (hinitialIndexZero :
      ∀ ⦃k : ℕ⦄,
        (hk : k + 1 < (assembledVertices i).length) →
          endpointUnitDiskAssembly_initialRole a centerParams localArcAtParam
              assembledVertices i k hk →
            k = 0)
    (hterminalNoLater :
      ∀ ⦃k l : ℕ⦄,
        (hk : k + 1 < (assembledVertices i).length) →
        (hl : l + 1 < (assembledVertices i).length) →
        k < l →
          endpointUnitDiskAssembly_terminalRole b centerParams localArcAtParam
              assembledVertices i k hk →
            False)
    (hinter_of_forall_eq_right :
      (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        p ∈ segment ℝ (assembledVertices i)[m] (assembledVertices i)[m + 1] →
        p ∈ segment ℝ (assembledVertices i)[n] (assembledVertices i)[n + 1] →
          p = (assembledVertices i)[m + 1]) →
      (segment ℝ (assembledVertices i)[m] (assembledVertices i)[m + 1] ∩
          segment ℝ (assembledVertices i)[n] (assembledVertices i)[n + 1]) =
        if n = m + 1 then {(assembledVertices i)[n]} else ∅)
    (hattach_pairwise_lt :
      (centerParams i).attach.Pairwise
        (fun t1 t2 : {t : ℝ // t ∈ centerParams i} => t1.1 < t2.1))
    (hbridge_m :
      endpointUnitDiskAssembly_bridgeRole centerParams localArcAtParam
        assembledVertices i m hm)
    (hlocal_n :
      endpointUnitDiskAssembly_localRole centerParams localArcAtParam
        assembledVertices i n hn) :
    (segment ℝ (assembledVertices i)[m] (assembledVertices i)[m + 1] ∩
        segment ℝ (assembledVertices i)[n] (assembledVertices i)[n + 1]) =
      if n = m + 1 then {(assembledVertices i)[n]} else ∅ := by
  rcases hbridge_m with
    ⟨pre_m, t1_m, t2_m, post_m, X_m, Y_m, hitems_m,
      hlast_m, hhead_m, hleft_m, hright_m⟩
  rcases hlocal_n with
    ⟨pre_n, t_n, post_n, q_n, hq_n, hitems_n,
      hleft_n, hright_n⟩
  exact hinter_of_forall_eq_right (by
    intro p hp_bridge hp_local
    have hlast_exit_m :
        (localArcAtParam i t1_m).vertices.getLast? =
          some (exitPoint i t1_m) := by
      have htarget := (localArcAtParam i t1_m).target_eq_last
      rw [(hlocalArcAtParam_props i t1_m).2.1] at htarget
      exact htarget
    have hX_m : X_m = exitPoint i t1_m := by
      exact (Option.some.inj (hlast_exit_m.symm.trans hlast_m)).symm
    have hhead_entry_m :
        (localArcAtParam i t2_m).vertices.head? =
          some (entryPoint i t2_m) := by
      have hsource := (localArcAtParam i t2_m).source_eq_head
      rw [(hlocalArcAtParam_props i t2_m).1] at hsource
      exact hsource
    have hY_m : Y_m = entryPoint i t2_m := by
      exact (Option.some.inj (hhead_entry_m.symm.trans hhead_m)).symm
    have hp_bridge_gap :
        p ∈ segment ℝ (exitPoint i t1_m) (entryPoint i t2_m) := by
      simpa [hleft_m, hright_m, hX_m, hY_m] using hp_bridge
    have hp_local' :
        p ∈ segment ℝ (localArcAtParam i t_n).vertices[q_n]
            (localArcAtParam i t_n).vertices[q_n + 1] := by
      simpa [hleft_n, hright_n] using hp_local
    have hp_carrier :
        p ∈ (localArcAtParam i t_n).carrier := by
      rw [(localArcAtParam i t_n).carrier_eq]
      exact ⟨q_n, hq_n, hp_local'⟩
    have hpair_bridge := hattach_pairwise_lt
    rw [hitems_m] at hpair_bridge
    have htail_pair :
        (t1_m :: t2_m :: post_m).Pairwise
          (fun u v : {t : ℝ // t ∈ centerParams i} => u.1 < v.1) :=
      (List.pairwise_append.1 hpair_bridge).2.1
    have ht12 : t1_m.1 < t2_m.1 :=
      (List.pairwise_cons.1 htail_pair).1 t2_m (by simp)
    rcases hentryExitParameters i t1_m with
      ⟨⟨e1, he1_pos, he1_lt_t1, hentry1⟩,
        ⟨x1, ht1_lt_x1, hx1_lt_one, hexit1⟩⟩
    rcases hentryExitParameters i t2_m with
      ⟨⟨e2, he2_pos, he2_lt_t2, hentry2⟩,
        ⟨x2, ht2_lt_x2, hx2_lt_one, hexit2⟩⟩
    rcases horderedCutSeparation i t1_m t2_m ht12 with
      ⟨sExit, sEntry, _ht1_sExit, hsExitEntry, _hsEntry_t2,
        hexit_order, hentry_order⟩
    let f : ℝ →ᵃ[ℝ] EuclideanSpace ℝ (Fin 2) :=
      AffineMap.lineMap (a i) (b i)
    have hf : Function.Injective f :=
      AffineMap.lineMap_injective (k := ℝ) (hendpoint_ne i)
    have hx1_eq : x1 = sExit := by
      exact hf (by rw [← hexit1, ← hexit_order])
    have he2_eq : e2 = sEntry := by
      exact hf (by rw [← hentry2, ← hentry_order])
    have hx1_lt_e2 : x1 < e2 := by
      linarith
    have ht_n_attach : t_n ∈ (centerParams i).attach := by
      rw [hitems_n]
      simp
    have ht_cases :
        t_n ∈ pre_m ∨ t_n = t1_m ∨ t_n = t2_m ∨ t_n ∈ post_m := by
      have ht_mem : t_n ∈ pre_m ++ t1_m :: t2_m :: post_m := by
        simpa [hitems_m] using ht_n_attach
      simpa [List.mem_append, List.mem_cons] using ht_mem
    rcases ht_cases with ht_pre | ht_cases
    · have ht_n_lt_t1 : t_n.1 < t1_m.1 :=
        (List.pairwise_append.1 hpair_bridge).2.2
          t_n ht_pre t1_m (by simp)
      rcases hentryExitParameters i t_n with
        ⟨⟨e_n, he_n_pos, he_n_lt_t_n, hentry_n⟩,
          ⟨x_n, ht_n_lt_x_n, hx_n_lt_one, hexit_n⟩⟩
      rcases horderedCutSeparation i t_n t1_m ht_n_lt_t1 with
        ⟨sExit', sEntry', _ht_n_sExit', hsExitEntry',
          _hsEntry_t1, hexit_order', hentry_order'⟩
      have hx_n_eq : x_n = sExit' := by
        exact hf (by rw [← hexit_n, ← hexit_order'])
      have he1_eq : e1 = sEntry' := by
        exact hf (by rw [← hentry1, ← hentry_order'])
      have hx_n_lt_x1 : x_n < x1 := by
        linarith
      have hpseg_param :
          p ∈ segment ℝ (AffineMap.lineMap (a i) (b i) x1)
              (AffineMap.lineMap (a i) (b i) e2) := by
        simpa [f, hexit1, hentry2] using hp_bridge_gap
      exact False.elim
        ((hchordGapLocalCarrierPosition i t_n
          (α := x1) (β := e2) (e := e_n) (x := x_n)
          hentry_n hexit_n (by linarith) hx1_lt_e2.le
          (by linarith) (by linarith)).2.2.1
            hpseg_param hp_carrier hx_n_lt_x1)
    rcases ht_cases with ht_eq1 | ht_cases
    · subst t_n
      have hp_eq_exit :
          p = exitPoint i t1_m :=
        (horderedOutsideGapMeetsNeighboringLocalCarriersOnly
          i t1_m t2_m ht12).1 hp_bridge_gap hp_carrier
      have hlast_exit :
          (localArcAtParam i t1_m).vertices.getLast? =
            some (exitPoint i t1_m) := by
        have htarget := (localArcAtParam i t1_m).target_eq_last
        rw [(hlocalArcAtParam_props i t1_m).2.1] at htarget
        exact htarget
      by_cases hq_last :
          q_n + 1 = (localArcAtParam i t1_m).vertices.length - 1
      · have hlast_get :
            (localArcAtParam i t1_m).vertices.getLast? =
              some ((localArcAtParam i t1_m).vertices[q_n + 1]) := by
          rw [List.getLast?_eq_getElem?]
          rw [show (localArcAtParam i t1_m).vertices.length - 1 =
              q_n + 1 by omega]
          rw [List.getElem?_eq_getElem hq_n]
        have hright_exit :
            (localArcAtParam i t1_m).vertices[q_n + 1] =
              exitPoint i t1_m :=
          Option.some.inj (hlast_get.symm.trans hlast_exit)
        have hval :
            (assembledVertices i)[n + 1] =
              (assembledVertices i)[m] := by
          rw [hright_n, hleft_m, hX_m]
          exact hright_exit
        have hidx :=
          ((hassembledVertices_nodup i).getElem_inj_iff).1 hval
        exact False.elim (by omega)
      · have hlast_index :
            (localArcAtParam i t1_m).vertices.length - 1 <
              (localArcAtParam i t1_m).vertices.length := by
          have hlen := (localArcAtParam i t1_m).length_ge_two
          omega
        have hlast_get :
            (localArcAtParam i t1_m).vertices.getLast? =
              some (((localArcAtParam i t1_m).vertices)[
                (localArcAtParam i t1_m).vertices.length - 1]) := by
          rw [List.getLast?_eq_getElem?]
          rw [List.getElem?_eq_getElem hlast_index]
        have hlast_value :
            ((localArcAtParam i t1_m).vertices)[
                (localArcAtParam i t1_m).vertices.length - 1] =
              exitPoint i t1_m :=
          Option.some.inj (hlast_get.symm.trans hlast_exit)
        have hleft_ne :
            (localArcAtParam i t1_m).vertices[q_n] ≠
              exitPoint i t1_m := by
          intro hEq
          have hval :
              (localArcAtParam i t1_m).vertices[q_n] =
                ((localArcAtParam i t1_m).vertices)[
                  (localArcAtParam i t1_m).vertices.length - 1] := by
            rw [hEq, hlast_value]
          have hidx :=
            ((localArcAtParam i t1_m).simple_vertices.getElem_inj_iff).1 hval
          omega
        have hright_ne :
            (localArcAtParam i t1_m).vertices[q_n + 1] ≠
              exitPoint i t1_m := by
          intro hEq
          have hval :
              (localArcAtParam i t1_m).vertices[q_n + 1] =
                ((localArcAtParam i t1_m).vertices)[
                  (localArcAtParam i t1_m).vertices.length - 1] := by
            rw [hEq, hlast_value]
          have hidx :=
            ((localArcAtParam i t1_m).simple_vertices.getElem_inj_iff).1 hval
          omega
        have hpseg_exit :
            exitPoint i t1_m ∈
              segment ℝ (localArcAtParam i t1_m).vertices[q_n]
                (localArcAtParam i t1_m).vertices[q_n + 1] := by
          simpa [hp_eq_exit] using hp_local'
        have hpopen_exit :
            exitPoint i t1_m ∈
              openSegment ℝ (localArcAtParam i t1_m).vertices[q_n]
                (localArcAtParam i t1_m).vertices[q_n + 1] :=
          mem_openSegment_of_ne_left_right (𝕜 := ℝ)
            hleft_ne hright_ne hpseg_exit
        have hpopen_last :
            ((localArcAtParam i t1_m).vertices)[
                (localArcAtParam i t1_m).vertices.length - 1] ∈
              openSegment ℝ (localArcAtParam i t1_m).vertices[q_n]
                (localArcAtParam i t1_m).vertices[q_n + 1] := by
          simpa [hlast_value] using hpopen_exit
        exact False.elim
          ((localArcAtParam i t1_m).vertices_avoid_nonincident_interiors
            hq_n hlast_index (by omega) (by omega) hpopen_last)
    rcases ht_cases with ht_eq2 | ht_post
    · subst t_n
      have hp_eq_entry :
          p = entryPoint i t2_m :=
        (horderedOutsideGapMeetsNeighboringLocalCarriersOnly
          i t1_m t2_m ht12).2 hp_bridge_gap hp_carrier
      calc
        p = entryPoint i t2_m := hp_eq_entry
        _ = Y_m := hY_m.symm
        _ = (assembledVertices i)[m + 1] := hright_m.symm
    · have hprefix_pair :
        ((pre_m ++ [t1_m, t2_m]) ++ post_m).Pairwise
          (fun u v : {t : ℝ // t ∈ centerParams i} => u.1 < v.1) := by
        simpa [List.append_assoc] using hpair_bridge
      have ht2_lt_tn : t2_m.1 < t_n.1 :=
        (List.pairwise_append.1 hprefix_pair).2.2
          t2_m (by simp) t_n ht_post
      rcases hentryExitParameters i t_n with
        ⟨⟨e_n, he_n_pos, he_n_lt_t_n, hentry_n⟩,
          ⟨x_n, ht_n_lt_x_n, hx_n_lt_one, hexit_n⟩⟩
      rcases horderedCutSeparation i t2_m t_n ht2_lt_tn with
        ⟨sExit', sEntry', _ht2_sExit', hsExitEntry',
          _hsEntry_tn, _hexit_order', hentry_order'⟩
      have he_n_eq : e_n = sEntry' := by
        exact hf (by rw [← hentry_n, ← hentry_order'])
      have he2_lt_e_n : e2 < e_n := by
        linarith
      have hpseg_param :
          p ∈ segment ℝ (AffineMap.lineMap (a i) (b i) x1)
              (AffineMap.lineMap (a i) (b i) e2) := by
        simpa [f, hexit1, hentry2] using hp_bridge_gap
      exact False.elim
        ((hchordGapLocalCarrierPosition i t_n
          (α := x1) (β := e2) (e := e_n) (x := x_n)
          hentry_n hexit_n (by linarith) hx1_lt_e2.le
          (by linarith) (by linarith)).1
            hpseg_param hp_carrier he2_lt_e_n))

private lemma endpointUnitDiskAssembly_segments_bridge_bridge
    {ι : Type*} [Fintype ι]
    (a b : ι → EuclideanSpace ℝ (Fin 2))
    (T : Finset (EuclideanSpace ℝ (Fin 2)))
    (r : EuclideanSpace ℝ (Fin 2) → ℝ)
    (centerParams : ι → List ℝ)
    (centerOfParam :
      ∀ i, {t : ℝ // t ∈ centerParams i} → EuclideanSpace ℝ (Fin 2))
    (hcenterOfParam_def :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}),
        centerOfParam i t = AffineMap.lineMap (a i) (b i) t.1)
    (localArcAtParam :
      ∀ i, {t : ℝ // t ∈ centerParams i} → PolygonalArc)
    (entryPoint exitPoint :
      ∀ i, {t : ℝ // t ∈ centerParams i} → EuclideanSpace ℝ (Fin 2))
    (orderedLocalVertexBlocks :
      ∀ i, List (List (EuclideanSpace ℝ (Fin 2))))
    (assembledVertices : ι → List (EuclideanSpace ℝ (Fin 2)))
    (horderedLocalVertexBlocks_def : ∀ i,
      orderedLocalVertexBlocks i =
        (centerParams i).attach.map
          (fun t => (localArcAtParam i t).vertices))
    (hassembledVertices_def : ∀ i,
      assembledVertices i =
        EndpointUnitDiskAlternatingVertexList
          (a i) (b i) (orderedLocalVertexBlocks i))
    (hendpoint_ne : ∀ i, a i ≠ b i)
    (hcenterParams_sorted : ∀ i, (centerParams i).SortedLT)
    (hcenterOfParam_T :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}), centerOfParam i t ∈ T)
    (hlocalArcAtParam_props :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}),
        (localArcAtParam i t).source = entryPoint i t ∧
          (localArcAtParam i t).target = exitPoint i t ∧
            (localArcAtParam i t).carrier ⊆
              Metric.closedBall (centerOfParam i t) (r (centerOfParam i t)) ∧
              (localArcAtParam i t).relativeInterior ⊆
                Metric.ball (centerOfParam i t) (r (centerOfParam i t)))
    (hentryExitParameters :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}),
        (∃ s : ℝ, 0 < s ∧ s < t.1 ∧
          entryPoint i t = AffineMap.lineMap (a i) (b i) s) ∧
          (∃ s : ℝ, t.1 < s ∧ s < 1 ∧
            exitPoint i t = AffineMap.lineMap (a i) (b i) s))
    (horderedCutSeparation :
      ∀ i (t1 t2 : {t : ℝ // t ∈ centerParams i}),
        t1.1 < t2.1 →
          ∃ sExit sEntry : ℝ,
            t1.1 < sExit ∧
              sExit < sEntry ∧
                sEntry < t2.1 ∧
                  exitPoint i t1 = AffineMap.lineMap (a i) (b i) sExit ∧
                    entryPoint i t2 = AffineMap.lineMap (a i) (b i) sEntry)
    (hchordGapLocalCarrierPosition :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}) {α β e x : ℝ},
        entryPoint i t = AffineMap.lineMap (a i) (b i) e →
          exitPoint i t = AffineMap.lineMap (a i) (b i) x →
            0 ≤ α → α ≤ β → β ≤ 1 → e < x →
              (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
                p ∈ segment ℝ (AffineMap.lineMap (a i) (b i) α)
                    (AffineMap.lineMap (a i) (b i) β) →
                  p ∈ (localArcAtParam i t).carrier →
                    β < e → False) ∧
                (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
                  p ∈ segment ℝ (AffineMap.lineMap (a i) (b i) α)
                      (AffineMap.lineMap (a i) (b i) β) →
                    p ∈ (localArcAtParam i t).carrier →
                      β = e → p = entryPoint i t) ∧
                  (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
                    p ∈ segment ℝ (AffineMap.lineMap (a i) (b i) α)
                        (AffineMap.lineMap (a i) (b i) β) →
                      p ∈ (localArcAtParam i t).carrier →
                        x < α → False) ∧
                    (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
                      p ∈ segment ℝ (AffineMap.lineMap (a i) (b i) α)
                          (AffineMap.lineMap (a i) (b i) β) →
                        p ∈ (localArcAtParam i t).carrier →
                          x = α → p = exitPoint i t))
    (hinitialGapMeetsLocalCarrierOnly :
      ∀ i (t : {t : ℝ // t ∈ centerParams i})
        ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        p ∈ segment ℝ (a i) (entryPoint i t) →
          p ∈ (localArcAtParam i t).carrier → p = entryPoint i t)
    (hterminalGapMeetsLocalCarrierOnly :
      ∀ i (t : {t : ℝ // t ∈ centerParams i})
        ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        p ∈ segment ℝ (exitPoint i t) (b i) →
          p ∈ (localArcAtParam i t).carrier → p = exitPoint i t)
    (horderedOutsideGapMeetsNeighboringLocalCarriersOnly :
      ∀ i (t1 t2 : {t : ℝ // t ∈ centerParams i}),
        t1.1 < t2.1 →
          (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
            p ∈ segment ℝ (exitPoint i t1) (entryPoint i t2) →
              p ∈ (localArcAtParam i t1).carrier → p = exitPoint i t1) ∧
            (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
              p ∈ segment ℝ (exitPoint i t1) (entryPoint i t2) →
                p ∈ (localArcAtParam i t2).carrier → p = entryPoint i t2))
    (hdisjoint : ∀ ⦃z w : EuclideanSpace ℝ (Fin 2)⦄,
      z ∈ T → w ∈ T → z ≠ w →
        Disjoint (Metric.closedBall z (r z)) (Metric.closedBall w (r w)))
    (hassembledVertices_nodup : ∀ i, (assembledVertices i).Nodup)
    (hassembledVertices_avoid :
      ∀ i ⦃m k : ℕ⦄,
        (hm : m + 1 < (assembledVertices i).length) →
          (hk : k < (assembledVertices i).length) →
            k ≠ m → k ≠ m + 1 →
              (assembledVertices i)[k] ∉
                openSegment ℝ
                  (assembledVertices i)[m] (assembledVertices i)[m + 1])
    (hassembledEdgeEndpointRoles :
      ∀ i ⦃m : ℕ⦄,
        (hm : m + 1 < (assembledVertices i).length) →
          ((centerParams i).attach = [] ∧
              (assembledVertices i)[m] = a i ∧
                (assembledVertices i)[m + 1] = b i) ∨
            (∃ t ts X,
              (centerParams i).attach = t :: ts ∧
                (localArcAtParam i t).vertices.head? = some X ∧
                  (assembledVertices i)[m] = a i ∧
                    (assembledVertices i)[m + 1] = X) ∨
            (∃ (pre : List {t : ℝ // t ∈ centerParams i})
                (t : {t : ℝ // t ∈ centerParams i})
                (post : List {t : ℝ // t ∈ centerParams i}) (q : ℕ),
              ∃ hq : q + 1 < (localArcAtParam i t).vertices.length,
                (centerParams i).attach = pre ++ t :: post ∧
                  (assembledVertices i)[m] =
                    (localArcAtParam i t).vertices[q] ∧
                    (assembledVertices i)[m + 1] =
                      (localArcAtParam i t).vertices[q + 1]) ∨
            (∃ (pre : List {t : ℝ // t ∈ centerParams i})
                (t1 : {t : ℝ // t ∈ centerParams i})
                (t2 : {t : ℝ // t ∈ centerParams i})
                (post : List {t : ℝ // t ∈ centerParams i})
                (X Y : EuclideanSpace ℝ (Fin 2)),
              (centerParams i).attach = pre ++ t1 :: t2 :: post ∧
                (localArcAtParam i t1).vertices.getLast? = some X ∧
                  (localArcAtParam i t2).vertices.head? = some Y ∧
                    (assembledVertices i)[m] = X ∧
                      (assembledVertices i)[m + 1] = Y) ∨
            (∃ (pre : List {t : ℝ // t ∈ centerParams i})
                (t : {t : ℝ // t ∈ centerParams i})
                (X : EuclideanSpace ℝ (Fin 2)),
              (centerParams i).attach = pre ++ [t] ∧
                (localArcAtParam i t).vertices.getLast? = some X ∧
                  (assembledVertices i)[m] = X ∧
                    (assembledVertices i)[m + 1] = b i))
    (hlineSegmentInterSeparated :
      ∀ i {α β γ δ : ℝ}, α ≤ β → γ ≤ δ → β < γ →
        segment ℝ (AffineMap.lineMap (a i) (b i) α)
            (AffineMap.lineMap (a i) (b i) β) ∩
          segment ℝ (AffineMap.lineMap (a i) (b i) γ)
            (AffineMap.lineMap (a i) (b i) δ) =
        (∅ : Set (EuclideanSpace ℝ (Fin 2))))
    (i : ι) {m n : ℕ}
    (hm : m + 1 < (assembledVertices i).length)
    (hn : n + 1 < (assembledVertices i).length)
    (hmn : m < n)
    (hinitialIndexZero :
      ∀ ⦃k : ℕ⦄,
        (hk : k + 1 < (assembledVertices i).length) →
          endpointUnitDiskAssembly_initialRole a centerParams localArcAtParam
              assembledVertices i k hk →
            k = 0)
    (hterminalNoLater :
      ∀ ⦃k l : ℕ⦄,
        (hk : k + 1 < (assembledVertices i).length) →
        (hl : l + 1 < (assembledVertices i).length) →
        k < l →
          endpointUnitDiskAssembly_terminalRole b centerParams localArcAtParam
              assembledVertices i k hk →
            False)
    (hinter_of_forall_eq_right :
      (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        p ∈ segment ℝ (assembledVertices i)[m] (assembledVertices i)[m + 1] →
        p ∈ segment ℝ (assembledVertices i)[n] (assembledVertices i)[n + 1] →
          p = (assembledVertices i)[m + 1]) →
      (segment ℝ (assembledVertices i)[m] (assembledVertices i)[m + 1] ∩
          segment ℝ (assembledVertices i)[n] (assembledVertices i)[n + 1]) =
        if n = m + 1 then {(assembledVertices i)[n]} else ∅)
    (hattach_pairwise_lt :
      (centerParams i).attach.Pairwise
        (fun t1 t2 : {t : ℝ // t ∈ centerParams i} => t1.1 < t2.1))
    (hbridge_m :
      endpointUnitDiskAssembly_bridgeRole centerParams localArcAtParam
        assembledVertices i m hm)
    (hbridge_n :
      endpointUnitDiskAssembly_bridgeRole centerParams localArcAtParam
        assembledVertices i n hn) :
    (segment ℝ (assembledVertices i)[m] (assembledVertices i)[m + 1] ∩
        segment ℝ (assembledVertices i)[n] (assembledVertices i)[n + 1]) =
      if n = m + 1 then {(assembledVertices i)[n]} else ∅ := by
  rcases hbridge_m with
    ⟨pre_m, t1_m, t2_m, post_m, X_m, Y_m, hitems_m,
      hlast_m, hhead_m, hleft_m, hright_m⟩
  rcases hbridge_n with
    ⟨pre_n, t1_n, t2_n, post_n, X_n, Y_n, hitems_n,
      hlast_n, hhead_n, hleft_n, hright_n⟩
  have hlast_exit_m :
      (localArcAtParam i t1_m).vertices.getLast? =
        some (exitPoint i t1_m) := by
    have htarget := (localArcAtParam i t1_m).target_eq_last
    rw [(hlocalArcAtParam_props i t1_m).2.1] at htarget
    exact htarget
  have hX_m : X_m = exitPoint i t1_m := by
    exact (Option.some.inj (hlast_exit_m.symm.trans hlast_m)).symm
  have hhead_entry_m :
      (localArcAtParam i t2_m).vertices.head? =
        some (entryPoint i t2_m) := by
    have hsource := (localArcAtParam i t2_m).source_eq_head
    rw [(hlocalArcAtParam_props i t2_m).1] at hsource
    exact hsource
  have hY_m : Y_m = entryPoint i t2_m := by
    exact (Option.some.inj (hhead_entry_m.symm.trans hhead_m)).symm
  have hlast_exit_n :
      (localArcAtParam i t1_n).vertices.getLast? =
        some (exitPoint i t1_n) := by
    have htarget := (localArcAtParam i t1_n).target_eq_last
    rw [(hlocalArcAtParam_props i t1_n).2.1] at htarget
    exact htarget
  have hX_n : X_n = exitPoint i t1_n := by
    exact (Option.some.inj (hlast_exit_n.symm.trans hlast_n)).symm
  have hhead_entry_n :
      (localArcAtParam i t2_n).vertices.head? =
        some (entryPoint i t2_n) := by
    have hsource := (localArcAtParam i t2_n).source_eq_head
    rw [(hlocalArcAtParam_props i t2_n).1] at hsource
    exact hsource
  have hY_n : Y_n = entryPoint i t2_n := by
    exact (Option.some.inj (hhead_entry_n.symm.trans hhead_n)).symm
  have hpair_bridge_m := hattach_pairwise_lt
  rw [hitems_m] at hpair_bridge_m
  have htail_pair_m :
      (t1_m :: t2_m :: post_m).Pairwise
        (fun u v : {t : ℝ // t ∈ centerParams i} => u.1 < v.1) :=
    (List.pairwise_append.1 hpair_bridge_m).2.1
  have ht12_m : t1_m.1 < t2_m.1 :=
    (List.pairwise_cons.1 htail_pair_m).1 t2_m (by simp)
  have hpair_bridge_n := hattach_pairwise_lt
  rw [hitems_n] at hpair_bridge_n
  have htail_pair_n :
      (t1_n :: t2_n :: post_n).Pairwise
        (fun u v : {t : ℝ // t ∈ centerParams i} => u.1 < v.1) :=
    (List.pairwise_append.1 hpair_bridge_n).2.1
  have ht12_n : t1_n.1 < t2_n.1 :=
    (List.pairwise_cons.1 htail_pair_n).1 t2_n (by simp)
  rcases hentryExitParameters i t1_m with
    ⟨⟨e1_m, he1_m_pos, he1_m_lt_t1_m, hentry1_m⟩,
      ⟨x1_m, ht1_m_lt_x1_m, hx1_m_lt_one, hexit1_m⟩⟩
  rcases hentryExitParameters i t2_m with
    ⟨⟨e2_m, he2_m_pos, he2_m_lt_t2_m, hentry2_m⟩,
      ⟨x2_m, ht2_m_lt_x2_m, hx2_m_lt_one, hexit2_m⟩⟩
  rcases hentryExitParameters i t1_n with
    ⟨⟨e1_n, he1_n_pos, he1_n_lt_t1_n, hentry1_n⟩,
      ⟨x1_n, ht1_n_lt_x1_n, hx1_n_lt_one, hexit1_n⟩⟩
  rcases hentryExitParameters i t2_n with
    ⟨⟨e2_n, he2_n_pos, he2_n_lt_t2_n, hentry2_n⟩,
      ⟨x2_n, ht2_n_lt_x2_n, hx2_n_lt_one, hexit2_n⟩⟩
  rcases horderedCutSeparation i t1_m t2_m ht12_m with
    ⟨sExit_m, sEntry_m, _ht1_m_sExit, hsExitEntry_m,
      _hsEntry_t2_m, hexit_order_m, hentry_order_m⟩
  rcases horderedCutSeparation i t1_n t2_n ht12_n with
    ⟨sExit_n, sEntry_n, _ht1_n_sExit, hsExitEntry_n,
      _hsEntry_t2_n, hexit_order_n, hentry_order_n⟩
  let f : ℝ →ᵃ[ℝ] EuclideanSpace ℝ (Fin 2) :=
    AffineMap.lineMap (a i) (b i)
  have hf : Function.Injective f :=
    AffineMap.lineMap_injective (k := ℝ) (hendpoint_ne i)
  have hx1_m_eq : x1_m = sExit_m := by
    exact hf (by rw [← hexit1_m, ← hexit_order_m])
  have he2_m_eq : e2_m = sEntry_m := by
    exact hf (by rw [← hentry2_m, ← hentry_order_m])
  have hx1_m_lt_e2_m : x1_m < e2_m := by
    linarith
  have hx1_n_eq : x1_n = sExit_n := by
    exact hf (by rw [← hexit1_n, ← hexit_order_n])
  have he2_n_eq : e2_n = sEntry_n := by
    exact hf (by rw [← hentry2_n, ← hentry_order_n])
  have hx1_n_lt_e2_n : x1_n < e2_n := by
    linarith
  have ht1_n_attach : t1_n ∈ (centerParams i).attach := by
    rw [hitems_n]
    simp
  have ht1_n_cases :
      t1_n ∈ pre_m ∨ t1_n = t1_m ∨ t1_n = t2_m ∨
        t1_n ∈ post_m := by
    have ht_mem : t1_n ∈ pre_m ++ t1_m :: t2_m :: post_m := by
      simpa [hitems_m] using ht1_n_attach
    simpa [List.mem_append, List.mem_cons] using ht_mem
  exact hinter_of_forall_eq_right (by
    intro p hp_bridge_m hp_bridge_n
    have hp_bridge_m' :
        p ∈ segment ℝ (exitPoint i t1_m) (entryPoint i t2_m) := by
      simpa [hleft_m, hright_m, hX_m, hY_m] using hp_bridge_m
    have hp_bridge_n' :
        p ∈ segment ℝ (exitPoint i t1_n) (entryPoint i t2_n) := by
      simpa [hleft_n, hright_n, hX_n, hY_n] using hp_bridge_n
    rcases ht1_n_cases with ht1_n_pre | ht1_n_cases
    · have ht1_n_lt_t1_m : t1_n.1 < t1_m.1 :=
        (List.pairwise_append.1 hpair_bridge_m).2.2
          t1_n ht1_n_pre t1_m (by simp)
      have ht1_m_attach : t1_m ∈ (centerParams i).attach := by
        rw [hitems_m]
        simp
      have ht1_m_cases :
          t1_m ∈ pre_n ∨ t1_m = t1_n ∨ t1_m = t2_n ∨
            t1_m ∈ post_n := by
        have ht_mem : t1_m ∈ pre_n ++ t1_n :: t2_n :: post_n := by
          simpa [hitems_n] using ht1_m_attach
        simpa [List.mem_append, List.mem_cons] using ht_mem
      rcases ht1_m_cases with ht1_m_pre_n | ht1_m_cases
      · have ht1_m_lt_t1_n : t1_m.1 < t1_n.1 :=
          (List.pairwise_append.1 hpair_bridge_n).2.2
            t1_m ht1_m_pre_n t1_n (by simp)
        exact False.elim (by linarith)
      rcases ht1_m_cases with ht1_m_eq_t1_n | ht1_m_cases
      · have hvals : t1_m.1 = t1_n.1 := by
          simpa [ht1_m_eq_t1_n]
        exact False.elim (by linarith)
      rcases ht1_m_cases with ht1_m_eq_t2_n | ht1_m_post_n
      · subst t2_n
        have he2_n_lt_x1_m : e2_n < x1_m := by
          linarith
        have hdisjoint_bridge :
            segment ℝ (exitPoint i t1_n) (entryPoint i t1_m) ∩
                segment ℝ (exitPoint i t1_m) (entryPoint i t2_m) =
              (∅ : Set (EuclideanSpace ℝ (Fin 2))) := by
          simpa [f, hexit1_n, hentry2_n, hexit1_m, hentry2_m] using
            (hlineSegmentInterSeparated i
              (α := x1_n) (β := e2_n) (γ := x1_m) (δ := e2_m)
              (le_of_lt hx1_n_lt_e2_n)
              (le_of_lt hx1_m_lt_e2_m) he2_n_lt_x1_m)
        have hp_empty :
            p ∈ (∅ : Set (EuclideanSpace ℝ (Fin 2))) := by
          simpa [hdisjoint_bridge] using
            (show p ∈ segment ℝ (exitPoint i t1_n) (entryPoint i t1_m) ∩
                segment ℝ (exitPoint i t1_m) (entryPoint i t2_m) from
              ⟨by simpa using hp_bridge_n', hp_bridge_m'⟩)
        exact False.elim hp_empty
      · have htail2_pair_n :
            (t2_n :: post_n).Pairwise
              (fun u v : {t : ℝ // t ∈ centerParams i} => u.1 < v.1) :=
          (List.pairwise_cons.1 htail_pair_n).2
        have ht2_n_lt_t1_m : t2_n.1 < t1_m.1 :=
          (List.pairwise_cons.1 htail2_pair_n).1
            t1_m ht1_m_post_n
        rcases horderedCutSeparation i t2_n t1_m ht2_n_lt_t1_m with
          ⟨sExit', sEntry', _ht2_n_sExit, hsExitEntry',
            _hsEntry_t1_m, hexit_order', hentry_order'⟩
        have hx2_n_eq : x2_n = sExit' := by
          exact hf (by rw [← hexit2_n, ← hexit_order'])
        have he1_m_eq : e1_m = sEntry' := by
          exact hf (by rw [← hentry1_m, ← hentry_order'])
        have hx2_n_lt_e1_m : x2_n < e1_m := by
          linarith
        have he2_n_lt_x1_m : e2_n < x1_m := by
          linarith
        have hdisjoint_bridge :
            segment ℝ (exitPoint i t1_n) (entryPoint i t2_n) ∩
                segment ℝ (exitPoint i t1_m) (entryPoint i t2_m) =
              (∅ : Set (EuclideanSpace ℝ (Fin 2))) := by
          simpa [f, hexit1_n, hentry2_n, hexit1_m, hentry2_m] using
            (hlineSegmentInterSeparated i
              (α := x1_n) (β := e2_n) (γ := x1_m) (δ := e2_m)
              (le_of_lt hx1_n_lt_e2_n)
              (le_of_lt hx1_m_lt_e2_m) he2_n_lt_x1_m)
        have hp_empty :
            p ∈ (∅ : Set (EuclideanSpace ℝ (Fin 2))) := by
          simpa [hdisjoint_bridge] using
            (show p ∈ segment ℝ (exitPoint i t1_n) (entryPoint i t2_n) ∩
                segment ℝ (exitPoint i t1_m) (entryPoint i t2_m) from
              ⟨hp_bridge_n', hp_bridge_m'⟩)
        exact False.elim hp_empty
    rcases ht1_n_cases with ht1_n_eq_t1_m | ht1_n_cases
    · subst t1_n
      have hval :
          (assembledVertices i)[m] = (assembledVertices i)[n] := by
        rw [hleft_m, hleft_n, hX_m, hX_n]
      have hidx :=
        ((hassembledVertices_nodup i).getElem_inj_iff).1 hval
      exact False.elim (by omega)
    rcases ht1_n_cases with ht1_n_eq_t2_m | ht1_n_post
    · subst t1_n
      have he2_m_lt_x1_n : e2_m < x1_n := by
        linarith
      have hdisjoint_bridge :
          segment ℝ (exitPoint i t1_m) (entryPoint i t2_m) ∩
              segment ℝ (exitPoint i t2_m) (entryPoint i t2_n) =
            (∅ : Set (EuclideanSpace ℝ (Fin 2))) := by
        simpa [f, hexit1_m, hentry2_m, hexit1_n, hentry2_n] using
          (hlineSegmentInterSeparated i
            (α := x1_m) (β := e2_m) (γ := x1_n) (δ := e2_n)
            (le_of_lt hx1_m_lt_e2_m)
            (le_of_lt hx1_n_lt_e2_n) he2_m_lt_x1_n)
      have hp_empty :
          p ∈ (∅ : Set (EuclideanSpace ℝ (Fin 2))) := by
        simpa [hdisjoint_bridge] using
          (show p ∈ segment ℝ (exitPoint i t1_m) (entryPoint i t2_m) ∩
              segment ℝ (exitPoint i t2_m) (entryPoint i t2_n) from
            ⟨hp_bridge_m', by simpa using hp_bridge_n'⟩)
      exact False.elim hp_empty
    · have hprefix_pair_m :
        ((pre_m ++ [t1_m, t2_m]) ++ post_m).Pairwise
          (fun u v : {t : ℝ // t ∈ centerParams i} => u.1 < v.1) := by
        simpa [List.append_assoc] using hpair_bridge_m
      have ht2_m_lt_t1_n : t2_m.1 < t1_n.1 :=
        (List.pairwise_append.1 hprefix_pair_m).2.2
          t2_m (by simp) t1_n ht1_n_post
      rcases horderedCutSeparation i t2_m t1_n ht2_m_lt_t1_n with
        ⟨sExit', sEntry', _ht2_m_sExit, hsExitEntry',
          _hsEntry_t1_n, hexit_order', hentry_order'⟩
      have hx2_m_eq : x2_m = sExit' := by
        exact hf (by rw [← hexit2_m, ← hexit_order'])
      have he1_n_eq : e1_n = sEntry' := by
        exact hf (by rw [← hentry1_n, ← hentry_order'])
      have hx2_m_lt_e1_n : x2_m < e1_n := by
        linarith
      have he2_m_lt_x1_n : e2_m < x1_n := by
        linarith
      have hdisjoint_bridge :
          segment ℝ (exitPoint i t1_m) (entryPoint i t2_m) ∩
              segment ℝ (exitPoint i t1_n) (entryPoint i t2_n) =
            (∅ : Set (EuclideanSpace ℝ (Fin 2))) := by
        simpa [f, hexit1_m, hentry2_m, hexit1_n, hentry2_n] using
          (hlineSegmentInterSeparated i
            (α := x1_m) (β := e2_m) (γ := x1_n) (δ := e2_n)
            (le_of_lt hx1_m_lt_e2_m)
            (le_of_lt hx1_n_lt_e2_n) he2_m_lt_x1_n)
      have hp_empty :
          p ∈ (∅ : Set (EuclideanSpace ℝ (Fin 2))) := by
        simpa [hdisjoint_bridge] using
          (show p ∈ segment ℝ (exitPoint i t1_m) (entryPoint i t2_m) ∩
              segment ℝ (exitPoint i t1_n) (entryPoint i t2_n) from
            ⟨hp_bridge_m', hp_bridge_n'⟩)
      exact False.elim hp_empty)

private lemma endpointUnitDiskAssembly_segments_bridge_terminal
    {ι : Type*} [Fintype ι]
    (a b : ι → EuclideanSpace ℝ (Fin 2))
    (T : Finset (EuclideanSpace ℝ (Fin 2)))
    (r : EuclideanSpace ℝ (Fin 2) → ℝ)
    (centerParams : ι → List ℝ)
    (centerOfParam :
      ∀ i, {t : ℝ // t ∈ centerParams i} → EuclideanSpace ℝ (Fin 2))
    (hcenterOfParam_def :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}),
        centerOfParam i t = AffineMap.lineMap (a i) (b i) t.1)
    (localArcAtParam :
      ∀ i, {t : ℝ // t ∈ centerParams i} → PolygonalArc)
    (entryPoint exitPoint :
      ∀ i, {t : ℝ // t ∈ centerParams i} → EuclideanSpace ℝ (Fin 2))
    (orderedLocalVertexBlocks :
      ∀ i, List (List (EuclideanSpace ℝ (Fin 2))))
    (assembledVertices : ι → List (EuclideanSpace ℝ (Fin 2)))
    (horderedLocalVertexBlocks_def : ∀ i,
      orderedLocalVertexBlocks i =
        (centerParams i).attach.map
          (fun t => (localArcAtParam i t).vertices))
    (hassembledVertices_def : ∀ i,
      assembledVertices i =
        EndpointUnitDiskAlternatingVertexList
          (a i) (b i) (orderedLocalVertexBlocks i))
    (hendpoint_ne : ∀ i, a i ≠ b i)
    (hcenterParams_sorted : ∀ i, (centerParams i).SortedLT)
    (hcenterOfParam_T :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}), centerOfParam i t ∈ T)
    (hlocalArcAtParam_props :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}),
        (localArcAtParam i t).source = entryPoint i t ∧
          (localArcAtParam i t).target = exitPoint i t ∧
            (localArcAtParam i t).carrier ⊆
              Metric.closedBall (centerOfParam i t) (r (centerOfParam i t)) ∧
              (localArcAtParam i t).relativeInterior ⊆
                Metric.ball (centerOfParam i t) (r (centerOfParam i t)))
    (hentryExitParameters :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}),
        (∃ s : ℝ, 0 < s ∧ s < t.1 ∧
          entryPoint i t = AffineMap.lineMap (a i) (b i) s) ∧
          (∃ s : ℝ, t.1 < s ∧ s < 1 ∧
            exitPoint i t = AffineMap.lineMap (a i) (b i) s))
    (horderedCutSeparation :
      ∀ i (t1 t2 : {t : ℝ // t ∈ centerParams i}),
        t1.1 < t2.1 →
          ∃ sExit sEntry : ℝ,
            t1.1 < sExit ∧
              sExit < sEntry ∧
                sEntry < t2.1 ∧
                  exitPoint i t1 = AffineMap.lineMap (a i) (b i) sExit ∧
                    entryPoint i t2 = AffineMap.lineMap (a i) (b i) sEntry)
    (hchordGapLocalCarrierPosition :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}) {α β e x : ℝ},
        entryPoint i t = AffineMap.lineMap (a i) (b i) e →
          exitPoint i t = AffineMap.lineMap (a i) (b i) x →
            0 ≤ α → α ≤ β → β ≤ 1 → e < x →
              (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
                p ∈ segment ℝ (AffineMap.lineMap (a i) (b i) α)
                    (AffineMap.lineMap (a i) (b i) β) →
                  p ∈ (localArcAtParam i t).carrier →
                    β < e → False) ∧
                (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
                  p ∈ segment ℝ (AffineMap.lineMap (a i) (b i) α)
                      (AffineMap.lineMap (a i) (b i) β) →
                    p ∈ (localArcAtParam i t).carrier →
                      β = e → p = entryPoint i t) ∧
                  (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
                    p ∈ segment ℝ (AffineMap.lineMap (a i) (b i) α)
                        (AffineMap.lineMap (a i) (b i) β) →
                      p ∈ (localArcAtParam i t).carrier →
                        x < α → False) ∧
                    (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
                      p ∈ segment ℝ (AffineMap.lineMap (a i) (b i) α)
                          (AffineMap.lineMap (a i) (b i) β) →
                        p ∈ (localArcAtParam i t).carrier →
                          x = α → p = exitPoint i t))
    (hinitialGapMeetsLocalCarrierOnly :
      ∀ i (t : {t : ℝ // t ∈ centerParams i})
        ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        p ∈ segment ℝ (a i) (entryPoint i t) →
          p ∈ (localArcAtParam i t).carrier → p = entryPoint i t)
    (hterminalGapMeetsLocalCarrierOnly :
      ∀ i (t : {t : ℝ // t ∈ centerParams i})
        ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        p ∈ segment ℝ (exitPoint i t) (b i) →
          p ∈ (localArcAtParam i t).carrier → p = exitPoint i t)
    (horderedOutsideGapMeetsNeighboringLocalCarriersOnly :
      ∀ i (t1 t2 : {t : ℝ // t ∈ centerParams i}),
        t1.1 < t2.1 →
          (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
            p ∈ segment ℝ (exitPoint i t1) (entryPoint i t2) →
              p ∈ (localArcAtParam i t1).carrier → p = exitPoint i t1) ∧
            (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
              p ∈ segment ℝ (exitPoint i t1) (entryPoint i t2) →
                p ∈ (localArcAtParam i t2).carrier → p = entryPoint i t2))
    (hdisjoint : ∀ ⦃z w : EuclideanSpace ℝ (Fin 2)⦄,
      z ∈ T → w ∈ T → z ≠ w →
        Disjoint (Metric.closedBall z (r z)) (Metric.closedBall w (r w)))
    (hassembledVertices_nodup : ∀ i, (assembledVertices i).Nodup)
    (hassembledVertices_avoid :
      ∀ i ⦃m k : ℕ⦄,
        (hm : m + 1 < (assembledVertices i).length) →
          (hk : k < (assembledVertices i).length) →
            k ≠ m → k ≠ m + 1 →
              (assembledVertices i)[k] ∉
                openSegment ℝ
                  (assembledVertices i)[m] (assembledVertices i)[m + 1])
    (hassembledEdgeEndpointRoles :
      ∀ i ⦃m : ℕ⦄,
        (hm : m + 1 < (assembledVertices i).length) →
          ((centerParams i).attach = [] ∧
              (assembledVertices i)[m] = a i ∧
                (assembledVertices i)[m + 1] = b i) ∨
            (∃ t ts X,
              (centerParams i).attach = t :: ts ∧
                (localArcAtParam i t).vertices.head? = some X ∧
                  (assembledVertices i)[m] = a i ∧
                    (assembledVertices i)[m + 1] = X) ∨
            (∃ (pre : List {t : ℝ // t ∈ centerParams i})
                (t : {t : ℝ // t ∈ centerParams i})
                (post : List {t : ℝ // t ∈ centerParams i}) (q : ℕ),
              ∃ hq : q + 1 < (localArcAtParam i t).vertices.length,
                (centerParams i).attach = pre ++ t :: post ∧
                  (assembledVertices i)[m] =
                    (localArcAtParam i t).vertices[q] ∧
                    (assembledVertices i)[m + 1] =
                      (localArcAtParam i t).vertices[q + 1]) ∨
            (∃ (pre : List {t : ℝ // t ∈ centerParams i})
                (t1 : {t : ℝ // t ∈ centerParams i})
                (t2 : {t : ℝ // t ∈ centerParams i})
                (post : List {t : ℝ // t ∈ centerParams i})
                (X Y : EuclideanSpace ℝ (Fin 2)),
              (centerParams i).attach = pre ++ t1 :: t2 :: post ∧
                (localArcAtParam i t1).vertices.getLast? = some X ∧
                  (localArcAtParam i t2).vertices.head? = some Y ∧
                    (assembledVertices i)[m] = X ∧
                      (assembledVertices i)[m + 1] = Y) ∨
            (∃ (pre : List {t : ℝ // t ∈ centerParams i})
                (t : {t : ℝ // t ∈ centerParams i})
                (X : EuclideanSpace ℝ (Fin 2)),
              (centerParams i).attach = pre ++ [t] ∧
                (localArcAtParam i t).vertices.getLast? = some X ∧
                  (assembledVertices i)[m] = X ∧
                    (assembledVertices i)[m + 1] = b i))
    (hlineSegmentInterSeparated :
      ∀ i {α β γ δ : ℝ}, α ≤ β → γ ≤ δ → β < γ →
        segment ℝ (AffineMap.lineMap (a i) (b i) α)
            (AffineMap.lineMap (a i) (b i) β) ∩
          segment ℝ (AffineMap.lineMap (a i) (b i) γ)
            (AffineMap.lineMap (a i) (b i) δ) =
        (∅ : Set (EuclideanSpace ℝ (Fin 2))))
    (i : ι) {m n : ℕ}
    (hm : m + 1 < (assembledVertices i).length)
    (hn : n + 1 < (assembledVertices i).length)
    (hmn : m < n)
    (hinitialIndexZero :
      ∀ ⦃k : ℕ⦄,
        (hk : k + 1 < (assembledVertices i).length) →
          endpointUnitDiskAssembly_initialRole a centerParams localArcAtParam
              assembledVertices i k hk →
            k = 0)
    (hterminalNoLater :
      ∀ ⦃k l : ℕ⦄,
        (hk : k + 1 < (assembledVertices i).length) →
        (hl : l + 1 < (assembledVertices i).length) →
        k < l →
          endpointUnitDiskAssembly_terminalRole b centerParams localArcAtParam
              assembledVertices i k hk →
            False)
    (hinter_of_forall_eq_right :
      (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        p ∈ segment ℝ (assembledVertices i)[m] (assembledVertices i)[m + 1] →
        p ∈ segment ℝ (assembledVertices i)[n] (assembledVertices i)[n + 1] →
          p = (assembledVertices i)[m + 1]) →
      (segment ℝ (assembledVertices i)[m] (assembledVertices i)[m + 1] ∩
          segment ℝ (assembledVertices i)[n] (assembledVertices i)[n + 1]) =
        if n = m + 1 then {(assembledVertices i)[n]} else ∅)
    (hattach_pairwise_lt :
      (centerParams i).attach.Pairwise
        (fun t1 t2 : {t : ℝ // t ∈ centerParams i} => t1.1 < t2.1))
    (hbridge_m :
      endpointUnitDiskAssembly_bridgeRole centerParams localArcAtParam
        assembledVertices i m hm)
    (hterminal_n :
      endpointUnitDiskAssembly_terminalRole b centerParams localArcAtParam
        assembledVertices i n hn) :
    (segment ℝ (assembledVertices i)[m] (assembledVertices i)[m + 1] ∩
        segment ℝ (assembledVertices i)[n] (assembledVertices i)[n + 1]) =
      if n = m + 1 then {(assembledVertices i)[n]} else ∅ := by
  rcases hbridge_m with
    ⟨pre_m, t1_m, t2_m, post_m, X_m, Y_m, hitems_m,
      hlast_m, hhead_m, hleft_m, hright_m⟩
  rcases hterminal_n with
    ⟨pre_n, t_n, X_n, hitems_n, hlast_n, hleft_n, hright_n⟩
  have hlast_exit_m :
      (localArcAtParam i t1_m).vertices.getLast? =
        some (exitPoint i t1_m) := by
    have htarget := (localArcAtParam i t1_m).target_eq_last
    rw [(hlocalArcAtParam_props i t1_m).2.1] at htarget
    exact htarget
  have hX_m : X_m = exitPoint i t1_m := by
    exact (Option.some.inj (hlast_exit_m.symm.trans hlast_m)).symm
  have hhead_entry_m :
      (localArcAtParam i t2_m).vertices.head? =
        some (entryPoint i t2_m) := by
    have hsource := (localArcAtParam i t2_m).source_eq_head
    rw [(hlocalArcAtParam_props i t2_m).1] at hsource
    exact hsource
  have hY_m : Y_m = entryPoint i t2_m := by
    exact (Option.some.inj (hhead_entry_m.symm.trans hhead_m)).symm
  have hlast_exit_n :
      (localArcAtParam i t_n).vertices.getLast? =
        some (exitPoint i t_n) := by
    have htarget := (localArcAtParam i t_n).target_eq_last
    rw [(hlocalArcAtParam_props i t_n).2.1] at htarget
    exact htarget
  have hX_n : X_n = exitPoint i t_n := by
    exact (Option.some.inj (hlast_exit_n.symm.trans hlast_n)).symm
  have hpair_bridge := hattach_pairwise_lt
  rw [hitems_m] at hpair_bridge
  have htail_pair :
      (t1_m :: t2_m :: post_m).Pairwise
        (fun u v : {t : ℝ // t ∈ centerParams i} => u.1 < v.1) :=
    (List.pairwise_append.1 hpair_bridge).2.1
  have ht12 : t1_m.1 < t2_m.1 :=
    (List.pairwise_cons.1 htail_pair).1 t2_m (by simp)
  have ht2_attach : t2_m ∈ (centerParams i).attach := by
    rw [hitems_m]
    simp
  have ht2_le_tn : t2_m.1 ≤ t_n.1 := by
    have ht2_cases : t2_m ∈ pre_n ∨ t2_m = t_n := by
      have ht2_mem : t2_m ∈ pre_n ∨ t2_m ∈ [t_n] := by
        simpa [hitems_n, List.mem_append] using ht2_attach
      rcases ht2_mem with ht_pre | ht_last
      · exact Or.inl ht_pre
      · exact Or.inr (by simpa using ht_last)
    rcases ht2_cases with ht_pre | ht_eq
    · exact le_of_lt (by
        have hpair := hattach_pairwise_lt
        rw [hitems_n] at hpair
        exact (List.pairwise_append.1 hpair).2.2
          t2_m ht_pre t_n (by simp))
    · subst t_n
      exact le_rfl
  rcases hentryExitParameters i t1_m with
    ⟨⟨e1, he1_pos, he1_lt_t1, hentry1⟩,
      ⟨x1, ht1_lt_x1, hx1_lt_one, hexit1⟩⟩
  rcases hentryExitParameters i t2_m with
    ⟨⟨e2, he2_pos, he2_lt_t2, hentry2⟩,
      ⟨x2, ht2_lt_x2, hx2_lt_one, hexit2⟩⟩
  rcases hentryExitParameters i t_n with
    ⟨⟨eN, heN_pos, heN_lt_tN, hentryN⟩,
      ⟨xN, htN_lt_xN, hxN_lt_one, hexitN⟩⟩
  rcases horderedCutSeparation i t1_m t2_m ht12 with
    ⟨sExit, sEntry, _ht1_sExit, hsExitEntry, _hsEntry_t2,
      hexit_order, hentry_order⟩
  let f : ℝ →ᵃ[ℝ] EuclideanSpace ℝ (Fin 2) :=
    AffineMap.lineMap (a i) (b i)
  have hf : Function.Injective f :=
    AffineMap.lineMap_injective (k := ℝ) (hendpoint_ne i)
  have hx1_eq : x1 = sExit := by
    exact hf (by rw [← hexit1, ← hexit_order])
  have he2_eq : e2 = sEntry := by
    exact hf (by rw [← hentry2, ← hentry_order])
  have hx1_lt_e2 : x1 < e2 := by
    linarith
  have he2_lt_xN : e2 < xN := by
    linarith
  have hdisjoint_bridge_terminal :
      segment ℝ (exitPoint i t1_m) (entryPoint i t2_m) ∩
          segment ℝ (exitPoint i t_n) (b i) =
        (∅ : Set (EuclideanSpace ℝ (Fin 2))) := by
    simpa [f, hexit1, hentry2, hexitN] using
      (hlineSegmentInterSeparated i
        (α := x1) (β := e2) (γ := xN) (δ := (1 : ℝ))
        (le_of_lt hx1_lt_e2) (by linarith) he2_lt_xN)
  exact hinter_of_forall_eq_right (by
    intro p hp_bridge hp_terminal
    have hp_bridge' :
        p ∈ segment ℝ (exitPoint i t1_m) (entryPoint i t2_m) := by
      simpa [hleft_m, hright_m, hX_m, hY_m] using hp_bridge
    have hp_terminal' :
        p ∈ segment ℝ (exitPoint i t_n) (b i) := by
      simpa [hleft_n, hright_n, hX_n] using hp_terminal
    have hp_empty :
        p ∈ (∅ : Set (EuclideanSpace ℝ (Fin 2))) := by
      simpa [hdisjoint_bridge_terminal] using
        (show p ∈ segment ℝ (exitPoint i t1_m) (entryPoint i t2_m) ∩
            segment ℝ (exitPoint i t_n) (b i) from
          ⟨hp_bridge', hp_terminal'⟩)
    exact False.elim hp_empty)

private lemma endpointUnitDiskAssembly_segments_bridge
    {ι : Type*} [Fintype ι]
    (a b : ι → EuclideanSpace ℝ (Fin 2))
    (T : Finset (EuclideanSpace ℝ (Fin 2)))
    (r : EuclideanSpace ℝ (Fin 2) → ℝ)
    (centerParams : ι → List ℝ)
    (centerOfParam :
      ∀ i, {t : ℝ // t ∈ centerParams i} → EuclideanSpace ℝ (Fin 2))
    (hcenterOfParam_def :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}),
        centerOfParam i t = AffineMap.lineMap (a i) (b i) t.1)
    (localArcAtParam :
      ∀ i, {t : ℝ // t ∈ centerParams i} → PolygonalArc)
    (entryPoint exitPoint :
      ∀ i, {t : ℝ // t ∈ centerParams i} → EuclideanSpace ℝ (Fin 2))
    (orderedLocalVertexBlocks :
      ∀ i, List (List (EuclideanSpace ℝ (Fin 2))))
    (assembledVertices : ι → List (EuclideanSpace ℝ (Fin 2)))
    (horderedLocalVertexBlocks_def : ∀ i,
      orderedLocalVertexBlocks i =
        (centerParams i).attach.map
          (fun t => (localArcAtParam i t).vertices))
    (hassembledVertices_def : ∀ i,
      assembledVertices i =
        EndpointUnitDiskAlternatingVertexList
          (a i) (b i) (orderedLocalVertexBlocks i))
    (hendpoint_ne : ∀ i, a i ≠ b i)
    (hcenterParams_sorted : ∀ i, (centerParams i).SortedLT)
    (hcenterOfParam_T :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}), centerOfParam i t ∈ T)
    (hlocalArcAtParam_props :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}),
        (localArcAtParam i t).source = entryPoint i t ∧
          (localArcAtParam i t).target = exitPoint i t ∧
            (localArcAtParam i t).carrier ⊆
              Metric.closedBall (centerOfParam i t) (r (centerOfParam i t)) ∧
              (localArcAtParam i t).relativeInterior ⊆
                Metric.ball (centerOfParam i t) (r (centerOfParam i t)))
    (hentryExitParameters :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}),
        (∃ s : ℝ, 0 < s ∧ s < t.1 ∧
          entryPoint i t = AffineMap.lineMap (a i) (b i) s) ∧
          (∃ s : ℝ, t.1 < s ∧ s < 1 ∧
            exitPoint i t = AffineMap.lineMap (a i) (b i) s))
    (horderedCutSeparation :
      ∀ i (t1 t2 : {t : ℝ // t ∈ centerParams i}),
        t1.1 < t2.1 →
          ∃ sExit sEntry : ℝ,
            t1.1 < sExit ∧
              sExit < sEntry ∧
                sEntry < t2.1 ∧
                  exitPoint i t1 = AffineMap.lineMap (a i) (b i) sExit ∧
                    entryPoint i t2 = AffineMap.lineMap (a i) (b i) sEntry)
    (hchordGapLocalCarrierPosition :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}) {α β e x : ℝ},
        entryPoint i t = AffineMap.lineMap (a i) (b i) e →
          exitPoint i t = AffineMap.lineMap (a i) (b i) x →
            0 ≤ α → α ≤ β → β ≤ 1 → e < x →
              (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
                p ∈ segment ℝ (AffineMap.lineMap (a i) (b i) α)
                    (AffineMap.lineMap (a i) (b i) β) →
                  p ∈ (localArcAtParam i t).carrier →
                    β < e → False) ∧
                (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
                  p ∈ segment ℝ (AffineMap.lineMap (a i) (b i) α)
                      (AffineMap.lineMap (a i) (b i) β) →
                    p ∈ (localArcAtParam i t).carrier →
                      β = e → p = entryPoint i t) ∧
                  (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
                    p ∈ segment ℝ (AffineMap.lineMap (a i) (b i) α)
                        (AffineMap.lineMap (a i) (b i) β) →
                      p ∈ (localArcAtParam i t).carrier →
                        x < α → False) ∧
                    (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
                      p ∈ segment ℝ (AffineMap.lineMap (a i) (b i) α)
                          (AffineMap.lineMap (a i) (b i) β) →
                        p ∈ (localArcAtParam i t).carrier →
                          x = α → p = exitPoint i t))
    (hinitialGapMeetsLocalCarrierOnly :
      ∀ i (t : {t : ℝ // t ∈ centerParams i})
        ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        p ∈ segment ℝ (a i) (entryPoint i t) →
          p ∈ (localArcAtParam i t).carrier → p = entryPoint i t)
    (hterminalGapMeetsLocalCarrierOnly :
      ∀ i (t : {t : ℝ // t ∈ centerParams i})
        ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        p ∈ segment ℝ (exitPoint i t) (b i) →
          p ∈ (localArcAtParam i t).carrier → p = exitPoint i t)
    (horderedOutsideGapMeetsNeighboringLocalCarriersOnly :
      ∀ i (t1 t2 : {t : ℝ // t ∈ centerParams i}),
        t1.1 < t2.1 →
          (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
            p ∈ segment ℝ (exitPoint i t1) (entryPoint i t2) →
              p ∈ (localArcAtParam i t1).carrier → p = exitPoint i t1) ∧
            (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
              p ∈ segment ℝ (exitPoint i t1) (entryPoint i t2) →
                p ∈ (localArcAtParam i t2).carrier → p = entryPoint i t2))
    (hdisjoint : ∀ ⦃z w : EuclideanSpace ℝ (Fin 2)⦄,
      z ∈ T → w ∈ T → z ≠ w →
        Disjoint (Metric.closedBall z (r z)) (Metric.closedBall w (r w)))
    (hassembledVertices_nodup : ∀ i, (assembledVertices i).Nodup)
    (hassembledVertices_avoid :
      ∀ i ⦃m k : ℕ⦄,
        (hm : m + 1 < (assembledVertices i).length) →
          (hk : k < (assembledVertices i).length) →
            k ≠ m → k ≠ m + 1 →
              (assembledVertices i)[k] ∉
                openSegment ℝ
                  (assembledVertices i)[m] (assembledVertices i)[m + 1])
    (hassembledEdgeEndpointRoles :
      ∀ i ⦃m : ℕ⦄,
        (hm : m + 1 < (assembledVertices i).length) →
          ((centerParams i).attach = [] ∧
              (assembledVertices i)[m] = a i ∧
                (assembledVertices i)[m + 1] = b i) ∨
            (∃ t ts X,
              (centerParams i).attach = t :: ts ∧
                (localArcAtParam i t).vertices.head? = some X ∧
                  (assembledVertices i)[m] = a i ∧
                    (assembledVertices i)[m + 1] = X) ∨
            (∃ (pre : List {t : ℝ // t ∈ centerParams i})
                (t : {t : ℝ // t ∈ centerParams i})
                (post : List {t : ℝ // t ∈ centerParams i}) (q : ℕ),
              ∃ hq : q + 1 < (localArcAtParam i t).vertices.length,
                (centerParams i).attach = pre ++ t :: post ∧
                  (assembledVertices i)[m] =
                    (localArcAtParam i t).vertices[q] ∧
                    (assembledVertices i)[m + 1] =
                      (localArcAtParam i t).vertices[q + 1]) ∨
            (∃ (pre : List {t : ℝ // t ∈ centerParams i})
                (t1 : {t : ℝ // t ∈ centerParams i})
                (t2 : {t : ℝ // t ∈ centerParams i})
                (post : List {t : ℝ // t ∈ centerParams i})
                (X Y : EuclideanSpace ℝ (Fin 2)),
              (centerParams i).attach = pre ++ t1 :: t2 :: post ∧
                (localArcAtParam i t1).vertices.getLast? = some X ∧
                  (localArcAtParam i t2).vertices.head? = some Y ∧
                    (assembledVertices i)[m] = X ∧
                      (assembledVertices i)[m + 1] = Y) ∨
            (∃ (pre : List {t : ℝ // t ∈ centerParams i})
                (t : {t : ℝ // t ∈ centerParams i})
                (X : EuclideanSpace ℝ (Fin 2)),
              (centerParams i).attach = pre ++ [t] ∧
                (localArcAtParam i t).vertices.getLast? = some X ∧
                  (assembledVertices i)[m] = X ∧
                    (assembledVertices i)[m + 1] = b i))
    (hlineSegmentInterSeparated :
      ∀ i {α β γ δ : ℝ}, α ≤ β → γ ≤ δ → β < γ →
        segment ℝ (AffineMap.lineMap (a i) (b i) α)
            (AffineMap.lineMap (a i) (b i) β) ∩
          segment ℝ (AffineMap.lineMap (a i) (b i) γ)
            (AffineMap.lineMap (a i) (b i) δ) =
        (∅ : Set (EuclideanSpace ℝ (Fin 2))))
    (i : ι) {m n : ℕ}
    (hm : m + 1 < (assembledVertices i).length)
    (hn : n + 1 < (assembledVertices i).length)
    (hmn : m < n)
    (hinitialIndexZero :
      ∀ ⦃k : ℕ⦄,
        (hk : k + 1 < (assembledVertices i).length) →
          endpointUnitDiskAssembly_initialRole a centerParams localArcAtParam
              assembledVertices i k hk →
            k = 0)
    (hterminalNoLater :
      ∀ ⦃k l : ℕ⦄,
        (hk : k + 1 < (assembledVertices i).length) →
        (hl : l + 1 < (assembledVertices i).length) →
        k < l →
          endpointUnitDiskAssembly_terminalRole b centerParams localArcAtParam
              assembledVertices i k hk →
            False)
    (hinter_of_forall_eq_right :
      (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        p ∈ segment ℝ (assembledVertices i)[m] (assembledVertices i)[m + 1] →
        p ∈ segment ℝ (assembledVertices i)[n] (assembledVertices i)[n + 1] →
          p = (assembledVertices i)[m + 1]) →
      (segment ℝ (assembledVertices i)[m] (assembledVertices i)[m + 1] ∩
          segment ℝ (assembledVertices i)[n] (assembledVertices i)[n + 1]) =
        if n = m + 1 then {(assembledVertices i)[n]} else ∅)
    (hattach_pairwise_lt :
      (centerParams i).attach.Pairwise
        (fun t1 t2 : {t : ℝ // t ∈ centerParams i} => t1.1 < t2.1))
    (hbridge_m :
      endpointUnitDiskAssembly_bridgeRole centerParams localArcAtParam
        assembledVertices i m hm)
    (hroles_n :
      endpointUnitDiskAssembly_nonemptyRole a b centerParams localArcAtParam
        assembledVertices i n hn) :
    (segment ℝ (assembledVertices i)[m] (assembledVertices i)[m + 1] ∩
        segment ℝ (assembledVertices i)[n] (assembledVertices i)[n + 1]) =
      if n = m + 1 then {(assembledVertices i)[n]} else ∅ := by
  rcases hroles_n with hinitial_n | hroles_n
  · exact endpointUnitDiskAssembly_segments_bridge_initial
      a b T r centerParams centerOfParam hcenterOfParam_def
        localArcAtParam entryPoint exitPoint orderedLocalVertexBlocks
        assembledVertices horderedLocalVertexBlocks_def hassembledVertices_def
        hendpoint_ne hcenterParams_sorted hcenterOfParam_T
        hlocalArcAtParam_props hentryExitParameters horderedCutSeparation
        hchordGapLocalCarrierPosition hinitialGapMeetsLocalCarrierOnly
        hterminalGapMeetsLocalCarrierOnly
        horderedOutsideGapMeetsNeighboringLocalCarriersOnly hdisjoint
        hassembledVertices_nodup hassembledVertices_avoid
        hassembledEdgeEndpointRoles hlineSegmentInterSeparated i hm hn hmn
        hinitialIndexZero hterminalNoLater hinter_of_forall_eq_right
        hattach_pairwise_lt hbridge_m hinitial_n
  · rcases hroles_n with hlocal_n | hroles_n
    · exact endpointUnitDiskAssembly_segments_bridge_local
        a b T r centerParams centerOfParam hcenterOfParam_def
        localArcAtParam entryPoint exitPoint orderedLocalVertexBlocks
        assembledVertices horderedLocalVertexBlocks_def hassembledVertices_def
        hendpoint_ne hcenterParams_sorted hcenterOfParam_T
        hlocalArcAtParam_props hentryExitParameters horderedCutSeparation
        hchordGapLocalCarrierPosition hinitialGapMeetsLocalCarrierOnly
        hterminalGapMeetsLocalCarrierOnly
        horderedOutsideGapMeetsNeighboringLocalCarriersOnly hdisjoint
        hassembledVertices_nodup hassembledVertices_avoid
        hassembledEdgeEndpointRoles hlineSegmentInterSeparated i hm hn hmn
        hinitialIndexZero hterminalNoLater hinter_of_forall_eq_right
        hattach_pairwise_lt hbridge_m hlocal_n
    · rcases hroles_n with hbridge_n | hterminal_n
      · exact endpointUnitDiskAssembly_segments_bridge_bridge
          a b T r centerParams centerOfParam hcenterOfParam_def
          localArcAtParam entryPoint exitPoint orderedLocalVertexBlocks
          assembledVertices horderedLocalVertexBlocks_def hassembledVertices_def
          hendpoint_ne hcenterParams_sorted hcenterOfParam_T
          hlocalArcAtParam_props hentryExitParameters horderedCutSeparation
          hchordGapLocalCarrierPosition hinitialGapMeetsLocalCarrierOnly
          hterminalGapMeetsLocalCarrierOnly
          horderedOutsideGapMeetsNeighboringLocalCarriersOnly hdisjoint
          hassembledVertices_nodup hassembledVertices_avoid
          hassembledEdgeEndpointRoles hlineSegmentInterSeparated i hm hn hmn
          hinitialIndexZero hterminalNoLater hinter_of_forall_eq_right
          hattach_pairwise_lt hbridge_m hbridge_n
      · exact endpointUnitDiskAssembly_segments_bridge_terminal
          a b T r centerParams centerOfParam hcenterOfParam_def
          localArcAtParam entryPoint exitPoint orderedLocalVertexBlocks
          assembledVertices horderedLocalVertexBlocks_def hassembledVertices_def
          hendpoint_ne hcenterParams_sorted hcenterOfParam_T
          hlocalArcAtParam_props hentryExitParameters horderedCutSeparation
          hchordGapLocalCarrierPosition hinitialGapMeetsLocalCarrierOnly
          hterminalGapMeetsLocalCarrierOnly
          horderedOutsideGapMeetsNeighboringLocalCarriersOnly hdisjoint
          hassembledVertices_nodup hassembledVertices_avoid
          hassembledEdgeEndpointRoles hlineSegmentInterSeparated i hm hn hmn
          hinitialIndexZero hterminalNoLater hinter_of_forall_eq_right
          hattach_pairwise_lt hbridge_m hterminal_n

private lemma endpointUnitDiskAssembly_segments_terminal
    {ι : Type*} [Fintype ι]
    (a b : ι → EuclideanSpace ℝ (Fin 2))
    (T : Finset (EuclideanSpace ℝ (Fin 2)))
    (r : EuclideanSpace ℝ (Fin 2) → ℝ)
    (centerParams : ι → List ℝ)
    (centerOfParam :
      ∀ i, {t : ℝ // t ∈ centerParams i} → EuclideanSpace ℝ (Fin 2))
    (hcenterOfParam_def :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}),
        centerOfParam i t = AffineMap.lineMap (a i) (b i) t.1)
    (localArcAtParam :
      ∀ i, {t : ℝ // t ∈ centerParams i} → PolygonalArc)
    (entryPoint exitPoint :
      ∀ i, {t : ℝ // t ∈ centerParams i} → EuclideanSpace ℝ (Fin 2))
    (orderedLocalVertexBlocks :
      ∀ i, List (List (EuclideanSpace ℝ (Fin 2))))
    (assembledVertices : ι → List (EuclideanSpace ℝ (Fin 2)))
    (horderedLocalVertexBlocks_def : ∀ i,
      orderedLocalVertexBlocks i =
        (centerParams i).attach.map
          (fun t => (localArcAtParam i t).vertices))
    (hassembledVertices_def : ∀ i,
      assembledVertices i =
        EndpointUnitDiskAlternatingVertexList
          (a i) (b i) (orderedLocalVertexBlocks i))
    (hendpoint_ne : ∀ i, a i ≠ b i)
    (hcenterParams_sorted : ∀ i, (centerParams i).SortedLT)
    (hcenterOfParam_T :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}), centerOfParam i t ∈ T)
    (hlocalArcAtParam_props :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}),
        (localArcAtParam i t).source = entryPoint i t ∧
          (localArcAtParam i t).target = exitPoint i t ∧
            (localArcAtParam i t).carrier ⊆
              Metric.closedBall (centerOfParam i t) (r (centerOfParam i t)) ∧
              (localArcAtParam i t).relativeInterior ⊆
                Metric.ball (centerOfParam i t) (r (centerOfParam i t)))
    (hentryExitParameters :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}),
        (∃ s : ℝ, 0 < s ∧ s < t.1 ∧
          entryPoint i t = AffineMap.lineMap (a i) (b i) s) ∧
          (∃ s : ℝ, t.1 < s ∧ s < 1 ∧
            exitPoint i t = AffineMap.lineMap (a i) (b i) s))
    (horderedCutSeparation :
      ∀ i (t1 t2 : {t : ℝ // t ∈ centerParams i}),
        t1.1 < t2.1 →
          ∃ sExit sEntry : ℝ,
            t1.1 < sExit ∧
              sExit < sEntry ∧
                sEntry < t2.1 ∧
                  exitPoint i t1 = AffineMap.lineMap (a i) (b i) sExit ∧
                    entryPoint i t2 = AffineMap.lineMap (a i) (b i) sEntry)
    (hchordGapLocalCarrierPosition :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}) {α β e x : ℝ},
        entryPoint i t = AffineMap.lineMap (a i) (b i) e →
          exitPoint i t = AffineMap.lineMap (a i) (b i) x →
            0 ≤ α → α ≤ β → β ≤ 1 → e < x →
              (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
                p ∈ segment ℝ (AffineMap.lineMap (a i) (b i) α)
                    (AffineMap.lineMap (a i) (b i) β) →
                  p ∈ (localArcAtParam i t).carrier →
                    β < e → False) ∧
                (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
                  p ∈ segment ℝ (AffineMap.lineMap (a i) (b i) α)
                      (AffineMap.lineMap (a i) (b i) β) →
                    p ∈ (localArcAtParam i t).carrier →
                      β = e → p = entryPoint i t) ∧
                  (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
                    p ∈ segment ℝ (AffineMap.lineMap (a i) (b i) α)
                        (AffineMap.lineMap (a i) (b i) β) →
                      p ∈ (localArcAtParam i t).carrier →
                        x < α → False) ∧
                    (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
                      p ∈ segment ℝ (AffineMap.lineMap (a i) (b i) α)
                          (AffineMap.lineMap (a i) (b i) β) →
                        p ∈ (localArcAtParam i t).carrier →
                          x = α → p = exitPoint i t))
    (hinitialGapMeetsLocalCarrierOnly :
      ∀ i (t : {t : ℝ // t ∈ centerParams i})
        ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        p ∈ segment ℝ (a i) (entryPoint i t) →
          p ∈ (localArcAtParam i t).carrier → p = entryPoint i t)
    (hterminalGapMeetsLocalCarrierOnly :
      ∀ i (t : {t : ℝ // t ∈ centerParams i})
        ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        p ∈ segment ℝ (exitPoint i t) (b i) →
          p ∈ (localArcAtParam i t).carrier → p = exitPoint i t)
    (horderedOutsideGapMeetsNeighboringLocalCarriersOnly :
      ∀ i (t1 t2 : {t : ℝ // t ∈ centerParams i}),
        t1.1 < t2.1 →
          (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
            p ∈ segment ℝ (exitPoint i t1) (entryPoint i t2) →
              p ∈ (localArcAtParam i t1).carrier → p = exitPoint i t1) ∧
            (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
              p ∈ segment ℝ (exitPoint i t1) (entryPoint i t2) →
                p ∈ (localArcAtParam i t2).carrier → p = entryPoint i t2))
    (hdisjoint : ∀ ⦃z w : EuclideanSpace ℝ (Fin 2)⦄,
      z ∈ T → w ∈ T → z ≠ w →
        Disjoint (Metric.closedBall z (r z)) (Metric.closedBall w (r w)))
    (hassembledVertices_nodup : ∀ i, (assembledVertices i).Nodup)
    (hassembledVertices_avoid :
      ∀ i ⦃m k : ℕ⦄,
        (hm : m + 1 < (assembledVertices i).length) →
          (hk : k < (assembledVertices i).length) →
            k ≠ m → k ≠ m + 1 →
              (assembledVertices i)[k] ∉
                openSegment ℝ
                  (assembledVertices i)[m] (assembledVertices i)[m + 1])
    (hassembledEdgeEndpointRoles :
      ∀ i ⦃m : ℕ⦄,
        (hm : m + 1 < (assembledVertices i).length) →
          ((centerParams i).attach = [] ∧
              (assembledVertices i)[m] = a i ∧
                (assembledVertices i)[m + 1] = b i) ∨
            (∃ t ts X,
              (centerParams i).attach = t :: ts ∧
                (localArcAtParam i t).vertices.head? = some X ∧
                  (assembledVertices i)[m] = a i ∧
                    (assembledVertices i)[m + 1] = X) ∨
            (∃ (pre : List {t : ℝ // t ∈ centerParams i})
                (t : {t : ℝ // t ∈ centerParams i})
                (post : List {t : ℝ // t ∈ centerParams i}) (q : ℕ),
              ∃ hq : q + 1 < (localArcAtParam i t).vertices.length,
                (centerParams i).attach = pre ++ t :: post ∧
                  (assembledVertices i)[m] =
                    (localArcAtParam i t).vertices[q] ∧
                    (assembledVertices i)[m + 1] =
                      (localArcAtParam i t).vertices[q + 1]) ∨
            (∃ (pre : List {t : ℝ // t ∈ centerParams i})
                (t1 : {t : ℝ // t ∈ centerParams i})
                (t2 : {t : ℝ // t ∈ centerParams i})
                (post : List {t : ℝ // t ∈ centerParams i})
                (X Y : EuclideanSpace ℝ (Fin 2)),
              (centerParams i).attach = pre ++ t1 :: t2 :: post ∧
                (localArcAtParam i t1).vertices.getLast? = some X ∧
                  (localArcAtParam i t2).vertices.head? = some Y ∧
                    (assembledVertices i)[m] = X ∧
                      (assembledVertices i)[m + 1] = Y) ∨
            (∃ (pre : List {t : ℝ // t ∈ centerParams i})
                (t : {t : ℝ // t ∈ centerParams i})
                (X : EuclideanSpace ℝ (Fin 2)),
              (centerParams i).attach = pre ++ [t] ∧
                (localArcAtParam i t).vertices.getLast? = some X ∧
                  (assembledVertices i)[m] = X ∧
                    (assembledVertices i)[m + 1] = b i))
    (hlineSegmentInterSeparated :
      ∀ i {α β γ δ : ℝ}, α ≤ β → γ ≤ δ → β < γ →
        segment ℝ (AffineMap.lineMap (a i) (b i) α)
            (AffineMap.lineMap (a i) (b i) β) ∩
          segment ℝ (AffineMap.lineMap (a i) (b i) γ)
            (AffineMap.lineMap (a i) (b i) δ) =
        (∅ : Set (EuclideanSpace ℝ (Fin 2))))
    (i : ι) {m n : ℕ}
    (hm : m + 1 < (assembledVertices i).length)
    (hn : n + 1 < (assembledVertices i).length)
    (hmn : m < n)
    (hinitialIndexZero :
      ∀ ⦃k : ℕ⦄,
        (hk : k + 1 < (assembledVertices i).length) →
          endpointUnitDiskAssembly_initialRole a centerParams localArcAtParam
              assembledVertices i k hk →
            k = 0)
    (hterminalNoLater :
      ∀ ⦃k l : ℕ⦄,
        (hk : k + 1 < (assembledVertices i).length) →
        (hl : l + 1 < (assembledVertices i).length) →
        k < l →
          endpointUnitDiskAssembly_terminalRole b centerParams localArcAtParam
              assembledVertices i k hk →
            False)
    (hinter_of_forall_eq_right :
      (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        p ∈ segment ℝ (assembledVertices i)[m] (assembledVertices i)[m + 1] →
        p ∈ segment ℝ (assembledVertices i)[n] (assembledVertices i)[n + 1] →
          p = (assembledVertices i)[m + 1]) →
      (segment ℝ (assembledVertices i)[m] (assembledVertices i)[m + 1] ∩
          segment ℝ (assembledVertices i)[n] (assembledVertices i)[n + 1]) =
        if n = m + 1 then {(assembledVertices i)[n]} else ∅)
    (hattach_pairwise_lt :
      (centerParams i).attach.Pairwise
        (fun t1 t2 : {t : ℝ // t ∈ centerParams i} => t1.1 < t2.1))
    (hterminal_m :
      endpointUnitDiskAssembly_terminalRole b centerParams localArcAtParam
        assembledVertices i m hm) :
    (segment ℝ (assembledVertices i)[m] (assembledVertices i)[m + 1] ∩
        segment ℝ (assembledVertices i)[n] (assembledVertices i)[n + 1]) =
      if n = m + 1 then {(assembledVertices i)[n]} else ∅ := by
  exact False.elim (hterminalNoLater hm hn hmn hterminal_m)

private lemma endpointUnitDiskAssembly_segments
    {ι : Type*} [Fintype ι]
    (a b : ι → EuclideanSpace ℝ (Fin 2))
    (T : Finset (EuclideanSpace ℝ (Fin 2)))
    (r : EuclideanSpace ℝ (Fin 2) → ℝ)
    (centerParams : ι → List ℝ)
    (centerOfParam :
      ∀ i, {t : ℝ // t ∈ centerParams i} → EuclideanSpace ℝ (Fin 2))
    (hcenterOfParam_def :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}),
        centerOfParam i t = AffineMap.lineMap (a i) (b i) t.1)
    (localArcAtParam :
      ∀ i, {t : ℝ // t ∈ centerParams i} → PolygonalArc)
    (entryPoint exitPoint :
      ∀ i, {t : ℝ // t ∈ centerParams i} → EuclideanSpace ℝ (Fin 2))
    (orderedLocalVertexBlocks :
      ∀ i, List (List (EuclideanSpace ℝ (Fin 2))))
    (assembledVertices : ι → List (EuclideanSpace ℝ (Fin 2)))
    (horderedLocalVertexBlocks_def : ∀ i,
      orderedLocalVertexBlocks i =
        (centerParams i).attach.map
          (fun t => (localArcAtParam i t).vertices))
    (hassembledVertices_def : ∀ i,
      assembledVertices i =
        EndpointUnitDiskAlternatingVertexList
          (a i) (b i) (orderedLocalVertexBlocks i))
    (hendpoint_ne : ∀ i, a i ≠ b i)
    (hcenterParams_sorted : ∀ i, (centerParams i).SortedLT)
    (hcenterOfParam_T :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}), centerOfParam i t ∈ T)
    (hlocalArcAtParam_props :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}),
        (localArcAtParam i t).source = entryPoint i t ∧
          (localArcAtParam i t).target = exitPoint i t ∧
            (localArcAtParam i t).carrier ⊆
              Metric.closedBall (centerOfParam i t) (r (centerOfParam i t)) ∧
              (localArcAtParam i t).relativeInterior ⊆
                Metric.ball (centerOfParam i t) (r (centerOfParam i t)))
    (hentryExitParameters :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}),
        (∃ s : ℝ, 0 < s ∧ s < t.1 ∧
          entryPoint i t = AffineMap.lineMap (a i) (b i) s) ∧
          (∃ s : ℝ, t.1 < s ∧ s < 1 ∧
            exitPoint i t = AffineMap.lineMap (a i) (b i) s))
    (horderedCutSeparation :
      ∀ i (t1 t2 : {t : ℝ // t ∈ centerParams i}),
        t1.1 < t2.1 →
          ∃ sExit sEntry : ℝ,
            t1.1 < sExit ∧
              sExit < sEntry ∧
                sEntry < t2.1 ∧
                  exitPoint i t1 = AffineMap.lineMap (a i) (b i) sExit ∧
                    entryPoint i t2 = AffineMap.lineMap (a i) (b i) sEntry)
    (hchordGapLocalCarrierPosition :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}) {α β e x : ℝ},
        entryPoint i t = AffineMap.lineMap (a i) (b i) e →
          exitPoint i t = AffineMap.lineMap (a i) (b i) x →
            0 ≤ α → α ≤ β → β ≤ 1 → e < x →
              (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
                p ∈ segment ℝ (AffineMap.lineMap (a i) (b i) α)
                    (AffineMap.lineMap (a i) (b i) β) →
                  p ∈ (localArcAtParam i t).carrier →
                    β < e → False) ∧
                (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
                  p ∈ segment ℝ (AffineMap.lineMap (a i) (b i) α)
                      (AffineMap.lineMap (a i) (b i) β) →
                    p ∈ (localArcAtParam i t).carrier →
                      β = e → p = entryPoint i t) ∧
                  (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
                    p ∈ segment ℝ (AffineMap.lineMap (a i) (b i) α)
                        (AffineMap.lineMap (a i) (b i) β) →
                      p ∈ (localArcAtParam i t).carrier →
                        x < α → False) ∧
                    (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
                      p ∈ segment ℝ (AffineMap.lineMap (a i) (b i) α)
                          (AffineMap.lineMap (a i) (b i) β) →
                        p ∈ (localArcAtParam i t).carrier →
                          x = α → p = exitPoint i t))
    (hinitialGapMeetsLocalCarrierOnly :
      ∀ i (t : {t : ℝ // t ∈ centerParams i})
        ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        p ∈ segment ℝ (a i) (entryPoint i t) →
          p ∈ (localArcAtParam i t).carrier → p = entryPoint i t)
    (hterminalGapMeetsLocalCarrierOnly :
      ∀ i (t : {t : ℝ // t ∈ centerParams i})
        ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        p ∈ segment ℝ (exitPoint i t) (b i) →
          p ∈ (localArcAtParam i t).carrier → p = exitPoint i t)
    (horderedOutsideGapMeetsNeighboringLocalCarriersOnly :
      ∀ i (t1 t2 : {t : ℝ // t ∈ centerParams i}),
        t1.1 < t2.1 →
          (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
            p ∈ segment ℝ (exitPoint i t1) (entryPoint i t2) →
              p ∈ (localArcAtParam i t1).carrier → p = exitPoint i t1) ∧
            (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
              p ∈ segment ℝ (exitPoint i t1) (entryPoint i t2) →
                p ∈ (localArcAtParam i t2).carrier → p = entryPoint i t2))
    (hdisjoint : ∀ ⦃z w : EuclideanSpace ℝ (Fin 2)⦄,
      z ∈ T → w ∈ T → z ≠ w →
        Disjoint (Metric.closedBall z (r z)) (Metric.closedBall w (r w)))
    (hassembledVertices_nodup : ∀ i, (assembledVertices i).Nodup)
    (hassembledVertices_avoid :
      ∀ i ⦃m k : ℕ⦄,
        (hm : m + 1 < (assembledVertices i).length) →
          (hk : k < (assembledVertices i).length) →
            k ≠ m → k ≠ m + 1 →
              (assembledVertices i)[k] ∉
                openSegment ℝ
                  (assembledVertices i)[m] (assembledVertices i)[m + 1])
    (hassembledEdgeEndpointRoles :
      ∀ i ⦃m : ℕ⦄,
        (hm : m + 1 < (assembledVertices i).length) →
          ((centerParams i).attach = [] ∧
              (assembledVertices i)[m] = a i ∧
                (assembledVertices i)[m + 1] = b i) ∨
            (∃ t ts X,
              (centerParams i).attach = t :: ts ∧
                (localArcAtParam i t).vertices.head? = some X ∧
                  (assembledVertices i)[m] = a i ∧
                    (assembledVertices i)[m + 1] = X) ∨
            (∃ (pre : List {t : ℝ // t ∈ centerParams i})
                (t : {t : ℝ // t ∈ centerParams i})
                (post : List {t : ℝ // t ∈ centerParams i}) (q : ℕ),
              ∃ hq : q + 1 < (localArcAtParam i t).vertices.length,
                (centerParams i).attach = pre ++ t :: post ∧
                  (assembledVertices i)[m] =
                    (localArcAtParam i t).vertices[q] ∧
                    (assembledVertices i)[m + 1] =
                      (localArcAtParam i t).vertices[q + 1]) ∨
            (∃ (pre : List {t : ℝ // t ∈ centerParams i})
                (t1 : {t : ℝ // t ∈ centerParams i})
                (t2 : {t : ℝ // t ∈ centerParams i})
                (post : List {t : ℝ // t ∈ centerParams i})
                (X Y : EuclideanSpace ℝ (Fin 2)),
              (centerParams i).attach = pre ++ t1 :: t2 :: post ∧
                (localArcAtParam i t1).vertices.getLast? = some X ∧
                  (localArcAtParam i t2).vertices.head? = some Y ∧
                    (assembledVertices i)[m] = X ∧
                      (assembledVertices i)[m + 1] = Y) ∨
            (∃ (pre : List {t : ℝ // t ∈ centerParams i})
                (t : {t : ℝ // t ∈ centerParams i})
                (X : EuclideanSpace ℝ (Fin 2)),
              (centerParams i).attach = pre ++ [t] ∧
                (localArcAtParam i t).vertices.getLast? = some X ∧
                  (assembledVertices i)[m] = X ∧
                    (assembledVertices i)[m + 1] = b i))
    (hlineSegmentInterSeparated :
      ∀ i {α β γ δ : ℝ}, α ≤ β → γ ≤ δ → β < γ →
        segment ℝ (AffineMap.lineMap (a i) (b i) α)
            (AffineMap.lineMap (a i) (b i) β) ∩
          segment ℝ (AffineMap.lineMap (a i) (b i) γ)
            (AffineMap.lineMap (a i) (b i) δ) =
        (∅ : Set (EuclideanSpace ℝ (Fin 2)))) :
    ∀ i ⦃m n : ℕ⦄,
      (hm : m + 1 < (assembledVertices i).length) →
      (hn : n + 1 < (assembledVertices i).length) →
      m < n →
      (segment ℝ (assembledVertices i)[m] (assembledVertices i)[m + 1] ∩
          segment ℝ (assembledVertices i)[n] (assembledVertices i)[n + 1]) =
        if n = m + 1 then {(assembledVertices i)[n]} else ∅ := by
  intro i m n hm hn hmn
  have hinitialIndexZero :
      ∀ ⦃k : ℕ⦄,
        (hk : k + 1 < (assembledVertices i).length) →
        (∃ t ts X,
          (centerParams i).attach = t :: ts ∧
            (localArcAtParam i t).vertices.head? = some X ∧
              (assembledVertices i)[k] = a i ∧
                (assembledVertices i)[k + 1] = X) →
          k = 0 := by
    intro k hk hinit
    rcases hinit with ⟨t, ts, X, _hitems, _hhead, hleft, _hright⟩
    have hk_lt : k < (assembledVertices i).length :=
      Nat.lt_trans (Nat.lt_succ_self k) hk
    have hzero_lt : 0 < (assembledVertices i).length := by omega
    have hzero : (assembledVertices i)[0] = a i := by
      have hzero_opt : (assembledVertices i)[0]? = some (a i) := by
        rw [hassembledVertices_def i]
        simp [EndpointUnitDiskAlternatingVertexList]
      rw [List.getElem?_eq_getElem hzero_lt] at hzero_opt
      exact Option.some.inj hzero_opt
    have hval : (assembledVertices i)[k] = (assembledVertices i)[0] := by
      rw [hleft, hzero]
    exact ((hassembledVertices_nodup i).getElem_inj_iff).1 hval
  have hterminalNoLater :
      ∀ ⦃k l : ℕ⦄,
        (hk : k + 1 < (assembledVertices i).length) →
        (hl : l + 1 < (assembledVertices i).length) →
        k < l →
        (∃ pre t X,
          (centerParams i).attach = pre ++ [t] ∧
            (localArcAtParam i t).vertices.getLast? = some X ∧
              (assembledVertices i)[k] = X ∧
                (assembledVertices i)[k + 1] = b i) →
        False := by
    intro k l hk hl hkl hterminal
    rcases hterminal with ⟨pre, t, X, _hitems, _hlast, _hleft, hright⟩
    have hlast : (assembledVertices i).getLast? = some (b i) := by
      rw [show assembledVertices i =
          [a i] ++ ((orderedLocalVertexBlocks i).flatten ++ [b i]) by
        rw [hassembledVertices_def i]
        simp [EndpointUnitDiskAlternatingVertexList]]
      rw [List.getLast?_append_of_ne_nil [a i] (by simp :
        (orderedLocalVertexBlocks i).flatten ++ [b i] ≠ [])]
      simp
    have hlast_index :
        (assembledVertices i).length - 1 < (assembledVertices i).length := by
      omega
    have hlast_get :
        (assembledVertices i).getLast? =
          some ((assembledVertices i)[(assembledVertices i).length - 1]) := by
      rw [List.getLast?_eq_getElem?]
      rw [List.getElem?_eq_getElem hlast_index]
    have hlast_value :
        (assembledVertices i)[(assembledVertices i).length - 1] = b i :=
      Option.some.inj (hlast_get.symm.trans hlast)
    have hk1_last : k + 1 = (assembledVertices i).length - 1 := by
      have hval :
          (assembledVertices i)[k + 1] =
            (assembledVertices i)[(assembledVertices i).length - 1] := by
        rw [hright, hlast_value]
      exact ((hassembledVertices_nodup i).getElem_inj_iff).1 hval
    omega
  have hinter_of_forall_eq_right :
      (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        p ∈ segment ℝ (assembledVertices i)[m] (assembledVertices i)[m + 1] →
        p ∈ segment ℝ (assembledVertices i)[n] (assembledVertices i)[n + 1] →
          p = (assembledVertices i)[m + 1]) →
      (segment ℝ (assembledVertices i)[m] (assembledVertices i)[m + 1] ∩
          segment ℝ (assembledVertices i)[n] (assembledVertices i)[n + 1]) =
        if n = m + 1 then {(assembledVertices i)[n]} else ∅ := by
    intro hpoint
    by_cases hAdj : n = m + 1
    · subst n
      ext p
      constructor
      · intro hp
        have hp_eq := hpoint hp.1 hp.2
        simp [hp_eq]
      · intro hp
        have hp_eq : p = (assembledVertices i)[m + 1] := by
          simpa using hp
        subst p
        exact ⟨right_mem_segment ℝ (assembledVertices i)[m]
            (assembledVertices i)[m + 1],
          left_mem_segment ℝ (assembledVertices i)[m + 1]
            (assembledVertices i)[m + 1 + 1]⟩
    · ext p
      constructor
      · intro hp
        exfalso
        have hp_eq := hpoint hp.1 hp.2
        have hk : m + 1 < (assembledVertices i).length := hm
        have hn_lt : n < (assembledVertices i).length :=
          Nat.lt_trans (Nat.lt_succ_self n) hn
        have hleft_ne :
            (assembledVertices i)[n] ≠ (assembledVertices i)[m + 1] := by
          intro hEq
          have hidx := ((hassembledVertices_nodup i).getElem_inj_iff).1 hEq
          omega
        have hright_ne :
            (assembledVertices i)[n + 1] ≠ (assembledVertices i)[m + 1] := by
          intro hEq
          have hidx := ((hassembledVertices_nodup i).getElem_inj_iff).1 hEq
          omega
        have hpseg :
            (assembledVertices i)[m + 1] ∈
              segment ℝ (assembledVertices i)[n] (assembledVertices i)[n + 1] := by
          simpa [hp_eq] using hp.2
        have hpopen :
            (assembledVertices i)[m + 1] ∈
              openSegment ℝ (assembledVertices i)[n] (assembledVertices i)[n + 1] :=
          mem_openSegment_of_ne_left_right (𝕜 := ℝ)
            hleft_ne hright_ne hpseg
        exact hassembledVertices_avoid i hn hk (by omega) (by omega) hpopen
      · intro hp
        simp [hAdj] at hp
  have hattach_pairwise_lt :
      (centerParams i).attach.Pairwise
        (fun t1 t2 : {t : ℝ // t ∈ centerParams i} => t1.1 < t2.1) := by
    have hmap :
        ((centerParams i).attach.map
            (fun t : {t : ℝ // t ∈ centerParams i} => t.1)).Pairwise
          (fun x y : ℝ => x < y) := by
      simpa [List.attach_map_subtype_val] using
        (List.sortedLT_iff_pairwise.mp (hcenterParams_sorted i))
    rw [List.pairwise_map] at hmap
    exact hmap
  rcases hassembledEdgeEndpointRoles i hm with hnodisks | hroles
  · rcases hnodisks with ⟨hitems, _hleft, _hright⟩
    have hn_impossible : False := by
      have hn' : n + 1 < 2 := by
        rw [hassembledVertices_def i, horderedLocalVertexBlocks_def i] at hn
        simpa [EndpointUnitDiskAlternatingVertexList, hitems] using hn
      omega
    exact False.elim hn_impossible
  rcases hassembledEdgeEndpointRoles i hn with hnodisks_n | hroles_n
  · rcases hnodisks_n with ⟨hitems_n, _hleft_n, _hright_n⟩
    rcases hroles with hinitial | hroles
    · rcases hinitial with ⟨t, ts, X, hitems_m, _hhead_m, _hleft_m, _hright_m⟩
      simp [hitems_n] at hitems_m
    · rcases hroles with hlocal | hroles
      · rcases hlocal with
          ⟨pre, t, post, q, hq, hitems_m, _hleft_m, _hright_m⟩
        simp [hitems_n] at hitems_m
      · rcases hroles with hbridge | hterminal
        · rcases hbridge with
            ⟨pre, t1, t2, post, X, Y, hitems_m, _hlast_m,
              _hhead_m, _hleft_m, _hright_m⟩
          simp [hitems_n] at hitems_m
        · rcases hterminal with
            ⟨pre, t, X, hitems_m, _hlast_m, _hleft_m, _hright_m⟩
          simp [hitems_n] at hitems_m
  rcases hroles with hinitial_m | hroles_m
  · exact endpointUnitDiskAssembly_segments_initial
      a b T r centerParams centerOfParam hcenterOfParam_def
        localArcAtParam entryPoint exitPoint orderedLocalVertexBlocks
        assembledVertices horderedLocalVertexBlocks_def hassembledVertices_def
        hendpoint_ne hcenterParams_sorted hcenterOfParam_T
        hlocalArcAtParam_props hentryExitParameters horderedCutSeparation
        hchordGapLocalCarrierPosition hinitialGapMeetsLocalCarrierOnly
        hterminalGapMeetsLocalCarrierOnly
        horderedOutsideGapMeetsNeighboringLocalCarriersOnly hdisjoint
        hassembledVertices_nodup hassembledVertices_avoid
        hassembledEdgeEndpointRoles hlineSegmentInterSeparated i hm hn hmn
        hinitialIndexZero hterminalNoLater hinter_of_forall_eq_right
        hattach_pairwise_lt hinitial_m hroles_n
  · rcases hroles_m with hlocal_m | hroles_m
    · exact endpointUnitDiskAssembly_segments_local
        a b T r centerParams centerOfParam hcenterOfParam_def
        localArcAtParam entryPoint exitPoint orderedLocalVertexBlocks
        assembledVertices horderedLocalVertexBlocks_def hassembledVertices_def
        hendpoint_ne hcenterParams_sorted hcenterOfParam_T
        hlocalArcAtParam_props hentryExitParameters horderedCutSeparation
        hchordGapLocalCarrierPosition hinitialGapMeetsLocalCarrierOnly
        hterminalGapMeetsLocalCarrierOnly
        horderedOutsideGapMeetsNeighboringLocalCarriersOnly hdisjoint
        hassembledVertices_nodup hassembledVertices_avoid
        hassembledEdgeEndpointRoles hlineSegmentInterSeparated i hm hn hmn
        hinitialIndexZero hterminalNoLater hinter_of_forall_eq_right
        hattach_pairwise_lt hlocal_m hroles_n
    · rcases hroles_m with hbridge_m | hterminal_m
      · exact endpointUnitDiskAssembly_segments_bridge
          a b T r centerParams centerOfParam hcenterOfParam_def
          localArcAtParam entryPoint exitPoint orderedLocalVertexBlocks
          assembledVertices horderedLocalVertexBlocks_def hassembledVertices_def
          hendpoint_ne hcenterParams_sorted hcenterOfParam_T
          hlocalArcAtParam_props hentryExitParameters horderedCutSeparation
          hchordGapLocalCarrierPosition hinitialGapMeetsLocalCarrierOnly
          hterminalGapMeetsLocalCarrierOnly
          horderedOutsideGapMeetsNeighboringLocalCarriersOnly hdisjoint
          hassembledVertices_nodup hassembledVertices_avoid
          hassembledEdgeEndpointRoles hlineSegmentInterSeparated i hm hn hmn
          hinitialIndexZero hterminalNoLater hinter_of_forall_eq_right
          hattach_pairwise_lt hbridge_m hroles_n
      · exact endpointUnitDiskAssembly_segments_terminal
          a b T r centerParams centerOfParam hcenterOfParam_def
          localArcAtParam entryPoint exitPoint orderedLocalVertexBlocks
          assembledVertices horderedLocalVertexBlocks_def hassembledVertices_def
          hendpoint_ne hcenterParams_sorted hcenterOfParam_T
          hlocalArcAtParam_props hentryExitParameters horderedCutSeparation
          hchordGapLocalCarrierPosition hinitialGapMeetsLocalCarrierOnly
          hterminalGapMeetsLocalCarrierOnly
          horderedOutsideGapMeetsNeighboringLocalCarriersOnly hdisjoint
          hassembledVertices_nodup hassembledVertices_avoid
          hassembledEdgeEndpointRoles hlineSegmentInterSeparated i hm hn hmn
          hinitialIndexZero hterminalNoLater hinter_of_forall_eq_right
          hattach_pairwise_lt hterminal_m

private abbrev endpointUnitDiskAssembly_center
    (T : Finset (EuclideanSpace ℝ (Fin 2))) :=
  {z : EuclideanSpace ℝ (Fin 2) // z ∈ T}

private abbrev endpointUnitDiskAssembly_incident
    {ι : Type*} (a b : ι → EuclideanSpace ℝ (Fin 2))
    (z : EuclideanSpace ℝ (Fin 2)) :=
  {i : ι // z ∈ openSegment ℝ (a i) (b i)}

private abbrev endpointUnitDiskAssembly_pointRole
    {ι : Type*}
    (a b : ι → EuclideanSpace ℝ (Fin 2))
    (T : Finset (EuclideanSpace ℝ (Fin 2)))
    (r : EuclideanSpace ℝ (Fin 2) → ℝ)
    (centerParams : ι → List ℝ)
    (centerOfParam :
      ∀ i, {t : ℝ // t ∈ centerParams i} → EuclideanSpace ℝ (Fin 2))
    (localArcAtParam :
      ∀ i, {t : ℝ // t ∈ centerParams i} → PolygonalArc)
    (entryPoint exitPoint :
      ∀ i, {t : ℝ // t ∈ centerParams i} → EuclideanSpace ℝ (Fin 2))
    (i : ι) (p : EuclideanSpace ℝ (Fin 2)) : Prop :=
  (p ∈ openSegment ℝ (a i) (b i) ∧
      ∀ z : EuclideanSpace ℝ (Fin 2),
        z ∈ T → p ∉ Metric.closedBall z (r z)) ∨
    (∃ t : {t : ℝ // t ∈ centerParams i},
      p ∈ (localArcAtParam i t).relativeInterior ∧
        p ∈ Metric.ball (centerOfParam i t) (r (centerOfParam i t))) ∨
      (∃ t : {t : ℝ // t ∈ centerParams i},
        (p = entryPoint i t ∧
            p ∈ Metric.sphere (centerOfParam i t) (r (centerOfParam i t)) ∧
              p ∈ openSegment ℝ (a i) (b i)) ∨
          (p = exitPoint i t ∧
            p ∈ Metric.sphere (centerOfParam i t) (r (centerOfParam i t)) ∧
              p ∈ openSegment ℝ (a i) (b i)))

private lemma endpointUnitDiskAssembly_splicePoint_not_other
    {ι : Type*} [Fintype ι]
    (a b : ι → EuclideanSpace ℝ (Fin 2))
    (T : Finset (EuclideanSpace ℝ (Fin 2)))
    (r : EuclideanSpace ℝ (Fin 2) → ℝ)
    (centerParams : ι → List ℝ)
    (centerOfParam :
      ∀ i, {t : ℝ // t ∈ centerParams i} → EuclideanSpace ℝ (Fin 2))
    (localArcAtParam :
      ∀ i, {t : ℝ // t ∈ centerParams i} → PolygonalArc)
    (entryPoint exitPoint :
      ∀ i, {t : ℝ // t ∈ centerParams i} → EuclideanSpace ℝ (Fin 2))
    (Gamma : ι → PolygonalArc)
    (hrpos : ∀ z ∈ T, 0 < r z)
    (hdisjoint : ∀ ⦃z w : EuclideanSpace ℝ (Fin 2)⦄,
      z ∈ T → w ∈ T → z ≠ w →
        Disjoint (Metric.closedBall z (r z)) (Metric.closedBall w (r w)))
    (hmiss : ∀ ⦃z : EuclideanSpace ℝ (Fin 2)⦄,
      z ∈ T → ∀ i,
        z ∉ segment ℝ (a i) (b i) →
          Disjoint (Metric.closedBall z (r z)) (segment ℝ (a i) (b i)))
    (hpairOnly : ∀ ⦃z y : EuclideanSpace ℝ (Fin 2)⦄,
      z ∈ T →
        y ∈ Metric.closedBall z (r z) →
          (∃ i j : ι,
            i ≠ j ∧
              y ∈ segment ℝ (a i) (b i) ∧
                y ∈ segment ℝ (a j) (b j)) →
            y = z)
    (hcenterOfParam_T :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}), centerOfParam i t ∈ T)
    (hfinalPointRoles :
      ∀ i ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        p ∈ (Gamma i).relativeInterior →
          endpointUnitDiskAssembly_pointRole a b T r centerParams
            centerOfParam localArcAtParam entryPoint exitPoint i p) :
    ∀ ⦃i j : ι⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄
        (t : {t : ℝ // t ∈ centerParams i}),
      i ≠ j →
        ((p = entryPoint i t ∧
            p ∈ Metric.sphere (centerOfParam i t) (r (centerOfParam i t)) ∧
              p ∈ openSegment ℝ (a i) (b i)) ∨
          (p = exitPoint i t ∧
            p ∈ Metric.sphere (centerOfParam i t) (r (centerOfParam i t)) ∧
              p ∈ openSegment ℝ (a i) (b i))) →
          p ∉ (Gamma j).relativeInterior := by
  intro i j p t hij hsplice hpj
  have hp_sphere_i :
      p ∈ Metric.sphere (centerOfParam i t) (r (centerOfParam i t)) := by
    rcases hsplice with hentry | hexit
    · exact hentry.2.1
    · exact hexit.2.1
  have hp_open_i : p ∈ openSegment ℝ (a i) (b i) := by
    rcases hsplice with hentry | hexit
    · exact hentry.2.2
    · exact hexit.2.2
  have hp_closed_i :
      p ∈ Metric.closedBall (centerOfParam i t) (r (centerOfParam i t)) := by
    rw [Metric.mem_closedBall]
    exact le_of_eq (by simpa [Metric.mem_sphere, dist_eq_norm] using hp_sphere_i)
  have hpseg_i : p ∈ segment ℝ (a i) (b i) :=
    openSegment_subset_segment ℝ (a i) (b i) hp_open_i
  rcases hfinalPointRoles j hpj with houtside_j | hlocal_or_splice_j
  · exact houtside_j.2 (centerOfParam i t) (hcenterOfParam_T i t) hp_closed_i
  rcases hlocal_or_splice_j with hlocal_j | hsplice_j
  · rcases hlocal_j with ⟨tj, _hp_rel_j, hp_ball_j⟩
    by_cases hcenter_eq : centerOfParam i t = centerOfParam j tj
    · have hp_ball_same :
          p ∈ Metric.ball (centerOfParam i t) (r (centerOfParam i t)) := by
        simpa [hcenter_eq] using hp_ball_j
      have hdist_lt :
          dist p (centerOfParam i t) < r (centerOfParam i t) := by
        simpa [Metric.mem_ball] using hp_ball_same
      have hdist_eq :
          dist p (centerOfParam i t) = r (centerOfParam i t) := by
        simpa [Metric.mem_sphere, dist_eq_norm] using hp_sphere_i
      linarith
    · have hp_closed_j :
          p ∈ Metric.closedBall (centerOfParam j tj) (r (centerOfParam j tj)) :=
        Metric.ball_subset_closedBall hp_ball_j
      have hdis :
          Disjoint
            (Metric.closedBall (centerOfParam i t) (r (centerOfParam i t)))
            (Metric.closedBall (centerOfParam j tj) (r (centerOfParam j tj))) :=
        hdisjoint (hcenterOfParam_T i t) (hcenterOfParam_T j tj) hcenter_eq
      exact (Set.disjoint_left.mp hdis) hp_closed_i hp_closed_j
  · rcases hsplice_j with ⟨tj, hsplice_j⟩
    have hp_open_j : p ∈ openSegment ℝ (a j) (b j) := by
      rcases hsplice_j with hentry_j | hexit_j
      · exact hentry_j.2.2
      · exact hexit_j.2.2
    have hpseg_j : p ∈ segment ℝ (a j) (b j) :=
      openSegment_subset_segment ℝ (a j) (b j) hp_open_j
    by_cases hcenter_on_j :
        centerOfParam i t ∈ segment ℝ (a j) (b j)
    · have hp_center :
          p = centerOfParam i t :=
        hpairOnly (hcenterOfParam_T i t) hp_closed_i
          ⟨i, j, hij, hpseg_i, hpseg_j⟩
      have hdist_zero : dist p (centerOfParam i t) = 0 := by
        rw [hp_center, dist_self]
      have hdist_eq :
          dist p (centerOfParam i t) = r (centerOfParam i t) := by
        simpa [Metric.mem_sphere, dist_eq_norm] using hp_sphere_i
      linarith [hrpos (centerOfParam i t) (hcenterOfParam_T i t)]
    · have hdis :
          Disjoint
            (Metric.closedBall (centerOfParam i t) (r (centerOfParam i t)))
            (segment ℝ (a j) (b j)) :=
        hmiss (hcenterOfParam_T i t) j hcenter_on_j
      exact (Set.disjoint_left.mp hdis) hp_closed_i hpseg_j

private lemma endpointUnitDiskAssembly_sharedPointTransverseRoles
    {ι : Type*} [Fintype ι]
    (a b : ι → EuclideanSpace ℝ (Fin 2))
    (T : Finset (EuclideanSpace ℝ (Fin 2)))
    (r : EuclideanSpace ℝ (Fin 2) → ℝ)
    (Gamma : ι → PolygonalArc)
    (localXi :
      ∀ z : endpointUnitDiskAssembly_center T,
        endpointUnitDiskAssembly_incident a b z.1 → PolygonalArc)
    (hsharedPointRoles :
      ∀ ⦃i j : ι⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        i ≠ j →
          p ∈ (Gamma i).relativeInterior →
            p ∈ (Gamma j).relativeInterior →
              ((p ∈ openSegment ℝ (a i) (b i) ∧
                    ∀ z : EuclideanSpace ℝ (Fin 2),
                      z ∈ T → p ∉ Metric.closedBall z (r z)) ∧
                  (p ∈ openSegment ℝ (a j) (b j) ∧
                    ∀ z : EuclideanSpace ℝ (Fin 2),
                      z ∈ T → p ∉ Metric.closedBall z (r z))) ∨
                (∃ (z : endpointUnitDiskAssembly_center T)
                    (ii jj : endpointUnitDiskAssembly_incident a b z.1),
                  ii.1 = i ∧ jj.1 = j ∧
                    p ∈ (localXi z ii).relativeInterior ∧
                      p ∈ (localXi z jj).relativeInterior))
    (hchordTransverse :
      ∀ ⦃i j : ι⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        i ≠ j →
          p ∈ openSegment ℝ (a i) (b i) →
            p ∈ openSegment ℝ (a j) (b j) →
              ¬ ∃ t : ℝ, b j - a j = t • (b i - a i))
    (hlocalTransverse :
      ∀ (z : endpointUnitDiskAssembly_center T)
          ⦃ii jj : endpointUnitDiskAssembly_incident a b z.1⦄
          ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        ii ≠ jj →
          p ∈ (localXi z ii).relativeInterior →
            p ∈ (localXi z jj).relativeInterior →
              ∃ m n : ℕ,
                ∃ (hm : m + 1 < (localXi z ii).vertices.length)
                  (hn : n + 1 < (localXi z jj).vertices.length),
                  p ∈ segment ℝ (localXi z ii).vertices[m]
                      (localXi z ii).vertices[m + 1] ∧
                    p ∈ segment ℝ (localXi z jj).vertices[n]
                        (localXi z jj).vertices[n + 1] ∧
                      ¬ ∃ t : ℝ,
                        (localXi z jj).vertices[n + 1] -
                            (localXi z jj).vertices[n] =
                          t • ((localXi z ii).vertices[m + 1] -
                            (localXi z ii).vertices[m])) :
    ∀ ⦃i j : ι⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
      i ≠ j →
        p ∈ (Gamma i).relativeInterior →
          p ∈ (Gamma j).relativeInterior →
            ((p ∈ openSegment ℝ (a i) (b i) ∧
                  ∀ z : EuclideanSpace ℝ (Fin 2),
                    z ∈ T → p ∉ Metric.closedBall z (r z)) ∧
                (p ∈ openSegment ℝ (a j) (b j) ∧
                  ∀ z : EuclideanSpace ℝ (Fin 2),
                    z ∈ T → p ∉ Metric.closedBall z (r z)) ∧
                  ¬ ∃ t : ℝ, b j - a j = t • (b i - a i)) ∨
              (∃ (z : endpointUnitDiskAssembly_center T) (ii jj : endpointUnitDiskAssembly_incident a b z.1),
                ii.1 = i ∧ jj.1 = j ∧
                  p ∈ (localXi z ii).relativeInterior ∧
                    p ∈ (localXi z jj).relativeInterior ∧
                      ∃ m n : ℕ,
                        ∃ (hm : m + 1 < (localXi z ii).vertices.length)
                          (hn : n + 1 < (localXi z jj).vertices.length),
                          p ∈ segment ℝ (localXi z ii).vertices[m]
                              (localXi z ii).vertices[m + 1] ∧
                            p ∈ segment ℝ (localXi z jj).vertices[n]
                                (localXi z jj).vertices[n + 1] ∧
                              ¬ ∃ t : ℝ,
                                (localXi z jj).vertices[n + 1] -
                                    (localXi z jj).vertices[n] =
                                  t • ((localXi z ii).vertices[m + 1] -
                                    (localXi z ii).vertices[m])) := by
  intro i j p hij hpi hpj
  rcases hsharedPointRoles hij hpi hpj with houtside | hlocal
  · exact Or.inl ⟨houtside.1, houtside.2,
      hchordTransverse hij houtside.1.1 houtside.2.1⟩
  · rcases hlocal with ⟨z, ii, jj, hii, hjj, hpii, hpjj⟩
    have hij_inc : ii ≠ jj := by
      intro hijj
      apply hij
      have hval : ii.1 = jj.1 := congrArg Subtype.val hijj
      rwa [hii, hjj] at hval
    exact Or.inr ⟨z, ii, jj, hii, hjj, hpii, hpjj,
      hlocalTransverse z hij_inc hpii hpjj⟩

private lemma endpointUnitDiskAssembly_blockEdgeInAlternating :
    ∀ {β : Type}
      (A B : EuclideanSpace ℝ (Fin 2))
      (items pre post : List β)
      (block : β → List (EuclideanSpace ℝ (Fin 2)))
      (x : β) (q : ℕ),
      (hitems : items = pre ++ x :: post) →
        (hq : q + 1 < (block x).length) →
          ∃ m : ℕ,
            ∃ hm : m + 1 <
              (EndpointUnitDiskAlternatingVertexList A B (items.map block)).length,
              (EndpointUnitDiskAlternatingVertexList A B (items.map block))[m] =
                  (block x)[q]'(Nat.lt_trans (Nat.lt_succ_self q) hq) ∧
                (EndpointUnitDiskAlternatingVertexList A B
                    (items.map block))[m + 1] =
                  (block x)[q + 1]'hq := by
  intro β A B items pre post block x q hitems hq
  subst items
  let l := (pre.map block).flatten.length
  refine ⟨l + q + 1, ?_, ?_, ?_⟩
  · simp [EndpointUnitDiskAlternatingVertexList, List.map_append,
      List.flatten_append, l]
    omega
  · simp only [EndpointUnitDiskAlternatingVertexList, List.map_append,
      List.map_cons, List.flatten_append, List.flatten_cons, List.append_assoc,
      List.singleton_append, List.cons_append, List.getElem_cons_succ]
    have hidx :
        l + q <
          ((pre.map block).flatten ++ (block x ++ ((post.map block).flatten ++ [B]))).length := by
      simp [l]
      omega
    change (((pre.map block).flatten ++
        (block x ++ ((post.map block).flatten ++ [B]))))[l + q]'hidx =
      (block x)[q]'(Nat.lt_trans (Nat.lt_succ_self q) hq)
    rw [List.getElem_append_right (by simp [l])]
    have hsub_sum :
        l + q - (List.map (List.length ∘ block) pre).sum = q := by
      simp [l]
    have hq_left : q < (block x).length :=
      Nat.lt_trans (Nat.lt_succ_self q) hq
    have hq_app :
        q < (block x ++ ((post.map block).flatten ++ [B])).length := by
      simp
      omega
    have hget :
        (block x ++ ((post.map block).flatten ++ [B]))[q]'hq_app =
          (block x)[q]'hq_left :=
      List.getElem_append_left (as := block x)
        (bs := (post.map block).flatten ++ [B]) (i := q) hq_left
    simpa [hsub_sum] using hget
  · simp only [EndpointUnitDiskAlternatingVertexList, List.map_append,
      List.map_cons, List.flatten_append, List.flatten_cons, List.append_assoc,
      List.singleton_append, List.cons_append, List.getElem_cons_succ]
    have hidx :
        l + (q + 1) <
          ((pre.map block).flatten ++ (block x ++ ((post.map block).flatten ++ [B]))).length := by
      simp [l]
      omega
    change (((pre.map block).flatten ++
        (block x ++ ((post.map block).flatten ++ [B]))))[l + (q + 1)]'hidx =
      (block x)[q + 1]'hq
    rw [List.getElem_append_right (by simp [l])]
    have hsub_sum :
        l + (q + 1) - (List.map (List.length ∘ block) pre).sum = q + 1 := by
      simp [l]
    have hq_app :
        q + 1 < (block x ++ ((post.map block).flatten ++ [B])).length := by
      simp
      omega
    have hget :
        (block x ++ ((post.map block).flatten ++ [B]))[q + 1]'hq_app =
          (block x)[q + 1]'hq :=
      List.getElem_append_left (as := block x)
        (bs := (post.map block).flatten ++ [B]) (i := q + 1) hq
    simpa [hsub_sum] using hget

private lemma endpointUnitDiskAssembly_localEdgeInAssembled
    {ι : Type*}
    (a b : ι → EuclideanSpace ℝ (Fin 2))
    (centerParams : ι → List ℝ)
    (localArcAtParam :
      ∀ i, {t : ℝ // t ∈ centerParams i} → PolygonalArc)
    (orderedLocalVertexBlocks :
      ∀ i, List (List (EuclideanSpace ℝ (Fin 2))))
    (assembledVertices : ι → List (EuclideanSpace ℝ (Fin 2)))
    (horderedLocalVertexBlocks_def : ∀ i,
      orderedLocalVertexBlocks i =
        (centerParams i).attach.map
          (fun t => (localArcAtParam i t).vertices))
    (hassembledVertices_def : ∀ i,
      assembledVertices i =
        EndpointUnitDiskAlternatingVertexList
          (a i) (b i) (orderedLocalVertexBlocks i)) :
    ∀ i (pre : List {t : ℝ // t ∈ centerParams i})
        (t : {t : ℝ // t ∈ centerParams i})
        (post : List {t : ℝ // t ∈ centerParams i}) (q : ℕ),
      (centerParams i).attach = pre ++ t :: post →
        (hq : q + 1 < (localArcAtParam i t).vertices.length) →
          ∃ m : ℕ,
            ∃ hm : m + 1 < (assembledVertices i).length,
              (assembledVertices i)[m] =
                  (localArcAtParam i t).vertices[q]'(Nat.lt_trans (Nat.lt_succ_self q) hq) ∧
                (assembledVertices i)[m + 1] =
                  (localArcAtParam i t).vertices[q + 1]'hq := by
  intro i pre t post q hitems hq
  simpa [hassembledVertices_def i, horderedLocalVertexBlocks_def i] using
    endpointUnitDiskAssembly_blockEdgeInAlternating (A := a i) (B := b i)
      (items := (centerParams i).attach) (pre := pre) (post := post)
      (block := fun t : {t : ℝ // t ∈ centerParams i} =>
        (localArcAtParam i t).vertices)
      (x := t) (q := q) hitems hq

private lemma endpointUnitDiskAssembly_outsideEdgeDirection
    {ι : Type*} [Fintype ι]
    (a b : ι → EuclideanSpace ℝ (Fin 2))
    (T : Finset (EuclideanSpace ℝ (Fin 2)))
    (r : EuclideanSpace ℝ (Fin 2) → ℝ)
    (centerParams : ι → List ℝ)
    (centerOfParam :
      ∀ i, {t : ℝ // t ∈ centerParams i} → EuclideanSpace ℝ (Fin 2))
    (localArcAtParam :
      ∀ i, {t : ℝ // t ∈ centerParams i} → PolygonalArc)
    (entryPoint exitPoint :
      ∀ i, {t : ℝ // t ∈ centerParams i} → EuclideanSpace ℝ (Fin 2))
    (assembledVertices : ι → List (EuclideanSpace ℝ (Fin 2)))
    (hassembledEdgeEndpointRoles :
      ∀ i ⦃m : ℕ⦄,
        (hm : m + 1 < (assembledVertices i).length) →
          ((centerParams i).attach = [] ∧
              (assembledVertices i)[m] = a i ∧
                (assembledVertices i)[m + 1] = b i) ∨
            endpointUnitDiskAssembly_nonemptyRole a b centerParams
              localArcAtParam assembledVertices i m hm)
    (hlocalArcAtParam_props :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}),
        (localArcAtParam i t).source = entryPoint i t ∧
          (localArcAtParam i t).target = exitPoint i t ∧
            (localArcAtParam i t).carrier ⊆
              Metric.closedBall (centerOfParam i t) (r (centerOfParam i t)) ∧
              (localArcAtParam i t).relativeInterior ⊆
                Metric.ball (centerOfParam i t) (r (centerOfParam i t)))
    (hcenterOfParam_T :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}), centerOfParam i t ∈ T)
    (hentryExitParameters :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}),
        (∃ s : ℝ, 0 < s ∧ s < t.1 ∧
          entryPoint i t = AffineMap.lineMap (a i) (b i) s) ∧
          (∃ s : ℝ, t.1 < s ∧ s < 1 ∧
            exitPoint i t = AffineMap.lineMap (a i) (b i) s))
    (hattach_pairwise_lt_all :
      ∀ i,
        (centerParams i).attach.Pairwise
          (fun t1 t2 : {t : ℝ // t ∈ centerParams i} => t1.1 < t2.1))
    (horderedCutSeparation :
      ∀ i (t1 t2 : {t : ℝ // t ∈ centerParams i}),
        t1.1 < t2.1 →
          ∃ sExit sEntry : ℝ,
            t1.1 < sExit ∧
              sExit < sEntry ∧
                sEntry < t2.1 ∧
                  exitPoint i t1 = AffineMap.lineMap (a i) (b i) sExit ∧
                    entryPoint i t2 = AffineMap.lineMap (a i) (b i) sEntry)
    (hendpoint_ne : ∀ i, a i ≠ b i)
    (hlineMapVecLeft :
      ∀ (A B : EuclideanSpace ℝ (Fin 2)) (e : ℝ),
        AffineMap.lineMap A B e - A = e • (B - A))
    (hlineMapVecBetween :
      ∀ (A B : EuclideanSpace ℝ (Fin 2)) (x y : ℝ),
        AffineMap.lineMap A B y - AffineMap.lineMap A B x =
          (y - x) • (B - A))
    (hlineMapVecRight :
      ∀ (A B : EuclideanSpace ℝ (Fin 2)) (x : ℝ),
        B - AffineMap.lineMap A B x = (1 - x) • (B - A)) :
    ∀ i ⦃p : EuclideanSpace ℝ (Fin 2)⦄ ⦃m : ℕ⦄,
      (hm : m + 1 < (assembledVertices i).length) →
        p ∈ segment ℝ (assembledVertices i)[m] (assembledVertices i)[m + 1] →
          (p ∈ openSegment ℝ (a i) (b i) ∧
              ∀ z : EuclideanSpace ℝ (Fin 2),
                z ∈ T → p ∉ Metric.closedBall z (r z)) →
            ∃ c : ℝ,
              c ≠ 0 ∧
                (assembledVertices i)[m + 1] - (assembledVertices i)[m] =
                  c • (b i - a i) := by
  intro i p m hm hpseg hpoutside
  rcases hassembledEdgeEndpointRoles i hm with hnodisks | hroles
  · rcases hnodisks with ⟨_hitems, hleft, hright⟩
    refine ⟨1, by norm_num, ?_⟩
    simpa [hleft, hright]
  rcases hroles with hinitial | hroles
  · rcases hinitial with ⟨t, _ts, X, _hitems, hhead, hleft, hright⟩
    have hsource_entry :
        (localArcAtParam i t).vertices.head? = some (entryPoint i t) := by
      have hsource := (localArcAtParam i t).source_eq_head
      rw [(hlocalArcAtParam_props i t).1] at hsource
      exact hsource
    have hX : X = entryPoint i t := by
      exact (Option.some.inj (hsource_entry.symm.trans hhead)).symm
    rcases hentryExitParameters i t with
      ⟨⟨e, he_pos, _he_lt_t, hentry⟩, _⟩
    refine ⟨e, ne_of_gt he_pos, ?_⟩
    calc
      (assembledVertices i)[m + 1] - (assembledVertices i)[m]
          = entryPoint i t - a i := by simp [hleft, hright, hX]
      _ = e • (b i - a i) := by
        simpa [hentry] using hlineMapVecLeft (a i) (b i) e
  rcases hroles with hlocal | hroles
  · rcases hlocal with ⟨_pre, t, _post, q, hq, _hitems, hleft, hright⟩
    have hp_carrier : p ∈ (localArcAtParam i t).carrier := by
      rw [(localArcAtParam i t).carrier_eq]
      exact ⟨q, hq, by simpa [hleft, hright] using hpseg⟩
    have hp_closed :
        p ∈ Metric.closedBall (centerOfParam i t) (r (centerOfParam i t)) :=
      (hlocalArcAtParam_props i t).2.2.1 hp_carrier
    exact False.elim
      (hpoutside.2 (centerOfParam i t) (hcenterOfParam_T i t) hp_closed)
  rcases hroles with hbridge | hterminal
  · rcases hbridge with ⟨pre, t1, t2, post, X, Y, hitems, hlast, hhead,
      hleft, hright⟩
    have hlast_exit :
        (localArcAtParam i t1).vertices.getLast? = some (exitPoint i t1) := by
      have htarget := (localArcAtParam i t1).target_eq_last
      rw [(hlocalArcAtParam_props i t1).2.1] at htarget
      exact htarget
    have hX : X = exitPoint i t1 := by
      exact (Option.some.inj (hlast_exit.symm.trans hlast)).symm
    have hhead_entry :
        (localArcAtParam i t2).vertices.head? = some (entryPoint i t2) := by
      have hsource := (localArcAtParam i t2).source_eq_head
      rw [(hlocalArcAtParam_props i t2).1] at hsource
      exact hsource
    have hY : Y = entryPoint i t2 := by
      exact (Option.some.inj (hhead_entry.symm.trans hhead)).symm
    have hpair_bridge := hattach_pairwise_lt_all i
    rw [hitems] at hpair_bridge
    have htail_pair :
        (t1 :: t2 :: post).Pairwise
          (fun u v : {t : ℝ // t ∈ centerParams i} => u.1 < v.1) :=
      (List.pairwise_append.1 hpair_bridge).2.1
    have ht12 : t1.1 < t2.1 :=
      (List.pairwise_cons.1 htail_pair).1 t2 (by simp)
    rcases hentryExitParameters i t1 with
      ⟨_hentry1, ⟨x1, _ht1_lt_x1, _hx1_lt_one, hexit1⟩⟩
    rcases hentryExitParameters i t2 with
      ⟨⟨e2, _he2_pos, _he2_lt_t2, hentry2⟩, _hexit2⟩
    rcases horderedCutSeparation i t1 t2 ht12 with
      ⟨sExit, sEntry, _ht1_sExit, hsExitEntry, _hsEntry_t2,
        hexit_order, hentry_order⟩
    let f : ℝ →ᵃ[ℝ] EuclideanSpace ℝ (Fin 2) :=
      AffineMap.lineMap (a i) (b i)
    have hf : Function.Injective f :=
      AffineMap.lineMap_injective (k := ℝ) (hendpoint_ne i)
    have hx1_eq : x1 = sExit := by
      exact hf (by rw [← hexit1, ← hexit_order])
    have he2_eq : e2 = sEntry := by
      exact hf (by rw [← hentry2, ← hentry_order])
    have hx1_lt_e2 : x1 < e2 := by
      linarith
    refine ⟨e2 - x1, sub_ne_zero.mpr (ne_of_gt hx1_lt_e2), ?_⟩
    calc
      (assembledVertices i)[m + 1] - (assembledVertices i)[m]
          = entryPoint i t2 - exitPoint i t1 := by simp [hleft, hright, hX, hY]
      _ = (e2 - x1) • (b i - a i) := by
        simpa [hexit1, hentry2] using
          hlineMapVecBetween (a i) (b i) x1 e2
  · rcases hterminal with ⟨_pre, t, X, _hitems, hlast, hleft, hright⟩
    have hlast_exit :
        (localArcAtParam i t).vertices.getLast? = some (exitPoint i t) := by
      have htarget := (localArcAtParam i t).target_eq_last
      rw [(hlocalArcAtParam_props i t).2.1] at htarget
      exact htarget
    have hX : X = exitPoint i t := by
      exact (Option.some.inj (hlast_exit.symm.trans hlast)).symm
    rcases hentryExitParameters i t with
      ⟨_hentry, ⟨x, _ht_lt_x, hx_lt_one, hexit⟩⟩
    refine ⟨1 - x, sub_ne_zero.mpr (by linarith), ?_⟩
    calc
      (assembledVertices i)[m + 1] - (assembledVertices i)[m]
          = b i - exitPoint i t := by simp [hleft, hright, hX]
      _ = (1 - x) • (b i - a i) := by
        simpa [hexit] using hlineMapVecRight (a i) (b i) x

private abbrev endpointUnitDiskAssembly_transverseWitness
    {ι : Type*}
    (Gamma : ι → PolygonalArc) (i j : ι)
    (p : EuclideanSpace ℝ (Fin 2)) : Prop :=
  ∃ m n : ℕ,
    ∃ (hm : m + 1 < (Gamma i).vertices.length)
      (hn : n + 1 < (Gamma j).vertices.length),
      p ∈ segment ℝ (Gamma i).vertices[m] (Gamma i).vertices[m + 1] ∧
        p ∈ segment ℝ (Gamma j).vertices[n] (Gamma j).vertices[n + 1] ∧
          ¬ ∃ t : ℝ,
            (Gamma j).vertices[n + 1] - (Gamma j).vertices[n] =
              t • ((Gamma i).vertices[m + 1] - (Gamma i).vertices[m])

private abbrev endpointUnitDiskAssembly_localTransverseRole
    {ι : Type*}
    (a b : ι → EuclideanSpace ℝ (Fin 2))
    (T : Finset (EuclideanSpace ℝ (Fin 2)))
    (localXi :
      ∀ z : endpointUnitDiskAssembly_center T,
        endpointUnitDiskAssembly_incident a b z.1 → PolygonalArc)
    (i j : ι) (p : EuclideanSpace ℝ (Fin 2)) : Prop :=
  ∃ (z : endpointUnitDiskAssembly_center T)
      (ii jj : endpointUnitDiskAssembly_incident a b z.1),
    ii.1 = i ∧ jj.1 = j ∧
      p ∈ (localXi z ii).relativeInterior ∧
        p ∈ (localXi z jj).relativeInterior ∧
          ∃ m n : ℕ,
            ∃ (hm : m + 1 < (localXi z ii).vertices.length)
              (hn : n + 1 < (localXi z jj).vertices.length),
              p ∈ segment ℝ (localXi z ii).vertices[m]
                  (localXi z ii).vertices[m + 1] ∧
                p ∈ segment ℝ (localXi z jj).vertices[n]
                    (localXi z jj).vertices[n + 1] ∧
                  ¬ ∃ t : ℝ,
                    (localXi z jj).vertices[n + 1] -
                        (localXi z jj).vertices[n] =
                      t • ((localXi z ii).vertices[m + 1] -
                        (localXi z ii).vertices[m])

private lemma endpointUnitDiskAssembly_interiorEdgeWitness
    {ι : Type*}
    (a b : ι → EuclideanSpace ℝ (Fin 2))
    (assembledVertices : ι → List (EuclideanSpace ℝ (Fin 2)))
    (assembledEdgeSet : ι → Set (EuclideanSpace ℝ (Fin 2)))
    (Gamma : ι → PolygonalArc)
    (hassembledEdgeSet_mem :
      ∀ i p,
        p ∈ assembledEdgeSet i ↔
          ∃ m : ℕ, ∃ hm : m + 1 < (assembledVertices i).length,
            p ∈ segment ℝ (assembledVertices i)[m]
              (assembledVertices i)[m + 1])
    (hGamma_relativeInterior :
      ∀ i, (Gamma i).relativeInterior =
        assembledEdgeSet i \ ({a i, b i} : Set (EuclideanSpace ℝ (Fin 2)))) :
    ∀ i ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
      p ∈ (Gamma i).relativeInterior →
        ∃ m : ℕ, ∃ hm : m + 1 < (assembledVertices i).length,
          p ∈ segment ℝ (assembledVertices i)[m]
            (assembledVertices i)[m + 1] := by
  intro i p hp
  rw [hGamma_relativeInterior i] at hp
  exact (hassembledEdgeSet_mem i p).1 hp.1

private lemma endpointUnitDiskAssembly_localArcRealize
    {ι : Type*}
    (a b : ι → EuclideanSpace ℝ (Fin 2))
    (T : Finset (EuclideanSpace ℝ (Fin 2)))
    (centerParams : ι → List ℝ)
    (centerOfParam :
      ∀ i, {t : ℝ // t ∈ centerParams i} → EuclideanSpace ℝ (Fin 2))
    (centerAtParam :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}),
        endpointUnitDiskAssembly_center T)
    (incidentAtParam :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}),
        endpointUnitDiskAssembly_incident a b (centerAtParam i t).1)
    (localXi :
      ∀ z : endpointUnitDiskAssembly_center T,
        endpointUnitDiskAssembly_incident a b z.1 → PolygonalArc)
    (localArcAtParam :
      ∀ i, {t : ℝ // t ∈ centerParams i} → PolygonalArc)
    (hcenterAtParam_val :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}),
        (centerAtParam i t).1 = centerOfParam i t)
    (hincidentAtParam_val :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}),
        (incidentAtParam i t).1 = i)
    (hlocalArcAtParam_def :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}),
        localArcAtParam i t =
          localXi (centerAtParam i t) (incidentAtParam i t))
    (hchosenCenterOnChord_param :
      ∀ i ⦃z : EuclideanSpace ℝ (Fin 2)⦄,
        z ∈ T →
          z ∈ segment ℝ (a i) (b i) →
            ∃ t : {t : ℝ // t ∈ centerParams i}, centerOfParam i t = z) :
    ∀ i (z : endpointUnitDiskAssembly_center T)
        (ii : endpointUnitDiskAssembly_incident a b z.1),
      ii.1 = i →
        ∃ t : {t : ℝ // t ∈ centerParams i},
          localArcAtParam i t = localXi z ii := by
  intro i z ii hii
  have hz_i_open : z.1 ∈ openSegment ℝ (a i) (b i) := by
    simpa [hii] using ii.2
  rcases hchosenCenterOnChord_param i z.2
      (openSegment_subset_segment ℝ (a i) (b i) hz_i_open) with
    ⟨ti, hti_center⟩
  refine ⟨ti, ?_⟩
  have hz_eq : centerAtParam i ti = z := by
    apply Subtype.ext
    exact (hcenterAtParam_val i ti).trans hti_center
  subst z
  have hii_eq : incidentAtParam i ti = ii := by
    apply Subtype.ext
    exact (hincidentAtParam_val i ti).trans hii.symm
  rw [hlocalArcAtParam_def i ti, hii_eq]

private lemma endpointUnitDiskAssembly_sharedPointTransverse
    {ι : Type*} [Fintype ι]
    (a b : ι → EuclideanSpace ℝ (Fin 2))
    (T : Finset (EuclideanSpace ℝ (Fin 2)))
    (r : EuclideanSpace ℝ (Fin 2) → ℝ)
    (centerParams : ι → List ℝ)
    (localArcAtParam :
      ∀ i, {t : ℝ // t ∈ centerParams i} → PolygonalArc)
    (assembledVertices : ι → List (EuclideanSpace ℝ (Fin 2)))
    (Gamma : ι → PolygonalArc)
    (localXi :
      ∀ z : endpointUnitDiskAssembly_center T,
        endpointUnitDiskAssembly_incident a b z.1 → PolygonalArc)
    (hGamma_vertices : ∀ i, (Gamma i).vertices = assembledVertices i)
    (hGammaInteriorEdges :
      ∀ i ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        p ∈ (Gamma i).relativeInterior →
          ∃ m : ℕ, ∃ hm : m + 1 < (assembledVertices i).length,
            p ∈ segment ℝ (assembledVertices i)[m]
              (assembledVertices i)[m + 1])
    (hsharedPointTransverseRoles :
      ∀ ⦃i j : ι⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        i ≠ j →
          p ∈ (Gamma i).relativeInterior →
            p ∈ (Gamma j).relativeInterior →
              (((p ∈ openSegment ℝ (a i) (b i) ∧
                    ∀ z : EuclideanSpace ℝ (Fin 2),
                      z ∈ T → p ∉ Metric.closedBall z (r z)) ∧
                  (p ∈ openSegment ℝ (a j) (b j) ∧
                    ∀ z : EuclideanSpace ℝ (Fin 2),
                      z ∈ T → p ∉ Metric.closedBall z (r z)) ∧
                    ¬ ∃ t : ℝ, b j - a j = t • (b i - a i)) ∨
                endpointUnitDiskAssembly_localTransverseRole
                  a b T localXi i j p))
    (hlocalArcRealize :
      ∀ i (z : endpointUnitDiskAssembly_center T)
          (ii : endpointUnitDiskAssembly_incident a b z.1),
        ii.1 = i →
          ∃ t : {t : ℝ // t ∈ centerParams i},
            localArcAtParam i t = localXi z ii)
    (hlocalEdgeInAssembled :
      ∀ i (pre : List {t : ℝ // t ∈ centerParams i})
          (t : {t : ℝ // t ∈ centerParams i})
          (post : List {t : ℝ // t ∈ centerParams i}) (q : ℕ),
        (centerParams i).attach = pre ++ t :: post →
          (hq : q + 1 < (localArcAtParam i t).vertices.length) →
            ∃ m : ℕ,
              ∃ hm : m + 1 < (assembledVertices i).length,
                (assembledVertices i)[m] =
                    (localArcAtParam i t).vertices[q]'(
                      Nat.lt_trans (Nat.lt_succ_self q) hq) ∧
                  (assembledVertices i)[m + 1] =
                    (localArcAtParam i t).vertices[q + 1]'hq)
    (houtsideEdgeDirection :
      ∀ i ⦃p : EuclideanSpace ℝ (Fin 2)⦄ ⦃m : ℕ⦄,
        (hm : m + 1 < (assembledVertices i).length) →
          p ∈ segment ℝ (assembledVertices i)[m]
              (assembledVertices i)[m + 1] →
            (p ∈ openSegment ℝ (a i) (b i) ∧
                ∀ z : EuclideanSpace ℝ (Fin 2),
                  z ∈ T → p ∉ Metric.closedBall z (r z)) →
              ∃ c : ℝ,
                c ≠ 0 ∧
                  (assembledVertices i)[m + 1] -
                      (assembledVertices i)[m] =
                    c • (b i - a i))
    (hscalarTransfer :
      ∀ {vi vj ei ej : EuclideanSpace ℝ (Fin 2)} {ci cj t : ℝ},
        cj ≠ 0 →
          ei = ci • vi →
            ej = cj • vj →
              ej = t • ei →
                vj = (cj⁻¹ * t * ci) • vi) :
    ∀ ⦃i j : ι⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
      i ≠ j →
        p ∈ (Gamma i).relativeInterior →
          p ∈ (Gamma j).relativeInterior →
            endpointUnitDiskAssembly_transverseWitness Gamma i j p := by
  intro i j p hij hpi hpj
  rcases hsharedPointTransverseRoles hij hpi hpj with houtside | hlocal
  · rcases hGammaInteriorEdges i hpi with ⟨m, hm, hpm⟩
    rcases hGammaInteriorEdges j hpj with ⟨n, hn, hpn⟩
    rcases houtsideEdgeDirection i hm hpm houtside.1 with
      ⟨ci, _hci_ne, hdir_i⟩
    rcases houtsideEdgeDirection j hn hpn houtside.2.1 with
      ⟨cj, hcj_ne, hdir_j⟩
    have hmΓ : m + 1 < (Gamma i).vertices.length := by
      simpa [hGamma_vertices i] using hm
    have hnΓ : n + 1 < (Gamma j).vertices.length := by
      simpa [hGamma_vertices j] using hn
    refine ⟨m, n, hmΓ, hnΓ, ?_, ?_, ?_⟩
    · simpa [hGamma_vertices i] using hpm
    · simpa [hGamma_vertices j] using hpn
    · intro hscalar
      apply houtside.2.2
      rcases hscalar with ⟨t, ht⟩
      have ht_assembled :
          (assembledVertices j)[n + 1] - (assembledVertices j)[n] =
            t • ((assembledVertices i)[m + 1] - (assembledVertices i)[m]) := by
        simpa [hGamma_vertices i, hGamma_vertices j] using ht
      exact ⟨cj⁻¹ * t * ci,
        hscalarTransfer (ci := ci) (cj := cj) (t := t) hcj_ne hdir_i hdir_j
          ht_assembled⟩
  · rcases hlocal with
      ⟨z, ii, jj, hii, hjj, _hpii, _hpjj, q_i, q_j, hq_i, hq_j,
        hpseg_i, hpseg_j, hnonscalar⟩
    rcases hlocalArcRealize i z ii hii with ⟨ti, hlocalArc_i⟩
    rcases hlocalArcRealize j z jj hjj with ⟨tj, hlocalArc_j⟩
    have hq_i' : q_i + 1 < (localArcAtParam i ti).vertices.length := by
      simpa [hlocalArc_i] using hq_i
    have hq_j' : q_j + 1 < (localArcAtParam j tj).vertices.length := by
      simpa [hlocalArc_j] using hq_j
    have hti_attach : ti ∈ (centerParams i).attach := by
      simp
    have htj_attach : tj ∈ (centerParams j).attach := by
      simp
    rcases (List.mem_iff_append.mp hti_attach) with ⟨pre_i, post_i, hitems_i⟩
    rcases (List.mem_iff_append.mp htj_attach) with ⟨pre_j, post_j, hitems_j⟩
    rcases hlocalEdgeInAssembled i pre_i ti post_i q_i hitems_i hq_i' with
      ⟨m, hm, hm_left, hm_right⟩
    rcases hlocalEdgeInAssembled j pre_j tj post_j q_j hitems_j hq_j' with
      ⟨n, hn, hn_left, hn_right⟩
    have hmΓ : m + 1 < (Gamma i).vertices.length := by
      simpa [hGamma_vertices i] using hm
    have hnΓ : n + 1 < (Gamma j).vertices.length := by
      simpa [hGamma_vertices j] using hn
    refine ⟨m, n, hmΓ, hnΓ, ?_, ?_, ?_⟩
    · have hpseg_i' :
          p ∈ segment ℝ (assembledVertices i)[m] (assembledVertices i)[m + 1] := by
        simpa [hm_left, hm_right, hlocalArc_i] using hpseg_i
      simpa [hGamma_vertices i] using hpseg_i'
    · have hpseg_j' :
          p ∈ segment ℝ (assembledVertices j)[n] (assembledVertices j)[n + 1] := by
        simpa [hn_left, hn_right, hlocalArc_j] using hpseg_j
      simpa [hGamma_vertices j] using hpseg_j'
    · intro hscalar
      apply hnonscalar
      rcases hscalar with ⟨t, ht⟩
      refine ⟨t, ?_⟩
      have ht_assembled :
          (assembledVertices j)[n + 1] - (assembledVertices j)[n] =
            t • ((assembledVertices i)[m + 1] - (assembledVertices i)[m]) := by
        simpa [hGamma_vertices i, hGamma_vertices j] using ht
      simpa [hm_left, hm_right, hn_left, hn_right, hlocalArc_i, hlocalArc_j]
        using ht_assembled

private lemma endpointUnitDiskAssembly_assembledVertexCases
    {ι : Type*}
    (a b : ι → EuclideanSpace ℝ (Fin 2))
    (centerParams : ι → List ℝ)
    (localArcAtParam :
      ∀ i, {t : ℝ // t ∈ centerParams i} → PolygonalArc)
    (orderedLocalVertexBlocks :
      ∀ i, List (List (EuclideanSpace ℝ (Fin 2))))
    (assembledVertices : ι → List (EuclideanSpace ℝ (Fin 2)))
    (horderedLocalVertexBlocks_def : ∀ i,
      orderedLocalVertexBlocks i =
        (centerParams i).attach.map
          (fun t => (localArcAtParam i t).vertices))
    (hassembledVertices_def : ∀ i,
      assembledVertices i =
        EndpointUnitDiskAlternatingVertexList
          (a i) (b i) (orderedLocalVertexBlocks i)) :
    ∀ i ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
      p ∈ assembledVertices i →
        p = a i ∨
          (∃ t : {t : ℝ // t ∈ centerParams i},
            p ∈ (localArcAtParam i t).vertices) ∨
          p = b i := by
  intro i p hp
  rw [hassembledVertices_def i, horderedLocalVertexBlocks_def i] at hp
  simp [EndpointUnitDiskAlternatingVertexList] at hp
  rcases hp with hpA | hpflat | hpB
  · exact Or.inl hpA
  · rcases hpflat with ⟨t, ht, hpV⟩
    exact Or.inr (Or.inl ⟨⟨t, ht⟩, hpV⟩)
  · exact Or.inr (Or.inr hpB)

private lemma endpointUnitDiskAssembly_sharedPointOpen
    {ι : Type*} [Fintype ι]
    (a b : ι → EuclideanSpace ℝ (Fin 2))
    (T : Finset (EuclideanSpace ℝ (Fin 2)))
    (r : EuclideanSpace ℝ (Fin 2) → ℝ)
    (centerParams : ι → List ℝ)
    (centerOfParam :
      ∀ i, {t : ℝ // t ∈ centerParams i} → EuclideanSpace ℝ (Fin 2))
    (localArcAtParam :
      ∀ i, {t : ℝ // t ∈ centerParams i} → PolygonalArc)
    (assembledVertices : ι → List (EuclideanSpace ℝ (Fin 2)))
    (Gamma : ι → PolygonalArc)
    (localXi :
      ∀ z : endpointUnitDiskAssembly_center T,
        endpointUnitDiskAssembly_incident a b z.1 → PolygonalArc)
    (hsharedPointRoles :
      ∀ ⦃i j : ι⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        i ≠ j →
          p ∈ (Gamma i).relativeInterior →
            p ∈ (Gamma j).relativeInterior →
              ((p ∈ openSegment ℝ (a i) (b i) ∧
                    ∀ z : EuclideanSpace ℝ (Fin 2),
                      z ∈ T → p ∉ Metric.closedBall z (r z)) ∧
                  (p ∈ openSegment ℝ (a j) (b j) ∧
                    ∀ z : EuclideanSpace ℝ (Fin 2),
                      z ∈ T → p ∉ Metric.closedBall z (r z))) ∨
                (∃ (z : endpointUnitDiskAssembly_center T)
                    (ii jj : endpointUnitDiskAssembly_incident a b z.1),
                  ii.1 = i ∧ jj.1 = j ∧
                    p ∈ (localXi z ii).relativeInterior ∧
                      p ∈ (localXi z jj).relativeInterior))
    (hendpoint_ne : ∀ i, a i ≠ b i)
    (hGamma_vertices : ∀ i, (Gamma i).vertices = assembledVertices i)
    (hGammaInteriorEdges :
      ∀ i ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        p ∈ (Gamma i).relativeInterior →
          ∃ m : ℕ, ∃ hm : m + 1 < (assembledVertices i).length,
            p ∈ segment ℝ (assembledVertices i)[m]
              (assembledVertices i)[m + 1])
    (hassembledVertices_cases :
      ∀ i ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        p ∈ assembledVertices i →
          p = a i ∨
            (∃ t : {t : ℝ // t ∈ centerParams i},
              p ∈ (localArcAtParam i t).vertices) ∨
            p = b i)
    (hlocalArcAtParam_closed :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}),
        (localArcAtParam i t).carrier ⊆
          Metric.closedBall (centerOfParam i t) (r (centerOfParam i t)))
    (hcenterOfParam_T :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}), centerOfParam i t ∈ T)
    (hcleanLocal :
      ∀ (z : endpointUnitDiskAssembly_center T)
          ⦃ii jj : endpointUnitDiskAssembly_incident a b z.1⦄
          ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        ii ≠ jj →
          p ∈ (localXi z ii).relativeInterior →
            p ∈ (localXi z jj).relativeInterior →
              Nonempty (OrdinaryCleanLocalCrossing (localXi z) ii jj p))
    (hlocalArcRealize :
      ∀ i (z : endpointUnitDiskAssembly_center T)
          (ii : endpointUnitDiskAssembly_incident a b z.1),
        ii.1 = i →
          ∃ t : {t : ℝ // t ∈ centerParams i},
            localArcAtParam i t = localXi z ii)
    (hlocalEdgeInAssembled :
      ∀ i (pre : List {t : ℝ // t ∈ centerParams i})
          (t : {t : ℝ // t ∈ centerParams i})
          (post : List {t : ℝ // t ∈ centerParams i}) (q : ℕ),
        (centerParams i).attach = pre ++ t :: post →
          (hq : q + 1 < (localArcAtParam i t).vertices.length) →
            ∃ m : ℕ,
              ∃ hm : m + 1 < (assembledVertices i).length,
                (assembledVertices i)[m] =
                    (localArcAtParam i t).vertices[q]'(
                      Nat.lt_trans (Nat.lt_succ_self q) hq) ∧
                  (assembledVertices i)[m + 1] =
                    (localArcAtParam i t).vertices[q + 1]'hq) :
    ∀ ⦃i j : ι⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
      i ≠ j →
        p ∈ (Gamma i).relativeInterior →
          p ∈ (Gamma j).relativeInterior →
            ∃ m n : ℕ,
              ∃ (hm : m + 1 < (Gamma i).vertices.length)
                (hn : n + 1 < (Gamma j).vertices.length),
                p ∈ openSegment ℝ (Gamma i).vertices[m]
                    (Gamma i).vertices[m + 1] ∧
                  p ∈ openSegment ℝ (Gamma j).vertices[n]
                    (Gamma j).vertices[n + 1] := by
  intro i j p hij hpi hpj
  rcases hsharedPointRoles hij hpi hpj with houtside | hlocal
  · have outside_open_index :
        ∀ (k : ι),
          p ∈ (Gamma k).relativeInterior →
            (p ∈ openSegment ℝ (a k) (b k) ∧
              ∀ z : EuclideanSpace ℝ (Fin 2),
                z ∈ T → p ∉ Metric.closedBall z (r z)) →
              ∃ s : ℕ, ∃ hs : s + 1 < (Gamma k).vertices.length,
                p ∈ openSegment ℝ (Gamma k).vertices[s]
                  (Gamma k).vertices[s + 1] := by
      intro k hpk hpout
      have hp_ne_a : p ≠ a k := by
        intro hpa
        have : a k ∈ openSegment ℝ (a k) (b k) := by simpa [hpa] using hpout.1
        exact (hendpoint_ne k) (left_mem_openSegment_iff.mp this)
      have hp_ne_b : p ≠ b k := by
        intro hpb
        have : b k ∈ openSegment ℝ (a k) (b k) := by simpa [hpb] using hpout.1
        exact (hendpoint_ne k) (right_mem_openSegment_iff.mp this)
      rcases hGammaInteriorEdges k hpk with ⟨s, hs, hpseg⟩
      have hp_not_vertices : p ∉ assembledVertices k := by
        intro hpmem
        rcases hassembledVertices_cases k hpmem with hpA | hpflat | hpB
        · exact hp_ne_a hpA
        · rcases hpflat with ⟨t, hpV⟩
          have hp_local_carrier : p ∈ (localArcAtParam k t).carrier :=
            PolygonalArcVertexMemCarrier (localArcAtParam k t) hpV
          have hp_closed :
              p ∈ Metric.closedBall (centerOfParam k t) (r (centerOfParam k t)) :=
            hlocalArcAtParam_closed k t hp_local_carrier
          exact hpout.2 (centerOfParam k t) (hcenterOfParam_T k t) hp_closed
        · exact hp_ne_b hpB
      have hp_ne_left : (assembledVertices k)[s] ≠ p := by
        intro heq
        apply hp_not_vertices
        rw [← heq]
        exact List.getElem_mem _
      have hp_ne_right : (assembledVertices k)[s + 1] ≠ p := by
        intro heq
        apply hp_not_vertices
        rw [← heq]
        exact List.getElem_mem _
      refine ⟨s, by simpa [hGamma_vertices k] using hs, ?_⟩
      have hpopen :
          p ∈ openSegment ℝ (assembledVertices k)[s]
            (assembledVertices k)[s + 1] :=
        mem_openSegment_of_ne_left_right hp_ne_left hp_ne_right hpseg
      simpa [hGamma_vertices k] using hpopen
    rcases outside_open_index i hpi houtside.1 with ⟨mi, hmi, hpmi⟩
    rcases outside_open_index j hpj houtside.2 with ⟨mj, hmj, hpmj⟩
    exact ⟨mi, mj, hmi, hmj, hpmi, hpmj⟩
  · rcases hlocal with ⟨z, ii, jj, hii, hjj, hpii, hpjj⟩
    have hij_inc : ii ≠ jj := by
      intro hijj
      apply hij
      have hval : ii.1 = jj.1 := congrArg Subtype.val hijj
      rwa [hii, hjj] at hval
    let C : OrdinaryCleanLocalCrossing (localXi z) ii jj p :=
      Classical.choice (hcleanLocal z hij_inc hpii hpjj)
    rcases hlocalArcRealize i z ii hii with ⟨ti, hlocalArc_i⟩
    rcases hlocalArcRealize j z jj hjj with ⟨tj, hlocalArc_j⟩
    have hmi' : C.firstIndex + 1 < (localArcAtParam i ti).vertices.length := by
      simpa [hlocalArc_i] using C.firstIndex_valid
    have hmj' : C.secondIndex + 1 < (localArcAtParam j tj).vertices.length := by
      simpa [hlocalArc_j] using C.secondIndex_valid
    have hti_attach : ti ∈ (centerParams i).attach := by simp
    have htj_attach : tj ∈ (centerParams j).attach := by simp
    rcases List.mem_iff_append.mp hti_attach with ⟨pre_i, post_i, hitems_i⟩
    rcases List.mem_iff_append.mp htj_attach with ⟨pre_j, post_j, hitems_j⟩
    rcases hlocalEdgeInAssembled i pre_i ti post_i C.firstIndex hitems_i hmi' with
      ⟨mi, hmi, hmi_left, hmi_right⟩
    rcases hlocalEdgeInAssembled j pre_j tj post_j C.secondIndex hitems_j hmj' with
      ⟨mj, hmj, hmj_left, hmj_right⟩
    refine ⟨mi, mj, by simpa [hGamma_vertices i] using hmi,
      by simpa [hGamma_vertices j] using hmj, ?_, ?_⟩
    · have hopen :
          p ∈ openSegment ℝ (assembledVertices i)[mi]
            (assembledVertices i)[mi + 1] := by
        simpa [hmi_left, hmi_right, hlocalArc_i] using C.first_open
      simpa [hGamma_vertices i] using hopen
    · have hopen :
          p ∈ openSegment ℝ (assembledVertices j)[mj]
            (assembledVertices j)[mj + 1] := by
        simpa [hmj_left, hmj_right, hlocalArc_j] using C.second_open
      simpa [hGamma_vertices j] using hopen

private lemma endpointUnitDiskAssembly_noTriple
    {ι : Type*} [Fintype ι]
    (a b : ι → EuclideanSpace ℝ (Fin 2))
    (T : Finset (EuclideanSpace ℝ (Fin 2)))
    (r : EuclideanSpace ℝ (Fin 2) → ℝ)
    (hT : ∀ z, z ∈ T ↔
      z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1 ∧
        ∃ i j k : ι,
          i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
            z ∈ openSegment ℝ (a i) (b i) ∧
              z ∈ openSegment ℝ (a j) (b j) ∧
                z ∈ openSegment ℝ (a k) (b k))
    (hrpos : ∀ z ∈ T, 0 < r z)
    (hdisjoint : ∀ ⦃z w : EuclideanSpace ℝ (Fin 2)⦄,
      z ∈ T → w ∈ T → z ≠ w →
        Disjoint (Metric.closedBall z (r z)) (Metric.closedBall w (r w)))
    (Gamma : ι → PolygonalArc)
    (localXi :
      ∀ z : endpointUnitDiskAssembly_center T,
        endpointUnitDiskAssembly_incident a b z.1 → PolygonalArc)
    (hsharedPointRoles :
      ∀ ⦃i j : ι⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        i ≠ j →
          p ∈ (Gamma i).relativeInterior →
            p ∈ (Gamma j).relativeInterior →
              ((p ∈ openSegment ℝ (a i) (b i) ∧
                    ∀ z : EuclideanSpace ℝ (Fin 2),
                      z ∈ T → p ∉ Metric.closedBall z (r z)) ∧
                  (p ∈ openSegment ℝ (a j) (b j) ∧
                    ∀ z : EuclideanSpace ℝ (Fin 2),
                      z ∈ T → p ∉ Metric.closedBall z (r z))) ∨
                (∃ (z : endpointUnitDiskAssembly_center T)
                    (ii jj : endpointUnitDiskAssembly_incident a b z.1),
                  ii.1 = i ∧ jj.1 = j ∧
                    p ∈ (localXi z ii).relativeInterior ∧
                      p ∈ (localXi z jj).relativeInterior))
    (hGamma_unitInterior :
      ∀ i, (Gamma i).relativeInterior ⊆
        Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1)
    (hlocalCarrierClosed :
      ∀ (z : endpointUnitDiskAssembly_center T)
          (ii : endpointUnitDiskAssembly_incident a b z.1),
        (localXi z ii).carrier ⊆ Metric.closedBall z.1 (r z.1))
    (hlocalInteriorBall :
      ∀ (z : endpointUnitDiskAssembly_center T)
          (ii : endpointUnitDiskAssembly_incident a b z.1),
        (localXi z ii).relativeInterior ⊆ Metric.ball z.1 (r z.1))
    (hlocalNoTriple :
      ∀ (z : endpointUnitDiskAssembly_center T)
          ⦃ii jj kk : endpointUnitDiskAssembly_incident a b z.1⦄
          ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        ii ≠ jj → ii ≠ kk → jj ≠ kk →
          p ∈ (localXi z ii).relativeInterior →
            p ∈ (localXi z jj).relativeInterior →
              p ∈ (localXi z kk).relativeInterior → False) :
    ∀ ⦃i j k : ι⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
      i ≠ j → i ≠ k → j ≠ k →
        p ∈ (Gamma i).relativeInterior →
          p ∈ (Gamma j).relativeInterior →
            p ∈ (Gamma k).relativeInterior → False := by
  intro i j k p hij hik hjk hpi hpj hpk
  rcases hsharedPointRoles hij hpi hpj with hij_outside | hij_local
  · rcases hsharedPointRoles hik hpi hpk with hik_outside | hik_local
    · have hp_unit : p ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1 :=
        hGamma_unitInterior i hpi
      rcases EndpointUnitDiskTriplePointInChosenDisk a b T r hT hrpos
          hp_unit hij hik hjk hij_outside.1.1 hij_outside.2.1
          hik_outside.2.1 with
        ⟨z, hzT, hpz⟩
      exact hij_outside.1.2 z hzT hpz
    · rcases hik_local with ⟨z, ii, kk, _hii, _hkk, _hpii, hpkk⟩
      have hp_ball : p ∈ Metric.ball z.1 (r z.1) :=
        hlocalInteriorBall z kk hpkk
      have hp_closed : p ∈ Metric.closedBall z.1 (r z.1) :=
        Metric.ball_subset_closedBall hp_ball
      exact hij_outside.1.2 z.1 z.2 hp_closed
  · rcases hsharedPointRoles hik hpi hpk with hik_outside | hik_local
    · rcases hij_local with ⟨z, ii, jj, _hii, _hjj, hpii, _hpjj⟩
      have hp_ball : p ∈ Metric.ball z.1 (r z.1) :=
        hlocalInteriorBall z ii hpii
      have hp_closed : p ∈ Metric.closedBall z.1 (r z.1) :=
        Metric.ball_subset_closedBall hp_ball
      exact hik_outside.1.2 z.1 z.2 hp_closed
    · rcases hij_local with ⟨z, ii, jj, hii, hjj, hpii, hpjj⟩
      rcases hik_local with ⟨w, ii', kk, hii', hkk, hpii', hpkk⟩
      have hzw_val : z.1 = w.1 :=
        EndpointUnitDiskLocalPiecesSameCenter T r hdisjoint z.2 w.2
          (hlocalCarrierClosed z ii) (hlocalCarrierClosed w ii') hpii hpii'
      have hzw : z = w := Subtype.ext hzw_val
      subst w
      have hii_ne_jj : ii ≠ jj := by
        intro h
        apply hij
        have hval : ii.1 = jj.1 := congrArg Subtype.val h
        rwa [hii, hjj] at hval
      have hii_ne_kk : ii ≠ kk := by
        intro h
        apply hik
        have hval : ii.1 = kk.1 := congrArg Subtype.val h
        rwa [hii, hkk] at hval
      have hjj_ne_kk : jj ≠ kk := by
        intro h
        apply hjk
        have hval : jj.1 = kk.1 := congrArg Subtype.val h
        rwa [hjj, hkk] at hval
      exact hlocalNoTriple z hii_ne_jj hii_ne_kk hjj_ne_kk hpii hpjj hpkk

private lemma endpointUnitDiskAssembly_clean
    {ι : Type*} [Fintype ι]
    (a b : ι → EuclideanSpace ℝ (Fin 2))
    (ha : ∀ i, dist (a i) (0 : EuclideanSpace ℝ (Fin 2)) = 1)
    (hb : ∀ i, dist (b i) (0 : EuclideanSpace ℝ (Fin 2)) = 1)
    (Gamma : ι → PolygonalArc)
    (hGamma_source : ∀ i, (Gamma i).source = a i)
    (hGamma_target : ∀ i, (Gamma i).target = b i)
    (hGamma_unitInterior :
      ∀ i, (Gamma i).relativeInterior ⊆
        Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1)
    (hsharedPointOpen :
      ∀ ⦃i j : ι⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        i ≠ j →
          p ∈ (Gamma i).relativeInterior →
            p ∈ (Gamma j).relativeInterior →
              ∃ m n : ℕ,
                ∃ (hm : m + 1 < (Gamma i).vertices.length)
                  (hn : n + 1 < (Gamma j).vertices.length),
                  p ∈ openSegment ℝ (Gamma i).vertices[m]
                      (Gamma i).vertices[m + 1] ∧
                    p ∈ openSegment ℝ (Gamma j).vertices[n]
                      (Gamma j).vertices[n + 1])
    (hsharedPointTransverse :
      ∀ ⦃i j : ι⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        i ≠ j →
          p ∈ (Gamma i).relativeInterior →
            p ∈ (Gamma j).relativeInterior →
              endpointUnitDiskAssembly_transverseWitness Gamma i j p)
    (hnoTriple :
      ∀ ⦃i j k : ι⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        i ≠ j → i ≠ k → j ≠ k →
          p ∈ (Gamma i).relativeInterior →
            p ∈ (Gamma j).relativeInterior →
              p ∈ (Gamma k).relativeInterior → False)
    (hsharedPointUnique :
      ∀ ⦃i j : ι⦄ ⦃p q : EuclideanSpace ℝ (Fin 2)⦄,
        i ≠ j →
          p ∈ (Gamma i).relativeInterior →
            p ∈ (Gamma j).relativeInterior →
              q ∈ (Gamma i).relativeInterior →
                q ∈ (Gamma j).relativeInterior →
                  p = q) :
    ∀ ⦃i j : ι⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
      i ≠ j →
        p ∈ (Gamma i).relativeInterior →
          p ∈ (Gamma j).relativeInterior →
            Nonempty (OrdinaryCleanLocalCrossing Gamma i j p) := by
  intro i j p hij hpi hpj
  rcases hsharedPointOpen hij hpi hpj with ⟨mi, mj, hmi, hmj, hpmi, hpmj⟩
  rcases hsharedPointTransverse hij hpi hpj with
    ⟨mi', mj', hmi', hmj', hpmi', hpmj', hnonparallel⟩
  have hmi_eq : mi = mi' :=
    endpointUnitDiskAssembly_indexUnique (Gamma i) p mi mi' hmi hmi' hpmi hpmi'
  have hmj_eq : mj = mj' :=
    endpointUnitDiskAssembly_indexUnique (Gamma j) p mj mj' hmj hmj' hpmj hpmj'
  subst mi'
  subst mj'
  have hp_unit : p ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1 :=
    hGamma_unitInterior i hpi
  rw [Metric.mem_ball] at hp_unit
  have hendpoint_free :
      ∀ k : ι, p ≠ (Gamma k).source ∧ p ≠ (Gamma k).target := by
    intro k
    constructor
    · intro hpsource
      have hdist : dist p (0 : EuclideanSpace ℝ (Fin 2)) = 1 := by
        rw [hpsource, hGamma_source k]
        exact ha k
      linarith
    · intro hptarget
      have hdist : dist p (0 : EuclideanSpace ℝ (Fin 2)) = 1 := by
        rw [hptarget, hGamma_target k]
        exact hb k
      linarith
  obtain ⟨C, _hfirst, _hsecond⟩ :=
    OrdinaryCleanLocalCrossingOfOpenSegments Gamma i j p hij hpi hpj
      hnoTriple hendpoint_free
      (fun q hqi hqj => hsharedPointUnique hij hqi hqj hpi hpj)
      mi mj hmi hmj hpmi hpmj hnonparallel
  exact ⟨C⟩

private lemma endpointUnitDiskAssembly_twoPointsAvoidFinset
    {p q : EuclideanSpace ℝ (Fin 2)} (hpq : p ≠ q)
    (F : Finset (EuclideanSpace ℝ (Fin 2))) :
    ∃ x y : EuclideanSpace ℝ (Fin 2),
      x ∈ openSegment ℝ p q ∧
        y ∈ openSegment ℝ p q ∧
          x ∉ F ∧ y ∉ F ∧ x ≠ y := by
  let f : ℝ → EuclideanSpace ℝ (Fin 2) := AffineMap.lineMap p q
  have hf : Function.Injective f :=
    AffineMap.lineMap_injective (k := ℝ) hpq
  let bad : Set ℝ := f ⁻¹' (F : Set (EuclideanSpace ℝ (Fin 2)))
  have hbad_finite : bad.Finite :=
    F.finite_toSet.preimage (fun a _ b _ hab => hf hab)
  have hIinf : (Set.Ioo (0 : ℝ) 1).Infinite :=
    Set.Ioo_infinite zero_lt_one
  have hgood1 : (Set.Ioo (0 : ℝ) 1 \ bad).Infinite :=
    hIinf.diff hbad_finite
  rcases hgood1.nonempty with ⟨t1, ht1⟩
  have hbad2_finite : (bad ∪ ({t1} : Set ℝ)).Finite :=
    hbad_finite.union (Set.finite_singleton t1)
  have hgood2 : (Set.Ioo (0 : ℝ) 1 \ (bad ∪ ({t1} : Set ℝ))).Infinite :=
    hIinf.diff hbad2_finite
  rcases hgood2.nonempty with ⟨t2, ht2⟩
  refine ⟨f t1, f t2, ?_, ?_, ?_, ?_, ?_⟩
  · exact lineMap_mem_openSegment ℝ p q ht1.1
  · exact lineMap_mem_openSegment ℝ p q ht2.1
  · intro hxF
    exact ht1.2 hxF
  · intro hyF
    exact ht2.2 (Or.inl hyF)
  · intro hxy
    have ht12 : t1 = t2 := hf hxy
    exact ht2.2 (Or.inr (by simp [ht12]))

private lemma endpointUnitDiskAssembly_noCommonSegment
    {ι : Type*} [Fintype ι]
    (Gamma : ι → PolygonalArc)
    (hsharedPointUnique :
      ∀ ⦃i j : ι⦄ ⦃p q : EuclideanSpace ℝ (Fin 2)⦄,
        i ≠ j →
          p ∈ (Gamma i).relativeInterior →
            p ∈ (Gamma j).relativeInterior →
              q ∈ (Gamma i).relativeInterior →
                q ∈ (Gamma j).relativeInterior →
                  p = q) :
    ∀ ⦃i j : ι⦄,
      i ≠ j →
        ¬ ∃ m n : ℕ,
          ∃ (hm : m + 1 < (Gamma i).vertices.length)
            (hn : n + 1 < (Gamma j).vertices.length),
            ∃ p q : EuclideanSpace ℝ (Fin 2),
              p ≠ q ∧
                segment ℝ p q ⊆
                  segment ℝ (Gamma i).vertices[m] (Gamma i).vertices[m + 1] ∩
                    segment ℝ (Gamma j).vertices[n] (Gamma j).vertices[n + 1] := by
  intro i j hij hcommon
  rcases hcommon with ⟨m, n, hm, hn, p, q, hpq, hseg_subset⟩
  let forbidden : Finset (EuclideanSpace ℝ (Fin 2)) :=
    {(Gamma i).source, (Gamma i).target, (Gamma j).source, (Gamma j).target}
  rcases endpointUnitDiskAssembly_twoPointsAvoidFinset hpq forbidden with
    ⟨x, y, hx_open, hy_open, hx_not_forbidden, hy_not_forbidden, hxy⟩
  have hx_seg_pq : x ∈ segment ℝ p q :=
    openSegment_subset_segment ℝ p q hx_open
  have hy_seg_pq : y ∈ segment ℝ p q :=
    openSegment_subset_segment ℝ p q hy_open
  have hx_edges := hseg_subset hx_seg_pq
  have hy_edges := hseg_subset hy_seg_pq
  have hx_not_end_i :
      x ∉ ({(Gamma i).source, (Gamma i).target} :
        Set (EuclideanSpace ℝ (Fin 2))) := by
    intro hxend
    apply hx_not_forbidden
    simp at hxend
    rcases hxend with hxsource | hxtarget
    · simp [forbidden, hxsource]
    · simp [forbidden, hxtarget]
  have hx_not_end_j :
      x ∉ ({(Gamma j).source, (Gamma j).target} :
        Set (EuclideanSpace ℝ (Fin 2))) := by
    intro hxend
    apply hx_not_forbidden
    simp at hxend
    rcases hxend with hxsource | hxtarget
    · simp [forbidden, hxsource]
    · simp [forbidden, hxtarget]
  have hy_not_end_i :
      y ∉ ({(Gamma i).source, (Gamma i).target} :
        Set (EuclideanSpace ℝ (Fin 2))) := by
    intro hyend
    apply hy_not_forbidden
    simp at hyend
    rcases hyend with hysource | hytarget
    · simp [forbidden, hysource]
    · simp [forbidden, hytarget]
  have hy_not_end_j :
      y ∉ ({(Gamma j).source, (Gamma j).target} :
        Set (EuclideanSpace ℝ (Fin 2))) := by
    intro hyend
    apply hy_not_forbidden
    simp at hyend
    rcases hyend with hysource | hytarget
    · simp [forbidden, hysource]
    · simp [forbidden, hytarget]
  have hx_carrier_i : x ∈ (Gamma i).carrier := by
    rw [(Gamma i).carrier_eq]
    exact ⟨m, hm, hx_edges.1⟩
  have hx_carrier_j : x ∈ (Gamma j).carrier := by
    rw [(Gamma j).carrier_eq]
    exact ⟨n, hn, hx_edges.2⟩
  have hy_carrier_i : y ∈ (Gamma i).carrier := by
    rw [(Gamma i).carrier_eq]
    exact ⟨m, hm, hy_edges.1⟩
  have hy_carrier_j : y ∈ (Gamma j).carrier := by
    rw [(Gamma j).carrier_eq]
    exact ⟨n, hn, hy_edges.2⟩
  have hx_rel_i : x ∈ (Gamma i).relativeInterior := by
    rw [(Gamma i).relativeInterior_eq]
    exact ⟨hx_carrier_i, hx_not_end_i⟩
  have hx_rel_j : x ∈ (Gamma j).relativeInterior := by
    rw [(Gamma j).relativeInterior_eq]
    exact ⟨hx_carrier_j, hx_not_end_j⟩
  have hy_rel_i : y ∈ (Gamma i).relativeInterior := by
    rw [(Gamma i).relativeInterior_eq]
    exact ⟨hy_carrier_i, hy_not_end_i⟩
  have hy_rel_j : y ∈ (Gamma j).relativeInterior := by
    rw [(Gamma j).relativeInterior_eq]
    exact ⟨hy_carrier_j, hy_not_end_j⟩
  exact hxy (hsharedPointUnique hij hx_rel_i hx_rel_j hy_rel_i hy_rel_j)

private lemma endpointUnitDiskAssembly_finish
    {ι : Type*} [Fintype ι]
    (a b : ι → EuclideanSpace ℝ (Fin 2))
    (Gamma : ι → PolygonalArc)
    (hGammaProperties :
      ∀ i,
        (Gamma i).source = a i ∧
          (Gamma i).target = b i ∧
            (Gamma i).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ∧
              (Gamma i).relativeInterior ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1)
    (hnoCommonSegment :
      ∀ ⦃i j : ι⦄,
        i ≠ j →
          ¬ ∃ m n : ℕ,
            ∃ (hm : m + 1 < (Gamma i).vertices.length)
              (hn : n + 1 < (Gamma j).vertices.length),
              ∃ p q : EuclideanSpace ℝ (Fin 2),
                p ≠ q ∧
                  segment ℝ p q ⊆
                    segment ℝ (Gamma i).vertices[m] (Gamma i).vertices[m + 1] ∩
                      segment ℝ (Gamma j).vertices[n] (Gamma j).vertices[n + 1])
    (hnoTriple :
      ∀ ⦃i j k : ι⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        i ≠ j → i ≠ k → j ≠ k →
          p ∈ (Gamma i).relativeInterior →
            p ∈ (Gamma j).relativeInterior →
              p ∈ (Gamma k).relativeInterior → False)
    (hsharedPointTransverse :
      ∀ ⦃i j : ι⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        i ≠ j →
          p ∈ (Gamma i).relativeInterior →
            p ∈ (Gamma j).relativeInterior →
              endpointUnitDiskAssembly_transverseWitness Gamma i j p)
    (hsharedPointUnique :
      ∀ ⦃i j : ι⦄ ⦃p q : EuclideanSpace ℝ (Fin 2)⦄,
        i ≠ j →
          p ∈ (Gamma i).relativeInterior →
            p ∈ (Gamma j).relativeInterior →
              q ∈ (Gamma i).relativeInterior →
                q ∈ (Gamma j).relativeInterior →
                  p = q)
    (hclean :
      ∀ ⦃i j : ι⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        i ≠ j →
          p ∈ (Gamma i).relativeInterior →
            p ∈ (Gamma j).relativeInterior →
              Nonempty (OrdinaryCleanLocalCrossing Gamma i j p)) :
    (∀ i,
      (Gamma i).source = a i ∧
        (Gamma i).target = b i ∧
          (Gamma i).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ∧
            (Gamma i).relativeInterior ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1) ∧
      (∀ ⦃i j : ι⦄,
        i ≠ j →
          ¬ ∃ m n : ℕ,
            ∃ (hm : m + 1 < (Gamma i).vertices.length)
              (hn : n + 1 < (Gamma j).vertices.length),
              ∃ p q : EuclideanSpace ℝ (Fin 2),
                p ≠ q ∧
                  segment ℝ p q ⊆
                    segment ℝ (Gamma i).vertices[m] (Gamma i).vertices[m + 1] ∩
                      segment ℝ (Gamma j).vertices[n] (Gamma j).vertices[n + 1]) ∧
        (∀ ⦃i j k : ι⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
          i ≠ j → i ≠ k → j ≠ k →
            p ∈ (Gamma i).relativeInterior →
              p ∈ (Gamma j).relativeInterior →
                p ∈ (Gamma k).relativeInterior → False) ∧
        (∀ ⦃i j : ι⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
          i ≠ j →
            p ∈ (Gamma i).relativeInterior →
              p ∈ (Gamma j).relativeInterior →
                endpointUnitDiskAssembly_transverseWitness Gamma i j p) ∧
        (∀ ⦃i j : ι⦄ ⦃p q : EuclideanSpace ℝ (Fin 2)⦄,
          i ≠ j →
            p ∈ (Gamma i).relativeInterior →
              p ∈ (Gamma j).relativeInterior →
                q ∈ (Gamma i).relativeInterior →
                  q ∈ (Gamma j).relativeInterior →
                    p = q) ∧
        (∀ ⦃i j : ι⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
          i ≠ j →
            p ∈ (Gamma i).relativeInterior →
              p ∈ (Gamma j).relativeInterior →
                Nonempty (OrdinaryCleanLocalCrossing Gamma i j p)) := by
  exact ⟨hGammaProperties, hnoCommonSegment, hnoTriple,
    hsharedPointTransverse, hsharedPointUnique, hclean⟩

private lemma endpointUnitDiskAssembly_finalPointRoles
    {ι : Type*} [Fintype ι]
    (a b : ι → EuclideanSpace ℝ (Fin 2))
    (ha : ∀ i, dist (a i) (0 : EuclideanSpace ℝ (Fin 2)) = 1)
    (hb : ∀ i, dist (b i) (0 : EuclideanSpace ℝ (Fin 2)) = 1)
    (T : Finset (EuclideanSpace ℝ (Fin 2)))
    (r : EuclideanSpace ℝ (Fin 2) → ℝ)
    (hT : ∀ z, z ∈ T ↔
      z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1 ∧
        ∃ i j k : ι,
          i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
            z ∈ openSegment ℝ (a i) (b i) ∧
              z ∈ openSegment ℝ (a j) (b j) ∧
                z ∈ openSegment ℝ (a k) (b k))
    (hmiss : ∀ ⦃z : EuclideanSpace ℝ (Fin 2)⦄,
      z ∈ T → ∀ i,
        z ∉ segment ℝ (a i) (b i) →
          Disjoint (Metric.closedBall z (r z)) (segment ℝ (a i) (b i)))
    (centerParams : ι → List ℝ)
    (centerOfParam :
      ∀ i, {t : ℝ // t ∈ centerParams i} → EuclideanSpace ℝ (Fin 2))
    (localArcAtParam :
      ∀ i, {t : ℝ // t ∈ centerParams i} → PolygonalArc)
    (entryPoint exitPoint :
      ∀ i, {t : ℝ // t ∈ centerParams i} → EuclideanSpace ℝ (Fin 2))
    (assembledVertices : ι → List (EuclideanSpace ℝ (Fin 2)))
    (assembledEdgeSet : ι → Set (EuclideanSpace ℝ (Fin 2)))
    (hassembledEdgeSet_mem :
      ∀ i p,
        p ∈ assembledEdgeSet i ↔
          ∃ m : ℕ, ∃ hm : m + 1 < (assembledVertices i).length,
            p ∈ segment ℝ (assembledVertices i)[m]
              (assembledVertices i)[m + 1])
    (Gamma : ι → PolygonalArc)
    (hGamma_relativeInterior :
      ∀ i, (Gamma i).relativeInterior =
        assembledEdgeSet i \ ({a i, b i} : Set (EuclideanSpace ℝ (Fin 2))))
    (hassembledEdgeEndpointRoles :
      ∀ i ⦃m : ℕ⦄,
        (hm : m + 1 < (assembledVertices i).length) →
          ((centerParams i).attach = [] ∧
              (assembledVertices i)[m] = a i ∧
                (assembledVertices i)[m + 1] = b i) ∨
            endpointUnitDiskAssembly_nonemptyRole a b centerParams
              localArcAtParam assembledVertices i m hm)
    (hcenterParams_mem :
      ∀ i t,
        t ∈ centerParams i ↔
          0 < t ∧ t < 1 ∧ AffineMap.lineMap (a i) (b i) t ∈ T)
    (hlocalArcAtParam_props :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}),
        (localArcAtParam i t).source = entryPoint i t ∧
          (localArcAtParam i t).target = exitPoint i t ∧
            (localArcAtParam i t).carrier ⊆
              Metric.closedBall (centerOfParam i t) (r (centerOfParam i t)) ∧
              (localArcAtParam i t).relativeInterior ⊆
                Metric.ball (centerOfParam i t) (r (centerOfParam i t)))
    (hentry_exit_local :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}),
        entryPoint i t ∈ Metric.sphere (centerOfParam i t) (r (centerOfParam i t)) ∧
          exitPoint i t ∈ Metric.sphere (centerOfParam i t) (r (centerOfParam i t)) ∧
            entryPoint i t ∈ openSegment ℝ (a i) (centerOfParam i t) ∧
              exitPoint i t ∈ openSegment ℝ (centerOfParam i t) (b i) ∧
                Metric.closedBall (centerOfParam i t) (r (centerOfParam i t)) ∩
                    segment ℝ (a i) (b i) =
                  segment ℝ (entryPoint i t) (exitPoint i t))
    (hentryPoint_open_chord :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}),
        entryPoint i t ∈ openSegment ℝ (a i) (b i))
    (hexitPoint_open_chord :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}),
        exitPoint i t ∈ openSegment ℝ (a i) (b i))
    (hchosenCenterOnChord_param :
      ∀ i ⦃z : EuclideanSpace ℝ (Fin 2)⦄,
        z ∈ T →
          z ∈ segment ℝ (a i) (b i) →
            ∃ t : {t : ℝ // t ∈ centerParams i}, centerOfParam i t = z)
    (hentryExitParameters :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}),
        (∃ s : ℝ, 0 < s ∧ s < t.1 ∧
          entryPoint i t = AffineMap.lineMap (a i) (b i) s) ∧
          (∃ s : ℝ, t.1 < s ∧ s < 1 ∧
            exitPoint i t = AffineMap.lineMap (a i) (b i) s))
    (horderedCutSeparation :
      ∀ i (t1 t2 : {t : ℝ // t ∈ centerParams i}),
        t1.1 < t2.1 →
          ∃ sExit sEntry : ℝ,
            t1.1 < sExit ∧
              sExit < sEntry ∧
                sEntry < t2.1 ∧
                  exitPoint i t1 = AffineMap.lineMap (a i) (b i) sExit ∧
                    entryPoint i t2 = AffineMap.lineMap (a i) (b i) sEntry)
    (hattach_pairwise_lt_all :
      ∀ i,
        (centerParams i).attach.Pairwise
          (fun t1 t2 : {t : ℝ // t ∈ centerParams i} => t1.1 < t2.1))
    (hendpoint_ne : ∀ i, a i ≠ b i)
    (hchordGapDiskPosition :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}) {α β e x : ℝ},
        entryPoint i t = AffineMap.lineMap (a i) (b i) e →
          exitPoint i t = AffineMap.lineMap (a i) (b i) x →
            0 ≤ α → α ≤ β → β ≤ 1 → e < x →
              (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
                p ∈ segment ℝ (AffineMap.lineMap (a i) (b i) α)
                    (AffineMap.lineMap (a i) (b i) β) →
                  p ∈ Metric.closedBall (centerOfParam i t) (r (centerOfParam i t)) →
                    β < e → False) ∧
                (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
                  p ∈ segment ℝ (AffineMap.lineMap (a i) (b i) α)
                      (AffineMap.lineMap (a i) (b i) β) →
                    p ∈ Metric.closedBall (centerOfParam i t) (r (centerOfParam i t)) →
                      β = e → p = entryPoint i t) ∧
                  (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
                    p ∈ segment ℝ (AffineMap.lineMap (a i) (b i) α)
                        (AffineMap.lineMap (a i) (b i) β) →
                      p ∈ Metric.closedBall (centerOfParam i t) (r (centerOfParam i t)) →
                        x < α → False) ∧
                    (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
                      p ∈ segment ℝ (AffineMap.lineMap (a i) (b i) α)
                          (AffineMap.lineMap (a i) (b i) β) →
                        p ∈ Metric.closedBall (centerOfParam i t) (r (centerOfParam i t)) →
                          x = α → p = exitPoint i t)) :
    ∀ i ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
      p ∈ (Gamma i).relativeInterior →
        (p ∈ openSegment ℝ (a i) (b i) ∧
            ∀ z : EuclideanSpace ℝ (Fin 2),
              z ∈ T → p ∉ Metric.closedBall z (r z)) ∨
          (∃ t : {t : ℝ // t ∈ centerParams i},
            p ∈ (localArcAtParam i t).relativeInterior ∧
              p ∈ Metric.ball (centerOfParam i t) (r (centerOfParam i t))) ∨
            (∃ t : {t : ℝ // t ∈ centerParams i},
              (p = entryPoint i t ∧
                  p ∈ Metric.sphere (centerOfParam i t) (r (centerOfParam i t)) ∧
                    p ∈ openSegment ℝ (a i) (b i)) ∨
                (p = exitPoint i t ∧
                  p ∈ Metric.sphere (centerOfParam i t) (r (centerOfParam i t)) ∧
                    p ∈ openSegment ℝ (a i) (b i))) := by
  intro i p hp
  have hp_rel := hp
  rw [hGamma_relativeInterior i] at hp_rel
  have hp_edge : p ∈ assembledEdgeSet i := hp_rel.1
  have hp_ne_a : p ≠ a i := by
    intro hp_eq
    exact hp_rel.2 (by simp [hp_eq])
  have hp_ne_b : p ≠ b i := by
    intro hp_eq
    exact hp_rel.2 (by simp [hp_eq])
  rw [hassembledEdgeSet_mem i p] at hp_edge
  rcases hp_edge with ⟨m, hm, hpseg⟩
  rcases hassembledEdgeEndpointRoles i hm with hnodisks | hroles
  · rcases hnodisks with ⟨hitems, hleft, hright⟩
    left
    have hpseg_chord : p ∈ segment ℝ (a i) (b i) := by
      simpa [hleft, hright] using hpseg
    refine ⟨mem_openSegment_of_ne_left_right (𝕜 := ℝ)
      hp_ne_a.symm hp_ne_b.symm hpseg_chord, ?_⟩
    intro z hzT hpz
    by_cases hzseg : z ∈ segment ℝ (a i) (b i)
    · have hz_unit :
          z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1 :=
        ((hT z).1 hzT).1
      have hz_dist : dist z (0 : EuclideanSpace ℝ (Fin 2)) < 1 := by
        simpa [Metric.mem_ball] using hz_unit
      have hz_ne_a : z ≠ a i := by
        intro hz_eq
        subst z
        linarith [ha i]
      have hz_ne_b : z ≠ b i := by
        intro hz_eq
        subst z
        linarith [hb i]
      have hzopen : z ∈ openSegment ℝ (a i) (b i) :=
        mem_openSegment_of_ne_left_right (𝕜 := ℝ)
          hz_ne_a.symm hz_ne_b.symm hzseg
      rw [openSegment_eq_image_lineMap] at hzopen
      rcases hzopen with ⟨s, hs, hzs⟩
      have hs_mem : s ∈ centerParams i := by
        exact (hcenterParams_mem i s).2
          ⟨hs.1, hs.2, by simpa [hzs] using hzT⟩
      have hs_attach : (⟨s, hs_mem⟩ : {t : ℝ // t ∈ centerParams i}) ∈
          (centerParams i).attach := by
        simp
      simpa [hitems] using hs_attach
    · have hdis :
          Disjoint (Metric.closedBall z (r z)) (segment ℝ (a i) (b i)) :=
        hmiss hzT i hzseg
      exact (Set.disjoint_left.mp hdis) hpz hpseg_chord
  rcases hroles with hinitial | hroles
  · rcases hinitial with ⟨t, ts, X, hitems, hhead, hleft, hright⟩
    have hsource_entry :
        (localArcAtParam i t).vertices.head? = some (entryPoint i t) := by
      have hsource := (localArcAtParam i t).source_eq_head
      rw [(hlocalArcAtParam_props i t).1] at hsource
      exact hsource
    have hX : X = entryPoint i t := by
      exact (Option.some.inj (hsource_entry.symm.trans hhead)).symm
    have hpseg_gap : p ∈ segment ℝ (a i) (entryPoint i t) := by
      simpa [hleft, hright, hX] using hpseg
    by_cases hp_entry : p = entryPoint i t
    · right
      right
      refine ⟨t, Or.inl ⟨hp_entry, ?_, ?_⟩⟩
      · simpa [hp_entry] using (hentry_exit_local i t).1
      · simpa [hp_entry] using hentryPoint_open_chord i t
    · left
      have hentry_chord :
          entryPoint i t ∈ segment ℝ (a i) (b i) :=
        openSegment_subset_segment ℝ (a i) (b i)
          (hentryPoint_open_chord i t)
      have hpseg_chord : p ∈ segment ℝ (a i) (b i) :=
        (convex_segment (a i) (b i)).segment_subset
          (left_mem_segment ℝ (a i) (b i)) hentry_chord hpseg_gap
      refine ⟨mem_openSegment_of_ne_left_right (𝕜 := ℝ)
        hp_ne_a.symm hp_ne_b.symm hpseg_chord, ?_⟩
      intro z hzT hpz
      by_cases hzseg : z ∈ segment ℝ (a i) (b i)
      · rcases hchosenCenterOnChord_param i hzT hzseg with ⟨tz, htz_center⟩
        have htz_attach : tz ∈ (centerParams i).attach := by
          simp
        have htz_cases : tz = t ∨ tz ∈ ts := by
          simpa [hitems] using htz_attach
        rcases hentryExitParameters i t with
          ⟨⟨e, he_pos, he_lt_t, hentry⟩,
            ⟨x, ht_lt_x, hx_lt_one, hexit⟩⟩
        have hpseg_param :
            p ∈ segment ℝ (AffineMap.lineMap (a i) (b i) (0 : ℝ))
                (AffineMap.lineMap (a i) (b i) e) := by
          simpa [hentry] using hpseg_gap
        rcases htz_cases with htz_eq | htz_tail
        · subst tz
          have hpz_t :
              p ∈ Metric.closedBall (centerOfParam i t) (r (centerOfParam i t)) := by
            simpa [htz_center] using hpz
          have hp_eq_entry :
              p = entryPoint i t :=
            (hchordGapDiskPosition i t
              (α := (0 : ℝ)) (β := e) (e := e) (x := x)
              hentry hexit (by norm_num) (le_of_lt he_pos)
              (by linarith) (by linarith)).2.1
                hpseg_param hpz_t rfl
          exact hp_entry hp_eq_entry
        · have ht_lt_tz : t.1 < tz.1 := by
            have hpair := hattach_pairwise_lt_all i
            rw [hitems] at hpair
            exact (List.pairwise_cons.1 hpair).1 tz htz_tail
          rcases hentryExitParameters i tz with
            ⟨⟨ez, hez_pos, hez_lt_tz, hentryz⟩,
              ⟨xz, htz_lt_xz, hxz_lt_one, hexitz⟩⟩
          rcases horderedCutSeparation i t tz ht_lt_tz with
            ⟨sExit, sEntry, _ht_sExit, _hsExitEntry, _hsEntry_tz,
              _hexit_order, hentry_order⟩
          let f : ℝ →ᵃ[ℝ] EuclideanSpace ℝ (Fin 2) :=
            AffineMap.lineMap (a i) (b i)
          have hf : Function.Injective f :=
            AffineMap.lineMap_injective (k := ℝ) (hendpoint_ne i)
          have hez_eq : ez = sEntry := by
            exact hf (by rw [← hentryz, ← hentry_order])
          have he_lt_ez : e < ez := by
            linarith
          have hpz_tz :
              p ∈ Metric.closedBall (centerOfParam i tz)
                  (r (centerOfParam i tz)) := by
            simpa [htz_center] using hpz
          exact (hchordGapDiskPosition i tz
            (α := (0 : ℝ)) (β := e) (e := ez) (x := xz)
            hentryz hexitz (by norm_num) (le_of_lt he_pos)
            (by linarith) (by linarith)).1
              hpseg_param hpz_tz he_lt_ez
      · have hdis :
            Disjoint (Metric.closedBall z (r z)) (segment ℝ (a i) (b i)) :=
          hmiss hzT i hzseg
        exact (Set.disjoint_left.mp hdis) hpz hpseg_chord
  rcases hroles with hlocal | hroles
  · rcases hlocal with ⟨_pre, t, _post, q, hq, _hitems, hleft, hright⟩
    have hpseg_local :
        p ∈ segment ℝ (localArcAtParam i t).vertices[q]
            (localArcAtParam i t).vertices[q + 1] := by
      simpa [hleft, hright] using hpseg
    have hp_carrier : p ∈ (localArcAtParam i t).carrier := by
      rw [(localArcAtParam i t).carrier_eq]
      exact ⟨q, hq, hpseg_local⟩
    by_cases hp_entry : p = entryPoint i t
    · right
      right
      refine ⟨t, Or.inl ⟨hp_entry, ?_, ?_⟩⟩
      · simpa [hp_entry] using (hentry_exit_local i t).1
      · simpa [hp_entry] using hentryPoint_open_chord i t
    · by_cases hp_exit : p = exitPoint i t
      · right
        right
        refine ⟨t, Or.inr ⟨hp_exit, ?_, ?_⟩⟩
        · simpa [hp_exit] using (hentry_exit_local i t).2.1
        · simpa [hp_exit] using hexitPoint_open_chord i t
      · right
        left
        refine ⟨t, ?_, (hlocalArcAtParam_props i t).2.2.2 ?_⟩
        · rw [(localArcAtParam i t).relativeInterior_eq]
          refine ⟨hp_carrier, ?_⟩
          intro hp_end
          have hp_end' :
              p = entryPoint i t ∨ p = exitPoint i t := by
            simpa [(hlocalArcAtParam_props i t).1,
              (hlocalArcAtParam_props i t).2.1] using hp_end
          rcases hp_end' with hp_end_entry | hp_end_exit
          · exact hp_entry hp_end_entry
          · exact hp_exit hp_end_exit
        · rw [(localArcAtParam i t).relativeInterior_eq]
          refine ⟨hp_carrier, ?_⟩
          intro hp_end
          have hp_end' :
              p = entryPoint i t ∨ p = exitPoint i t := by
            simpa [(hlocalArcAtParam_props i t).1,
              (hlocalArcAtParam_props i t).2.1] using hp_end
          rcases hp_end' with hp_end_entry | hp_end_exit
          · exact hp_entry hp_end_entry
          · exact hp_exit hp_end_exit
  rcases hroles with hbridge | hterminal
  · rcases hbridge with ⟨pre, t1, t2, post, X, Y, hitems, hlast, hhead,
      hleft, hright⟩
    have hlast_exit :
        (localArcAtParam i t1).vertices.getLast? = some (exitPoint i t1) := by
      have htarget := (localArcAtParam i t1).target_eq_last
      rw [(hlocalArcAtParam_props i t1).2.1] at htarget
      exact htarget
    have hX : X = exitPoint i t1 := by
      exact (Option.some.inj (hlast_exit.symm.trans hlast)).symm
    have hhead_entry :
        (localArcAtParam i t2).vertices.head? = some (entryPoint i t2) := by
      have hsource := (localArcAtParam i t2).source_eq_head
      rw [(hlocalArcAtParam_props i t2).1] at hsource
      exact hsource
    have hY : Y = entryPoint i t2 := by
      exact (Option.some.inj (hhead_entry.symm.trans hhead)).symm
    have hpseg_gap : p ∈ segment ℝ (exitPoint i t1) (entryPoint i t2) := by
      simpa [hleft, hright, hX, hY] using hpseg
    by_cases hp_exit : p = exitPoint i t1
    · right
      right
      refine ⟨t1, Or.inr ⟨hp_exit, ?_, ?_⟩⟩
      · simpa [hp_exit] using (hentry_exit_local i t1).2.1
      · simpa [hp_exit] using hexitPoint_open_chord i t1
    · by_cases hp_entry : p = entryPoint i t2
      · right
        right
        refine ⟨t2, Or.inl ⟨hp_entry, ?_, ?_⟩⟩
        · simpa [hp_entry] using (hentry_exit_local i t2).1
        · simpa [hp_entry] using hentryPoint_open_chord i t2
      · left
        have hexit_chord :
            exitPoint i t1 ∈ segment ℝ (a i) (b i) :=
          openSegment_subset_segment ℝ (a i) (b i)
            (hexitPoint_open_chord i t1)
        have hentry_chord :
            entryPoint i t2 ∈ segment ℝ (a i) (b i) :=
          openSegment_subset_segment ℝ (a i) (b i)
            (hentryPoint_open_chord i t2)
        have hpseg_chord : p ∈ segment ℝ (a i) (b i) :=
          (convex_segment (a i) (b i)).segment_subset
            hexit_chord hentry_chord hpseg_gap
        refine ⟨mem_openSegment_of_ne_left_right (𝕜 := ℝ)
          hp_ne_a.symm hp_ne_b.symm hpseg_chord, ?_⟩
        intro z hzT hpz
        by_cases hzseg : z ∈ segment ℝ (a i) (b i)
        · rcases hchosenCenterOnChord_param i hzT hzseg with ⟨tz, htz_center⟩
          have htz_attach : tz ∈ (centerParams i).attach := by
            simp
          have htz_decomp :
              tz ∈ pre ∨ tz = t1 ∨ tz = t2 ∨ tz ∈ post := by
            have hmem : tz ∈ pre ++ t1 :: t2 :: post := by
              simpa [hitems] using htz_attach
            simpa [List.mem_append, List.mem_cons] using hmem
          have hpair_bridge := hattach_pairwise_lt_all i
          rw [hitems] at hpair_bridge
          have htail_pair :
              (t1 :: t2 :: post).Pairwise
                (fun u v : {t : ℝ // t ∈ centerParams i} => u.1 < v.1) :=
            (List.pairwise_append.1 hpair_bridge).2.1
          have ht12 : t1.1 < t2.1 :=
            (List.pairwise_cons.1 htail_pair).1 t2 (by simp)
          rcases hentryExitParameters i t1 with
            ⟨⟨e1, he1_pos, he1_lt_t1, hentry1⟩,
              ⟨x1, ht1_lt_x1, hx1_lt_one, hexit1⟩⟩
          rcases hentryExitParameters i t2 with
            ⟨⟨e2, he2_pos, he2_lt_t2, hentry2⟩,
              ⟨x2, ht2_lt_x2, hx2_lt_one, hexit2⟩⟩
          rcases horderedCutSeparation i t1 t2 ht12 with
            ⟨sExit, sEntry, _ht1_sExit, hsExitEntry, _hsEntry_t2,
              hexit_order, hentry_order⟩
          let f : ℝ →ᵃ[ℝ] EuclideanSpace ℝ (Fin 2) :=
            AffineMap.lineMap (a i) (b i)
          have hf : Function.Injective f :=
            AffineMap.lineMap_injective (k := ℝ) (hendpoint_ne i)
          have hx1_eq : x1 = sExit := by
            exact hf (by rw [← hexit1, ← hexit_order])
          have he2_eq : e2 = sEntry := by
            exact hf (by rw [← hentry2, ← hentry_order])
          have hx1_lt_e2 : x1 < e2 := by
            linarith
          have hpseg_param :
              p ∈ segment ℝ (AffineMap.lineMap (a i) (b i) x1)
                  (AffineMap.lineMap (a i) (b i) e2) := by
            simpa [hexit1, hentry2] using hpseg_gap
          rcases htz_decomp with htz_pre | htz_decomp
          · have htz_lt_t1 : tz.1 < t1.1 :=
              (List.pairwise_append.1 hpair_bridge).2.2 tz htz_pre t1 (by simp)
            rcases hentryExitParameters i tz with
              ⟨⟨ez, hez_pos, hez_lt_tz, hentryz⟩,
                ⟨xz, htz_lt_xz, hxz_lt_one, hexitz⟩⟩
            rcases horderedCutSeparation i tz t1 htz_lt_t1 with
              ⟨sExit', sEntry', _htz_sExit', _hsExitEntry',
                _hsEntry_t1, hexit_order', hentry_order'⟩
            have hxz_eq : xz = sExit' := by
              exact hf (by rw [← hexitz, ← hexit_order'])
            have he1_eq : e1 = sEntry' := by
              exact hf (by rw [← hentry1, ← hentry_order'])
            have hxz_lt_x1 : xz < x1 := by
              linarith
            have hpz_tz :
                p ∈ Metric.closedBall (centerOfParam i tz)
                    (r (centerOfParam i tz)) := by
              simpa [htz_center] using hpz
            exact (hchordGapDiskPosition i tz
              (α := x1) (β := e2) (e := ez) (x := xz)
              hentryz hexitz (by linarith) (le_of_lt hx1_lt_e2)
              (by linarith) (by linarith)).2.2.1
                hpseg_param hpz_tz hxz_lt_x1
          rcases htz_decomp with htz_eq1 | htz_decomp
          · subst tz
            have hpz_t1 :
                p ∈ Metric.closedBall (centerOfParam i t1)
                    (r (centerOfParam i t1)) := by
              simpa [htz_center] using hpz
            have hp_eq_exit :
                p = exitPoint i t1 :=
              (hchordGapDiskPosition i t1
                (α := x1) (β := e2) (e := e1) (x := x1)
                hentry1 hexit1 (by linarith) (le_of_lt hx1_lt_e2)
                (by linarith) (by linarith)).2.2.2
                  hpseg_param hpz_t1 rfl
            exact hp_exit hp_eq_exit
          rcases htz_decomp with htz_eq2 | htz_post
          · subst tz
            have hpz_t2 :
                p ∈ Metric.closedBall (centerOfParam i t2)
                    (r (centerOfParam i t2)) := by
              simpa [htz_center] using hpz
            have hp_eq_entry :
                p = entryPoint i t2 :=
              (hchordGapDiskPosition i t2
                (α := x1) (β := e2) (e := e2) (x := x2)
                hentry2 hexit2 (by linarith) (le_of_lt hx1_lt_e2)
                (by linarith) (by linarith)).2.1
                  hpseg_param hpz_t2 rfl
            exact hp_entry hp_eq_entry
          · have hprefix_pair :
                ((pre ++ [t1, t2]) ++ post).Pairwise
                  (fun u v : {t : ℝ // t ∈ centerParams i} => u.1 < v.1) := by
              simpa [List.append_assoc] using hpair_bridge
            have ht2_lt_tz : t2.1 < tz.1 :=
              (List.pairwise_append.1 hprefix_pair).2.2 t2 (by simp) tz htz_post
            rcases hentryExitParameters i tz with
              ⟨⟨ez, hez_pos, hez_lt_tz, hentryz⟩,
                ⟨xz, htz_lt_xz, hxz_lt_one, hexitz⟩⟩
            rcases horderedCutSeparation i t2 tz ht2_lt_tz with
              ⟨sExit', sEntry', _ht2_sExit', _hsExitEntry',
                _hsEntry_tz, _hexit_order', hentry_order'⟩
            have hez_eq : ez = sEntry' := by
              exact hf (by rw [← hentryz, ← hentry_order'])
            have he2_lt_ez : e2 < ez := by
              linarith
            have hpz_tz :
                p ∈ Metric.closedBall (centerOfParam i tz)
                    (r (centerOfParam i tz)) := by
              simpa [htz_center] using hpz
            exact (hchordGapDiskPosition i tz
              (α := x1) (β := e2) (e := ez) (x := xz)
              hentryz hexitz (by linarith) (le_of_lt hx1_lt_e2)
              (by linarith) (by linarith)).1
                hpseg_param hpz_tz he2_lt_ez
        · have hdis :
              Disjoint (Metric.closedBall z (r z)) (segment ℝ (a i) (b i)) :=
            hmiss hzT i hzseg
          exact (Set.disjoint_left.mp hdis) hpz hpseg_chord
  · rcases hterminal with ⟨pre, t, X, hitems, hlast, hleft, hright⟩
    have hlast_exit :
        (localArcAtParam i t).vertices.getLast? = some (exitPoint i t) := by
      have htarget := (localArcAtParam i t).target_eq_last
      rw [(hlocalArcAtParam_props i t).2.1] at htarget
      exact htarget
    have hX : X = exitPoint i t := by
      exact (Option.some.inj (hlast_exit.symm.trans hlast)).symm
    have hpseg_gap : p ∈ segment ℝ (exitPoint i t) (b i) := by
      simpa [hleft, hright, hX] using hpseg
    by_cases hp_exit : p = exitPoint i t
    · right
      right
      refine ⟨t, Or.inr ⟨hp_exit, ?_, ?_⟩⟩
      · simpa [hp_exit] using (hentry_exit_local i t).2.1
      · simpa [hp_exit] using hexitPoint_open_chord i t
    · left
      have hexit_chord :
          exitPoint i t ∈ segment ℝ (a i) (b i) :=
        openSegment_subset_segment ℝ (a i) (b i)
          (hexitPoint_open_chord i t)
      have hpseg_chord : p ∈ segment ℝ (a i) (b i) :=
        (convex_segment (a i) (b i)).segment_subset
          hexit_chord (right_mem_segment ℝ (a i) (b i)) hpseg_gap
      refine ⟨mem_openSegment_of_ne_left_right (𝕜 := ℝ)
        hp_ne_a.symm hp_ne_b.symm hpseg_chord, ?_⟩
      intro z hzT hpz
      by_cases hzseg : z ∈ segment ℝ (a i) (b i)
      · rcases hchosenCenterOnChord_param i hzT hzseg with ⟨tz, htz_center⟩
        have htz_attach : tz ∈ (centerParams i).attach := by
          simp
        have htz_cases : tz ∈ pre ∨ tz = t := by
          have hmem : tz ∈ pre ∨ tz ∈ [t] := by
            simpa [hitems, List.mem_append] using htz_attach
          rcases hmem with hpre | htlast
          · exact Or.inl hpre
          · exact Or.inr (by simpa using htlast)
        rcases hentryExitParameters i t with
          ⟨⟨e, he_pos, he_lt_t, hentry⟩,
            ⟨x, ht_lt_x, hx_lt_one, hexit⟩⟩
        have hpseg_param :
            p ∈ segment ℝ (AffineMap.lineMap (a i) (b i) x)
                (AffineMap.lineMap (a i) (b i) (1 : ℝ)) := by
          simpa [hexit] using hpseg_gap
        rcases htz_cases with htz_pre | htz_eq
        · have htz_lt_t : tz.1 < t.1 := by
            have hpair := hattach_pairwise_lt_all i
            rw [hitems] at hpair
            exact (List.pairwise_append.1 hpair).2.2 tz htz_pre t (by simp)
          rcases hentryExitParameters i tz with
            ⟨⟨ez, hez_pos, hez_lt_tz, hentryz⟩,
              ⟨xz, htz_lt_xz, hxz_lt_one, hexitz⟩⟩
          rcases horderedCutSeparation i tz t htz_lt_t with
            ⟨sExit, sEntry, _htz_sExit, _hsExitEntry, _hsEntry_t,
              hexit_order, hentry_order⟩
          let f : ℝ →ᵃ[ℝ] EuclideanSpace ℝ (Fin 2) :=
            AffineMap.lineMap (a i) (b i)
          have hf : Function.Injective f :=
            AffineMap.lineMap_injective (k := ℝ) (hendpoint_ne i)
          have hxz_eq : xz = sExit := by
            exact hf (by rw [← hexitz, ← hexit_order])
          have he_eq : e = sEntry := by
            exact hf (by rw [← hentry, ← hentry_order])
          have hxz_lt_x : xz < x := by
            linarith
          have hpz_tz :
              p ∈ Metric.closedBall (centerOfParam i tz)
                  (r (centerOfParam i tz)) := by
            simpa [htz_center] using hpz
          exact (hchordGapDiskPosition i tz
            (α := x) (β := (1 : ℝ)) (e := ez) (x := xz)
            hentryz hexitz (by linarith) (by linarith)
            (by norm_num) (by linarith)).2.2.1
              hpseg_param hpz_tz hxz_lt_x
        · subst tz
          have hpz_t :
              p ∈ Metric.closedBall (centerOfParam i t) (r (centerOfParam i t)) := by
            simpa [htz_center] using hpz
          have hp_eq_exit :
              p = exitPoint i t :=
            (hchordGapDiskPosition i t
              (α := x) (β := (1 : ℝ)) (e := e) (x := x)
              hentry hexit (by linarith) (by linarith)
              (by norm_num) (by linarith)).2.2.2
                hpseg_param hpz_t rfl
          exact hp_exit hp_eq_exit
      · have hdis :
            Disjoint (Metric.closedBall z (r z)) (segment ℝ (a i) (b i)) :=
          hmiss hzT i hzseg
        exact (Set.disjoint_left.mp hdis) hpz hpseg_chord

private structure endpointUnitDiskAssemblyPrepared
    {ι : Type*} (a b : ι → EuclideanSpace ℝ (Fin 2)) where
  Gamma : ι → PolygonalArc
  properties : ∀ i,
    (Gamma i).source = a i ∧
      (Gamma i).target = b i ∧
        (Gamma i).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ∧
          (Gamma i).relativeInterior ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1
  noCommonSegment : ∀ ⦃i j : ι⦄,
    i ≠ j →
      ¬ ∃ m n : ℕ,
        ∃ (hm : m + 1 < (Gamma i).vertices.length)
          (hn : n + 1 < (Gamma j).vertices.length),
          ∃ p q : EuclideanSpace ℝ (Fin 2),
            p ≠ q ∧
              segment ℝ p q ⊆
                segment ℝ (Gamma i).vertices[m] (Gamma i).vertices[m + 1] ∩
                  segment ℝ (Gamma j).vertices[n] (Gamma j).vertices[n + 1]
  noTriple : ∀ ⦃i j k : ι⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
    i ≠ j → i ≠ k → j ≠ k →
      p ∈ (Gamma i).relativeInterior →
        p ∈ (Gamma j).relativeInterior →
          p ∈ (Gamma k).relativeInterior → False
  transverse : ∀ ⦃i j : ι⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
    i ≠ j →
      p ∈ (Gamma i).relativeInterior →
        p ∈ (Gamma j).relativeInterior →
          endpointUnitDiskAssembly_transverseWitness Gamma i j p
  unique : ∀ ⦃i j : ι⦄ ⦃p q : EuclideanSpace ℝ (Fin 2)⦄,
    i ≠ j →
      p ∈ (Gamma i).relativeInterior →
        p ∈ (Gamma j).relativeInterior →
          q ∈ (Gamma i).relativeInterior →
            q ∈ (Gamma j).relativeInterior → p = q
  clean : ∀ ⦃i j : ι⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
    i ≠ j →
      p ∈ (Gamma i).relativeInterior →
        p ∈ (Gamma j).relativeInterior →
          Nonempty (OrdinaryCleanLocalCrossing Gamma i j p)

private noncomputable def endpointUnitDiskAssembly_prepare
    {ι : Type*} [Fintype ι]
    (a b : ι → EuclideanSpace ℝ (Fin 2))
    (ha : ∀ i, dist (a i) (0 : EuclideanSpace ℝ (Fin 2)) = 1)
    (hb : ∀ i, dist (b i) (0 : EuclideanSpace ℝ (Fin 2)) = 1)
    (hdistinct : Function.Injective (fun x : ι ⊕ ι => Sum.elim a b x))
    (T : Finset (EuclideanSpace ℝ (Fin 2)))
    (r : EuclideanSpace ℝ (Fin 2) → ℝ)
    (hT : ∀ z, z ∈ T ↔
      z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1 ∧
        ∃ i j k : ι,
          i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
            z ∈ openSegment ℝ (a i) (b i) ∧
              z ∈ openSegment ℝ (a j) (b j) ∧
                z ∈ openSegment ℝ (a k) (b k))
    (hrpos : ∀ z ∈ T, 0 < r z)
    (hclosed : ∀ z ∈ T,
      Metric.closedBall z (r z) ⊆
        Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1)
    (hdisjoint : ∀ ⦃z w : EuclideanSpace ℝ (Fin 2)⦄,
      z ∈ T → w ∈ T → z ≠ w →
        Disjoint (Metric.closedBall z (r z)) (Metric.closedBall w (r w)))
    (hmiss : ∀ ⦃z : EuclideanSpace ℝ (Fin 2)⦄,
      z ∈ T → ∀ i,
        z ∉ segment ℝ (a i) (b i) →
          Disjoint (Metric.closedBall z (r z)) (segment ℝ (a i) (b i)))
    (hpairOnly : ∀ ⦃z y : EuclideanSpace ℝ (Fin 2)⦄,
      z ∈ T →
        y ∈ Metric.closedBall z (r z) →
          (∃ i j : ι,
            i ≠ j ∧
              y ∈ segment ℝ (a i) (b i) ∧
                y ∈ segment ℝ (a j) (b j)) →
            y = z)
    (hlocal : ∀ z, z ∈ T →
      let κ := {i : ι // z ∈ openSegment ℝ (a i) (b i)}
      ∃ u v : κ → EuclideanSpace ℝ (Fin 2),
        ∃ Ξ : κ → PolygonalArc,
          (∀ i : κ,
            u i ∈ Metric.sphere z (r z) ∧
              v i ∈ Metric.sphere z (r z) ∧
                u i ∈ openSegment ℝ (a i.1) z ∧
                  v i ∈ openSegment ℝ z (b i.1) ∧
                    Metric.closedBall z (r z) ∩ segment ℝ (a i.1) (b i.1) =
                      segment ℝ (u i) (v i)) ∧
            (∀ i : κ,
              (Ξ i).source = u i ∧
                (Ξ i).target = v i ∧
                  (Ξ i).carrier ⊆ Metric.closedBall z (r z) ∧
                    (Ξ i).relativeInterior ⊆ Metric.ball z (r z)) ∧
              (∀ ⦃i j : κ⦄,
                i ≠ j →
                  ¬ ∃ m n : ℕ,
                    ∃ (hm : m + 1 < (Ξ i).vertices.length)
                      (hn : n + 1 < (Ξ j).vertices.length),
                      ∃ p q : EuclideanSpace ℝ (Fin 2),
                        p ≠ q ∧
                          segment ℝ p q ⊆
                            segment ℝ (Ξ i).vertices[m] (Ξ i).vertices[m + 1] ∩
                              segment ℝ (Ξ j).vertices[n] (Ξ j).vertices[n + 1]) ∧
                (∀ ⦃i j k : κ⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
                  i ≠ j → i ≠ k → j ≠ k →
                    p ∈ (Ξ i).relativeInterior →
                      p ∈ (Ξ j).relativeInterior →
                        p ∈ (Ξ k).relativeInterior → False) ∧
                  (∀ ⦃i j : κ⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
                    i ≠ j →
                      p ∈ (Ξ i).relativeInterior →
                        p ∈ (Ξ j).relativeInterior →
                          ∃ m n : ℕ,
                            ∃ (hm : m + 1 < (Ξ i).vertices.length)
                              (hn : n + 1 < (Ξ j).vertices.length),
                              p ∈ segment ℝ (Ξ i).vertices[m] (Ξ i).vertices[m + 1] ∧
                                p ∈ segment ℝ (Ξ j).vertices[n] (Ξ j).vertices[n + 1] ∧
                                  ¬ ∃ t : ℝ,
                                    (Ξ j).vertices[n + 1] - (Ξ j).vertices[n] =
                                      t • ((Ξ i).vertices[m + 1] -
                                        (Ξ i).vertices[m])) ∧
                    (∀ ⦃i j : κ⦄ ⦃p q : EuclideanSpace ℝ (Fin 2)⦄,
                      i ≠ j →
                        p ∈ (Ξ i).relativeInterior →
                          p ∈ (Ξ j).relativeInterior →
                            q ∈ (Ξ i).relativeInterior →
                              q ∈ (Ξ j).relativeInterior →
                                p = q) ∧
                    (∀ ⦃i j : κ⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
                      i ≠ j →
                        p ∈ (Ξ i).relativeInterior →
                          p ∈ (Ξ j).relativeInterior →
                            Nonempty (OrdinaryCleanLocalCrossing Ξ i j p))) :
    endpointUnitDiskAssemblyPrepared a b := by
  have hindexUnique := endpointUnitDiskAssembly_indexUnique
  have hchordControl :=
    @EndpointUnitChordMultiplePointControl ι _ a b ha hb hdistinct
  have hendpoint_ne : ∀ i, a i ≠ b i := hchordControl.2.1
  have hcenterParameterList :
      ∀ i,
        ∃ L : List ℝ,
          L.Nodup ∧
            L.SortedLT ∧
              (∀ t : ℝ,
                t ∈ L ↔
                  0 < t ∧ t < 1 ∧ AffineMap.lineMap (a i) (b i) t ∈ T) ∧
                (∀ t ∈ L,
                  AffineMap.lineMap (a i) (b i) t ∈ openSegment ℝ (a i) (b i)) := by
    intro i
    exact EndpointUnitDiskChordCenterParameterList (a i) (b i) (hendpoint_ne i) T
  have htripleCovered :=
    @EndpointUnitDiskTriplePointInChosenDisk ι _ a b T r hT hrpos
  have hlocalForeignMiss :=
    @EndpointUnitDiskLocalPieceMeetsOnlyIncidentChord ι _ a b T r hmiss
  have hlocalSameCenter :=
    @EndpointUnitDiskLocalPiecesSameCenter T r hdisjoint
  choose centerParams hcenterParams using hcenterParameterList
  have hcenterParams_nodup : ∀ i, (centerParams i).Nodup := by
    intro i
    exact (hcenterParams i).1
  have hcenterParams_sorted : ∀ i, (centerParams i).SortedLT := by
    intro i
    exact (hcenterParams i).2.1
  have hcenterParams_mem :
      ∀ i t,
        t ∈ centerParams i ↔
          0 < t ∧ t < 1 ∧ AffineMap.lineMap (a i) (b i) t ∈ T := by
    intro i
    exact (hcenterParams i).2.2.1
  have hcenterParams_open :
      ∀ i t,
        t ∈ centerParams i →
          AffineMap.lineMap (a i) (b i) t ∈ openSegment ℝ (a i) (b i) := by
    intro i
    exact (hcenterParams i).2.2.2
  let centerOfParam :
      ∀ i, {t : ℝ // t ∈ centerParams i} → EuclideanSpace ℝ (Fin 2) :=
    fun i t => AffineMap.lineMap (a i) (b i) t.1
  have hcenterOfParam_T :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}), centerOfParam i t ∈ T := by
    intro i t
    exact ((hcenterParams_mem i t.1).1 t.2).2.2
  have hcenterOfParam_bounds :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}), 0 < t.1 ∧ t.1 < 1 := by
    intro i t
    have ht := (hcenterParams_mem i t.1).1 t.2
    exact ⟨ht.1, ht.2.1⟩
  have hcenterOfParam_open :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}),
        centerOfParam i t ∈ openSegment ℝ (a i) (b i) := by
    intro i t
    exact hcenterParams_open i t.1 t.2
  let Center := {z : EuclideanSpace ℝ (Fin 2) // z ∈ T}
  let Incident (z : EuclideanSpace ℝ (Fin 2)) :=
    {j : ι // z ∈ openSegment ℝ (a j) (b j)}
  have hlocalAtCenter := fun z : Center ↦ hlocal z.1 z.2
  choose localU localV localXi hlocalAtCenter_spec using hlocalAtCenter
  let centerAtParam :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}), Center :=
    fun i t => ⟨centerOfParam i t, hcenterOfParam_T i t⟩
  let incidentAtParam :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}),
        Incident (centerOfParam i t) :=
    fun i t => ⟨i, hcenterOfParam_open i t⟩
  let entryPoint :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}), EuclideanSpace ℝ (Fin 2) :=
    fun i t => localU (centerAtParam i t) (incidentAtParam i t)
  let exitPoint :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}), EuclideanSpace ℝ (Fin 2) :=
    fun i t => localV (centerAtParam i t) (incidentAtParam i t)
  let localArcAtParam :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}), PolygonalArc :=
    fun i t => localXi (centerAtParam i t) (incidentAtParam i t)
  have hentry_exit_local :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}),
        entryPoint i t ∈ Metric.sphere (centerOfParam i t) (r (centerOfParam i t)) ∧
          exitPoint i t ∈ Metric.sphere (centerOfParam i t) (r (centerOfParam i t)) ∧
            entryPoint i t ∈ openSegment ℝ (a i) (centerOfParam i t) ∧
              exitPoint i t ∈ openSegment ℝ (centerOfParam i t) (b i) ∧
                Metric.closedBall (centerOfParam i t) (r (centerOfParam i t)) ∩
                    segment ℝ (a i) (b i) =
                  segment ℝ (entryPoint i t) (exitPoint i t) := by
    intro i t
    simpa [entryPoint, exitPoint, centerAtParam, incidentAtParam, Incident] using
      (hlocalAtCenter_spec (centerAtParam i t)).1 (incidentAtParam i t)
  have hlocalArcAtParam_props :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}),
        (localArcAtParam i t).source = entryPoint i t ∧
          (localArcAtParam i t).target = exitPoint i t ∧
            (localArcAtParam i t).carrier ⊆
              Metric.closedBall (centerOfParam i t) (r (centerOfParam i t)) ∧
              (localArcAtParam i t).relativeInterior ⊆
                Metric.ball (centerOfParam i t) (r (centerOfParam i t)) := by
    intro i t
    simpa [localArcAtParam, entryPoint, exitPoint, centerAtParam, incidentAtParam,
        Incident] using
      (hlocalAtCenter_spec (centerAtParam i t)).2.1 (incidentAtParam i t)
  have hentryExitParameters :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}),
        (∃ s : ℝ, 0 < s ∧ s < t.1 ∧
          entryPoint i t = AffineMap.lineMap (a i) (b i) s) ∧
          (∃ s : ℝ, t.1 < s ∧ s < 1 ∧
            exitPoint i t = AffineMap.lineMap (a i) (b i) s) := by
    intro i t
    have hbounds := hcenterOfParam_bounds i t
    have hends := hentry_exit_local i t
    exact EndpointUnitDiskChordEndpointParameters
      (A := a i) (B := b i) (z := centerOfParam i t)
      (u := entryPoint i t) (v := exitPoint i t) (t := t.1)
      (by rfl) hbounds.1 hbounds.2 hends.2.2.1 hends.2.2.2.1
  have horderedCutSeparation :
      ∀ i (t1 t2 : {t : ℝ // t ∈ centerParams i}),
        t1.1 < t2.1 →
          ∃ sExit sEntry : ℝ,
            t1.1 < sExit ∧
              sExit < sEntry ∧
                sEntry < t2.1 ∧
                  exitPoint i t1 = AffineMap.lineMap (a i) (b i) sExit ∧
                    entryPoint i t2 = AffineMap.lineMap (a i) (b i) sEntry := by
    intro i t1 t2 ht12
    rcases hentryExitParameters i t1 with
      ⟨⟨e1, _he1_pos, he1_lt_t1, hentry1⟩,
        ⟨x1, ht1_lt_x1, _hx1_lt_one, hexit1⟩⟩
    rcases hentryExitParameters i t2 with
      ⟨⟨e2, _he2_pos, he2_lt_t2, hentry2⟩,
        ⟨x2, ht2_lt_x2, _hx2_lt_one, hexit2⟩⟩
    have hcenter_ne : centerOfParam i t1 ≠ centerOfParam i t2 := by
      intro hsame
      have hparam_eq : t1.1 = t2.1 := by
        have hinj := AffineMap.lineMap_injective (k := ℝ) (hendpoint_ne i)
        exact hinj (by simpa [centerOfParam] using hsame)
      linarith
    have hballs_disjoint :
        Disjoint
          (Metric.closedBall (centerOfParam i t1) (r (centerOfParam i t1)))
          (Metric.closedBall (centerOfParam i t2) (r (centerOfParam i t2))) :=
      hdisjoint (hcenterOfParam_T i t1) (hcenterOfParam_T i t2) hcenter_ne
    have hx1_lt_e2 :
        x1 < e2 :=
      PolygonalReplacementStraightSegmentDisjointCutOrder
        (A := a i) (B := b i)
        (z1 := centerOfParam i t1) (z2 := centerOfParam i t2)
        (u1 := entryPoint i t1) (v1 := exitPoint i t1)
        (u2 := entryPoint i t2) (v2 := exitPoint i t2)
        (rho1 := r (centerOfParam i t1)) (rho2 := r (centerOfParam i t2))
        (center1 := t1.1) (center2 := t2.1)
        (left1 := e1) (right1 := x1) (left2 := e2) (right2 := x2)
        hballs_disjoint
        (hentry_exit_local i t1).2.2.2.2
        (hentry_exit_local i t2).2.2.2.2
        hentry1 hexit1 hentry2 hexit2
        he1_lt_t1 ht1_lt_x1 ht12 he2_lt_t2 ht2_lt_x2
    exact ⟨x1, e2, ht1_lt_x1, hx1_lt_e2, he2_lt_t2, hexit1, hentry2⟩
  have hchordSubsegmentUnitContainment :
      ∀ i {X Y : EuclideanSpace ℝ (Fin 2)},
        X ∈ segment ℝ (a i) (b i) →
          Y ∈ segment ℝ (a i) (b i) →
            segment ℝ X Y ⊆
                Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ∧
              ∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
                p ∈ segment ℝ X Y → p ≠ a i → p ≠ b i →
                  p ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
    intro i X Y hX hY
    exact EndpointUnitDiskChordSubsegmentUnitContainment
      (hA := ha i) (hB := hb i) (hAB := hendpoint_ne i) hX hY
  have horderedOutsideGapUnitContainment :
      ∀ i (t1 t2 : {t : ℝ // t ∈ centerParams i}),
        t1.1 < t2.1 →
          segment ℝ (exitPoint i t1) (entryPoint i t2) ⊆
              Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ∧
            ∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
              p ∈ segment ℝ (exitPoint i t1) (entryPoint i t2) →
                p ≠ a i → p ≠ b i →
                  p ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
    intro i t1 t2 ht12
    rcases horderedCutSeparation i t1 t2 ht12 with
      ⟨sExit, sEntry, ht1sExit, hsExitEntry, hsEntryt2, hexit, hentry⟩
    have ht1_bounds := hcenterOfParam_bounds i t1
    have ht2_bounds := hcenterOfParam_bounds i t2
    have hsExit_open :
        AffineMap.lineMap (a i) (b i) sExit ∈
          openSegment ℝ (a i) (b i) := by
      exact lineMap_mem_openSegment (𝕜 := ℝ) (a i) (b i)
        ⟨by linarith, by linarith⟩
    have hsEntry_open :
        AffineMap.lineMap (a i) (b i) sEntry ∈
          openSegment ℝ (a i) (b i) := by
      exact lineMap_mem_openSegment (𝕜 := ℝ) (a i) (b i)
        ⟨by linarith, by linarith⟩
    have hexit_segment :
        exitPoint i t1 ∈ segment ℝ (a i) (b i) := by
      rw [hexit]
      exact openSegment_subset_segment ℝ (a i) (b i) hsExit_open
    have hentry_segment :
        entryPoint i t2 ∈ segment ℝ (a i) (b i) := by
      rw [hentry]
      exact openSegment_subset_segment ℝ (a i) (b i) hsEntry_open
    exact hchordSubsegmentUnitContainment i hexit_segment hentry_segment
  have horderedOutsideGapMeetsNeighboringDisksOnly :
      ∀ i (t1 t2 : {t : ℝ // t ∈ centerParams i}),
        t1.1 < t2.1 →
          (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
            p ∈ segment ℝ (exitPoint i t1) (entryPoint i t2) →
              p ∈ Metric.closedBall (centerOfParam i t1) (r (centerOfParam i t1)) →
                p = exitPoint i t1) ∧
            (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
              p ∈ segment ℝ (exitPoint i t1) (entryPoint i t2) →
                p ∈ Metric.closedBall (centerOfParam i t2) (r (centerOfParam i t2)) →
                  p = entryPoint i t2) := by
    intro i t1 t2 ht12
    rcases horderedCutSeparation i t1 t2 ht12 with
      ⟨sExit, sEntry, ht1sExit, hsExitEntry, hsEntryt2, hexit, hentry⟩
    rcases hentryExitParameters i t1 with
      ⟨⟨e1, _he1_pos, he1_lt_t1, hentry1⟩, _⟩
    rcases hentryExitParameters i t2 with
      ⟨_, ⟨x2, ht2_lt_x2, _hx2_lt_one, hexit2⟩⟩
    have ht1_bounds := hcenterOfParam_bounds i t1
    have ht2_bounds := hcenterOfParam_bounds i t2
    exact EndpointUnitDiskOrderedGapDiskIntersections
      (A := a i) (B := b i)
      (z1 := centerOfParam i t1) (z2 := centerOfParam i t2)
      (u1 := entryPoint i t1) (v1 := exitPoint i t1)
      (u2 := entryPoint i t2) (v2 := exitPoint i t2)
      (rho1 := r (centerOfParam i t1)) (rho2 := r (centerOfParam i t2))
      (e1 := e1) (x1 := sExit) (e2 := sEntry) (x2 := x2)
      (hendpoint_ne i)
      (hentry_exit_local i t1).2.2.2.2
      (hentry_exit_local i t2).2.2.2.2
      hentry1 hexit hentry hexit2
      (by linarith) (by linarith)
      (by linarith) hsExitEntry (by linarith)
  have hlocalArcUnitContainment :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}),
        (localArcAtParam i t).carrier ⊆
            Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ∧
          (localArcAtParam i t).relativeInterior ⊆
            Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
    intro i t
    constructor
    · intro p hp
      have hp_unit_ball :
          p ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1 :=
        hclosed (centerOfParam i t) (hcenterOfParam_T i t)
          ((hlocalArcAtParam_props i t).2.2.1 hp)
      exact Metric.ball_subset_closedBall hp_unit_ball
    · intro p hp
      exact hclosed (centerOfParam i t) (hcenterOfParam_T i t)
        (Metric.ball_subset_closedBall ((hlocalArcAtParam_props i t).2.2.2 hp))
  have horderedOutsideGapMeetsNeighboringLocalCarriersOnly :
      ∀ i (t1 t2 : {t : ℝ // t ∈ centerParams i}),
        t1.1 < t2.1 →
          (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
            p ∈ segment ℝ (exitPoint i t1) (entryPoint i t2) →
              p ∈ (localArcAtParam i t1).carrier →
                p = exitPoint i t1) ∧
            (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
              p ∈ segment ℝ (exitPoint i t1) (entryPoint i t2) →
                p ∈ (localArcAtParam i t2).carrier →
                  p = entryPoint i t2) := by
    intro i t1 t2 ht12
    constructor
    · intro p hp_gap hp_carrier
      exact (horderedOutsideGapMeetsNeighboringDisksOnly i t1 t2 ht12).1
        hp_gap ((hlocalArcAtParam_props i t1).2.2.1 hp_carrier)
    · intro p hp_gap hp_carrier
      exact (horderedOutsideGapMeetsNeighboringDisksOnly i t1 t2 ht12).2
        hp_gap ((hlocalArcAtParam_props i t2).2.2.1 hp_carrier)
  have hchordGapLocalCarrierPosition :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}) {α β e x : ℝ},
        entryPoint i t = AffineMap.lineMap (a i) (b i) e →
          exitPoint i t = AffineMap.lineMap (a i) (b i) x →
            0 ≤ α → α ≤ β → β ≤ 1 → e < x →
              (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
                p ∈ segment ℝ (AffineMap.lineMap (a i) (b i) α)
                    (AffineMap.lineMap (a i) (b i) β) →
                  p ∈ (localArcAtParam i t).carrier →
                    β < e → False) ∧
                (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
                  p ∈ segment ℝ (AffineMap.lineMap (a i) (b i) α)
                      (AffineMap.lineMap (a i) (b i) β) →
                    p ∈ (localArcAtParam i t).carrier →
                      β = e → p = entryPoint i t) ∧
                  (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
                    p ∈ segment ℝ (AffineMap.lineMap (a i) (b i) α)
                        (AffineMap.lineMap (a i) (b i) β) →
                      p ∈ (localArcAtParam i t).carrier →
                        x < α → False) ∧
                    (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
                      p ∈ segment ℝ (AffineMap.lineMap (a i) (b i) α)
                          (AffineMap.lineMap (a i) (b i) β) →
                        p ∈ (localArcAtParam i t).carrier →
                          x = α → p = exitPoint i t) := by
    intro i t α β e x hentry hexit hα0 hαβ hβ1 hex
    have hgap :=
      EndpointUnitDiskChordGapCutDiskIntersections
        (A := a i) (B := b i) (z := centerOfParam i t)
        (u := entryPoint i t) (v := exitPoint i t)
        (rho := r (centerOfParam i t)) (α := α) (β := β) (e := e) (x := x)
        (hendpoint_ne i) (hentry_exit_local i t).2.2.2.2 hentry hexit
        hα0 hαβ hβ1 hex
    constructor
    · intro p hp_gap hp_carrier hβe
      exact hgap.1 hp_gap ((hlocalArcAtParam_props i t).2.2.1 hp_carrier) hβe
    constructor
    · intro p hp_gap hp_carrier hβe
      exact hgap.2.1 hp_gap ((hlocalArcAtParam_props i t).2.2.1 hp_carrier) hβe
    constructor
    · intro p hp_gap hp_carrier hxα
      exact hgap.2.2.1 hp_gap ((hlocalArcAtParam_props i t).2.2.1 hp_carrier) hxα
    · intro p hp_gap hp_carrier hxα
      exact hgap.2.2.2 hp_gap ((hlocalArcAtParam_props i t).2.2.1 hp_carrier) hxα
  have hinitialGapMeetsLocalCarrierOnly :
      ∀ i (t : {t : ℝ // t ∈ centerParams i})
        ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        p ∈ segment ℝ (a i) (entryPoint i t) →
          p ∈ (localArcAtParam i t).carrier →
            p = entryPoint i t := by
    intro i t p hp_gap hp_carrier
    rcases hentryExitParameters i t with
      ⟨⟨e, he_pos, he_lt_t, hentry⟩, ⟨x, ht_lt_x, hx_lt_one, hexit⟩⟩
    have hp_gap' :
        p ∈ segment ℝ (AffineMap.lineMap (a i) (b i) (0 : ℝ))
            (AffineMap.lineMap (a i) (b i) e) := by
      simpa [hentry] using hp_gap
    exact (hchordGapLocalCarrierPosition i t
      (α := (0 : ℝ)) (β := e) (e := e) (x := x) hentry hexit
      (by norm_num) (le_of_lt he_pos) (by linarith) (by linarith)).2.1
        hp_gap' hp_carrier rfl
  have hterminalGapMeetsLocalCarrierOnly :
      ∀ i (t : {t : ℝ // t ∈ centerParams i})
        ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        p ∈ segment ℝ (exitPoint i t) (b i) →
          p ∈ (localArcAtParam i t).carrier →
            p = exitPoint i t := by
    intro i t p hp_gap hp_carrier
    rcases hentryExitParameters i t with
      ⟨⟨e, he_pos, he_lt_t, hentry⟩, ⟨x, ht_lt_x, hx_lt_one, hexit⟩⟩
    have hp_gap' :
        p ∈ segment ℝ (AffineMap.lineMap (a i) (b i) x)
            (AffineMap.lineMap (a i) (b i) (1 : ℝ)) := by
      simpa [hexit] using hp_gap
    exact (hchordGapLocalCarrierPosition i t
      (α := x) (β := (1 : ℝ)) (e := e) (x := x) hentry hexit
      (by linarith) (le_of_lt hx_lt_one) (by norm_num) (by linarith)).2.2.2
        hp_gap' hp_carrier rfl
  let orderedLocalArcs : ∀ i, List PolygonalArc :=
    fun i => (centerParams i).attach.map (fun t => localArcAtParam i t)
  have horderedLocalArcs_length :
      ∀ i, (orderedLocalArcs i).length = (centerParams i).length := by
    intro i
    simp [orderedLocalArcs]
  have horderedLocalArcs_mem :
      ∀ i Γ, Γ ∈ orderedLocalArcs i →
        ∃ t : {t : ℝ // t ∈ centerParams i},
          localArcAtParam i t = Γ ∧
            Γ.source = entryPoint i t ∧
              Γ.target = exitPoint i t ∧
                Γ.carrier ⊆
                  Metric.closedBall (centerOfParam i t) (r (centerOfParam i t)) ∧
                  Γ.relativeInterior ⊆
                    Metric.ball (centerOfParam i t) (r (centerOfParam i t)) := by
    intro i Γ hΓ
    rcases List.mem_map.mp hΓ with ⟨t, _ht, htΓ⟩
    refine ⟨t, htΓ, ?_⟩
    rw [← htΓ]
    exact hlocalArcAtParam_props i t
  let orderedLocalVertexBlocks :
      ∀ i, List (List (EuclideanSpace ℝ (Fin 2))) :=
    fun i => (centerParams i).attach.map (fun t => (localArcAtParam i t).vertices)
  have horderedLocalVertexBlocks_nontrivial :
      ∀ i V, V ∈ orderedLocalVertexBlocks i → 2 ≤ V.length := by
    intro i V hV
    rcases List.mem_map.mp hV with ⟨t, _ht, htV⟩
    rw [← htV]
    exact (localArcAtParam i t).length_ge_two
  let assembledVertices : ∀ i, List (EuclideanSpace ℝ (Fin 2)) :=
    fun i => EndpointUnitDiskAlternatingVertexList
      (a i) (b i) (orderedLocalVertexBlocks i)
  let assembledEdgeSet : ∀ i, Set (EuclideanSpace ℝ (Fin 2)) := fun i =>
    {p | ∃ m : ℕ, ∃ hm : m + 1 < (assembledVertices i).length,
      p ∈ segment ℝ (assembledVertices i)[m] (assembledVertices i)[m + 1]}
  have hassembledVertices_mem_closed :
      ∀ i ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        p ∈ assembledVertices i →
          p ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
    intro i p hp
    simp [assembledVertices, EndpointUnitDiskAlternatingVertexList] at hp
    rcases hp with hpA | hp
    · rw [hpA]
      simp [Metric.mem_closedBall, ha i]
    · rcases hp with hpflat | hpB
      · rcases hpflat with ⟨V, hV, hpV⟩
        rcases List.mem_map.mp hV with ⟨t, _ht, htV⟩
        rw [← htV] at hpV
        exact (hlocalArcUnitContainment i t).1
          (PolygonalArcVertexMemCarrier (localArcAtParam i t) hpV)
      · rw [hpB]
        simp [Metric.mem_closedBall, hb i]
  have hassembledEdgeUnitContainment :
      ∀ i ⦃m : ℕ⦄,
        (hm : m + 1 < (assembledVertices i).length) →
          segment ℝ (assembledVertices i)[m] (assembledVertices i)[m + 1] ⊆
            Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
    intro i m hm
    have hm_left : m < (assembledVertices i).length :=
      Nat.lt_trans (Nat.lt_succ_self m) hm
    have hleft :
        (assembledVertices i)[m] ∈
          Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 :=
      hassembledVertices_mem_closed i
        (List.getElem_mem (l := assembledVertices i) hm_left)
    have hright :
        (assembledVertices i)[m + 1] ∈
          Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 :=
      hassembledVertices_mem_closed i
        (List.getElem_mem (l := assembledVertices i) hm)
    exact (convex_closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1).segment_subset
      hleft hright
  have hassembledEdgeUnitOpenContainment :
      ∀ i ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        p ∈ assembledEdgeSet i → p ≠ a i → p ≠ b i →
          p ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
    intro i p hp hpA hpB
    rcases hp with ⟨m, hm, hpm⟩
    have hblock_nonempty :
        ∀ t ∈ (centerParams i).attach,
          0 < ((localArcAtParam i t).vertices).length := by
      intro t _ht
      have hlen := (localArcAtParam i t).length_ge_two
      omega
    have hroles :=
      EndpointUnitDiskAlternatingVertexListEdgeRoles
        (A := a i) (B := b i)
        (items := (centerParams i).attach)
        (block := fun t => (localArcAtParam i t).vertices)
        hblock_nonempty
        (m := m)
        (hm := by simpa [assembledVertices, orderedLocalVertexBlocks] using hm)
        (p := p)
        (hp := by simpa [assembledVertices, orderedLocalVertexBlocks] using hpm)
    rcases hroles with hnodisks | hroles
    · rcases hnodisks with ⟨_hitems, hpAB⟩
      exact (hchordSubsegmentUnitContainment i
        (left_mem_segment ℝ (a i) (b i))
        (right_mem_segment ℝ (a i) (b i))).2 hpAB hpA hpB
    rcases hroles with hinitial | hroles
    · rcases hinitial with ⟨t, _ts, X, _hitems, hhead, hpAX⟩
      have hsource_entry :
          (localArcAtParam i t).vertices.head? = some (entryPoint i t) := by
        have hsource := (localArcAtParam i t).source_eq_head
        rw [(hlocalArcAtParam_props i t).1] at hsource
        exact hsource
      have hX : X = entryPoint i t := by
        exact (Option.some.inj (hsource_entry.symm.trans hhead)).symm
      have hentry_segment :
          entryPoint i t ∈ segment ℝ (a i) (b i) := by
        have hmem :
            entryPoint i t ∈
              Metric.closedBall (centerOfParam i t) (r (centerOfParam i t)) ∩
                segment ℝ (a i) (b i) := by
          rw [(hentry_exit_local i t).2.2.2.2]
          exact left_mem_segment ℝ (entryPoint i t) (exitPoint i t)
        exact hmem.2
      exact (hchordSubsegmentUnitContainment i
        (left_mem_segment ℝ (a i) (b i)) hentry_segment).2
          (by simpa [hX] using hpAX) hpA hpB
    rcases hroles with hlocal | hroles
    · rcases hlocal with ⟨_pre, t, _post, k, hk, _hitems, hplocal⟩
      have hp_carrier : p ∈ (localArcAtParam i t).carrier := by
        rw [(localArcAtParam i t).carrier_eq]
        exact ⟨k, hk, hplocal⟩
      exact hclosed (centerOfParam i t) (hcenterOfParam_T i t)
        ((hlocalArcAtParam_props i t).2.2.1 hp_carrier)
    rcases hroles with hbridge | hterminal
    · rcases hbridge with ⟨pre, t1, t2, post, X, Y, hitems, hlast, hhead, hpXY⟩
      have hlast_exit :
          (localArcAtParam i t1).vertices.getLast? = some (exitPoint i t1) := by
        have htarget := (localArcAtParam i t1).target_eq_last
        rw [(hlocalArcAtParam_props i t1).2.1] at htarget
        exact htarget
      have hX : X = exitPoint i t1 := by
        exact (Option.some.inj (hlast_exit.symm.trans hlast)).symm
      have hhead_entry :
          (localArcAtParam i t2).vertices.head? = some (entryPoint i t2) := by
        have hsource := (localArcAtParam i t2).source_eq_head
        rw [(hlocalArcAtParam_props i t2).1] at hsource
        exact hsource
      have hY : Y = entryPoint i t2 := by
        exact (Option.some.inj (hhead_entry.symm.trans hhead)).symm
      have ht12 : t1.1 < t2.1 := by
        have hmap :=
          congrArg
            (List.map (fun t : {t : ℝ // t ∈ centerParams i} => t.1)) hitems
        have hlist_eq : centerParams i =
            pre.map (fun t : {t : ℝ // t ∈ centerParams i} => t.1) ++
              t1.1 :: t2.1 ::
                post.map (fun t : {t : ℝ // t ∈ centerParams i} => t.1) := by
          simpa using hmap
        let n := (pre.map (fun t : {t : ℝ // t ∈ centerParams i} => t.1)).length
        let v1 : ℝ := t1.1
        let v2 : ℝ := t2.1
        have hn1 : n < (centerParams i).length := by
          rw [hlist_eq]
          simp [n]
        have hn2 : n + 1 < (centerParams i).length := by
          rw [hlist_eq]
          simp [n]
        have hget1_opt : (centerParams i)[n]? = some v1 := by
          rw [hlist_eq]
          simp [n, v1]
        have hget2_opt : (centerParams i)[n + 1]? = some v2 := by
          rw [hlist_eq]
          simp [n, v2]
        have hget1 : (centerParams i).get ⟨n, hn1⟩ = t1.1 := by
          have hsome := List.getElem?_eq_getElem hn1
          exact Option.some.inj (hsome.symm.trans (by simpa [v1] using hget1_opt))
        have hget2 : (centerParams i).get ⟨n + 1, hn2⟩ = t2.1 := by
          have hsome := List.getElem?_eq_getElem hn2
          exact Option.some.inj (hsome.symm.trans (by simpa [v2] using hget2_opt))
        have hlt :=
          hcenterParams_sorted i
            (show (⟨n, hn1⟩ : Fin (centerParams i).length) < ⟨n + 1, hn2⟩ by
              simp)
        rwa [hget1, hget2] at hlt
      exact (horderedOutsideGapUnitContainment i t1 t2 ht12).2
        (by simpa [hX, hY] using hpXY) hpA hpB
    · rcases hterminal with ⟨_pre, t, X, _hitems, hlast, hpXB⟩
      have hlast_exit :
          (localArcAtParam i t).vertices.getLast? = some (exitPoint i t) := by
        have htarget := (localArcAtParam i t).target_eq_last
        rw [(hlocalArcAtParam_props i t).2.1] at htarget
        exact htarget
      have hX : X = exitPoint i t := by
        exact (Option.some.inj (hlast_exit.symm.trans hlast)).symm
      have hexit_segment :
          exitPoint i t ∈ segment ℝ (a i) (b i) := by
        have hmem :
            exitPoint i t ∈
              Metric.closedBall (centerOfParam i t) (r (centerOfParam i t)) ∩
                segment ℝ (a i) (b i) := by
          rw [(hentry_exit_local i t).2.2.2.2]
          exact right_mem_segment ℝ (entryPoint i t) (exitPoint i t)
        exact hmem.2
      exact (hchordSubsegmentUnitContainment i hexit_segment
        (right_mem_segment ℝ (a i) (b i))).2
          (by simpa [hX] using hpXB) hpA hpB
  have hassembledVertices_nodup :
      ∀ i, (assembledVertices i).Nodup := by
    intro i
    have hblocks_nodup :
        ∀ t ∈ (centerParams i).attach,
          ((localArcAtParam i t).vertices).Nodup := by
      intro t _ht
      exact (localArcAtParam i t).simple_vertices
    have hblocks_pairwise :
        (((centerParams i).attach).map
            (fun t => (localArcAtParam i t).vertices)).Pairwise List.Disjoint := by
      have hattach_pairwise_lt :
          (centerParams i).attach.Pairwise
            (fun t1 t2 : {t : ℝ // t ∈ centerParams i} => t1.1 < t2.1) := by
        have hmap :
            ((centerParams i).attach.map
                (fun t : {t : ℝ // t ∈ centerParams i} => t.1)).Pairwise
              (fun x y : ℝ => x < y) := by
          simpa [List.attach_map_subtype_val] using
            (List.sortedLT_iff_pairwise.mp (hcenterParams_sorted i))
        rw [List.pairwise_map] at hmap
        exact hmap
      rw [List.pairwise_map]
      exact hattach_pairwise_lt.imp (by
        intro t1 t2 ht12
        rw [List.disjoint_left]
        intro p hp1 hp2
        have hcenter_ne : centerOfParam i t1 ≠ centerOfParam i t2 := by
          intro hsame
          have hparam_eq : t1.1 = t2.1 := by
            have hinj := AffineMap.lineMap_injective (k := ℝ) (hendpoint_ne i)
            exact hinj (by simpa [centerOfParam] using hsame)
          linarith
        have hp1_closed :
            p ∈ Metric.closedBall (centerOfParam i t1) (r (centerOfParam i t1)) :=
          (hlocalArcAtParam_props i t1).2.2.1
            (PolygonalArcVertexMemCarrier (localArcAtParam i t1) hp1)
        have hp2_closed :
            p ∈ Metric.closedBall (centerOfParam i t2) (r (centerOfParam i t2)) :=
          (hlocalArcAtParam_props i t2).2.2.1
            (PolygonalArcVertexMemCarrier (localArcAtParam i t2) hp2)
        exact (Set.disjoint_left.mp
          (hdisjoint (hcenterOfParam_T i t1) (hcenterOfParam_T i t2) hcenter_ne))
          hp1_closed hp2_closed)
    have hA_blocks :
        ∀ t ∈ (centerParams i).attach, a i ∉ (localArcAtParam i t).vertices := by
      intro t _ht hp
      have hp_ball :
          a i ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1 :=
        hclosed (centerOfParam i t) (hcenterOfParam_T i t)
          ((hlocalArcAtParam_props i t).2.2.1
            (PolygonalArcVertexMemCarrier (localArcAtParam i t) hp))
      have hp_dist : dist (a i) (0 : EuclideanSpace ℝ (Fin 2)) < 1 := by
        simpa [Metric.mem_ball] using hp_ball
      linarith [ha i]
    have hB_blocks :
        ∀ t ∈ (centerParams i).attach, b i ∉ (localArcAtParam i t).vertices := by
      intro t _ht hp
      have hp_ball :
          b i ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1 :=
        hclosed (centerOfParam i t) (hcenterOfParam_T i t)
          ((hlocalArcAtParam_props i t).2.2.1
            (PolygonalArcVertexMemCarrier (localArcAtParam i t) hp))
      have hp_dist : dist (b i) (0 : EuclideanSpace ℝ (Fin 2)) < 1 := by
        simpa [Metric.mem_ball] using hp_ball
      linarith [hb i]
    simpa [assembledVertices, orderedLocalVertexBlocks] using
      EndpointUnitDiskAlternatingVertexListNodup
        (A := a i) (B := b i)
        (items := (centerParams i).attach)
        (block := fun t => (localArcAtParam i t).vertices)
        (hendpoint_ne i) hblocks_nodup hblocks_pairwise hA_blocks hB_blocks
  have hlocalEdgeAvoidsAssembledVertices :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}) ⦃q : ℕ⦄,
        (hq : q + 1 < (localArcAtParam i t).vertices.length) →
          ∀ ⦃k : ℕ⦄,
            (hk : k < (assembledVertices i).length) →
              (assembledVertices i)[k] ∉
                openSegment ℝ
                  (localArcAtParam i t).vertices[q]
                  (localArcAtParam i t).vertices[q + 1] := by
    intro i t q hq k hk hpopen
    let Ξ := localArcAtParam i t
    generalize hp_def : (assembledVertices i)[k] = p at hpopen
    have hq_left : q < Ξ.vertices.length := Nat.lt_trans (Nat.lt_succ_self q) hq
    have hpopen_p :
        p ∈ openSegment ℝ Ξ.vertices[q] Ξ.vertices[q + 1] := by
      simpa [Ξ] using hpopen
    have hq_ne :
        Ξ.vertices[q] ≠ Ξ.vertices[q + 1] := by
      intro hsame
      have hidx_eq : q = q + 1 := by
        exact (Ξ.simple_vertices.getElem_inj_iff).1 hsame
      omega
    have hpseg :
        p ∈ segment ℝ Ξ.vertices[q] Ξ.vertices[q + 1] :=
      openSegment_subset_segment ℝ Ξ.vertices[q] Ξ.vertices[q + 1] hpopen_p
    have hp_carrier :
        p ∈ Ξ.carrier := by
      rw [Ξ.carrier_eq]
      exact ⟨q, hq, hpseg⟩
    have hp_closed :
        p ∈
          Metric.closedBall (centerOfParam i t) (r (centerOfParam i t)) := by
      simpa [Ξ] using (hlocalArcAtParam_props i t).2.2.1 hp_carrier
    have hvertex_mem : p ∈ assembledVertices i := by
      rw [← hp_def]
      exact List.getElem_mem hk
    clear hp_def
    simp [assembledVertices, EndpointUnitDiskAlternatingVertexList] at hvertex_mem
    rcases hvertex_mem with hA | hvertex_mem
    · have hA_ball :
          a i ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
        rw [← hA]
        exact hclosed (centerOfParam i t) (hcenterOfParam_T i t) hp_closed
      have hA_dist : dist (a i) (0 : EuclideanSpace ℝ (Fin 2)) < 1 := by
        simpa [Metric.mem_ball] using hA_ball
      linarith [ha i]
    · rcases hvertex_mem with hflat | hB
      · rcases hflat with ⟨V, hV, hpV⟩
        rcases List.mem_map.mp hV with ⟨t', _ht', htV⟩
        rw [← htV] at hpV
        let Ξ' := localArcAtParam i t'
        have hp_carrier' :
            p ∈ Ξ'.carrier :=
          PolygonalArcVertexMemCarrier Ξ' hpV
        have hp_closed' :
            p ∈
              Metric.closedBall (centerOfParam i t') (r (centerOfParam i t')) := by
          simpa [Ξ'] using (hlocalArcAtParam_props i t').2.2.1 hp_carrier'
        by_cases hcenter_eq : centerOfParam i t = centerOfParam i t'
        · have ht_param : t.1 = t'.1 := by
            have hinj := AffineMap.lineMap_injective (k := ℝ) (hendpoint_ne i)
            exact hinj (by simpa [centerOfParam] using hcenter_eq)
          have ht_eq : t = t' := Subtype.ext ht_param
          subst t'
          rcases List.mem_iff_getElem.mp hpV with ⟨l, hl, hget⟩
          by_cases hlq : l = q
          · subst l
            subst p
            exact hq_ne ((left_mem_openSegment_iff (𝕜 := ℝ)
              (x := Ξ.vertices[q]) (y := Ξ.vertices[q + 1])).1 hpopen_p)
          · by_cases hlq1 : l = q + 1
            · subst l
              subst p
              exact hq_ne ((right_mem_openSegment_iff (𝕜 := ℝ)
                (x := Ξ.vertices[q]) (y := Ξ.vertices[q + 1])).1 hpopen_p)
            · subst p
              exact Ξ.vertices_avoid_nonincident_interiors hq hl hlq hlq1 hpopen_p
        · exact (Set.disjoint_left.mp
            (hdisjoint (hcenterOfParam_T i t) (hcenterOfParam_T i t') hcenter_eq))
            hp_closed hp_closed'
      · have hB_ball :
            b i ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
          rw [← hB]
          exact hclosed (centerOfParam i t) (hcenterOfParam_T i t) hp_closed
        have hB_dist : dist (b i) (0 : EuclideanSpace ℝ (Fin 2)) < 1 := by
          simpa [Metric.mem_ball] using hB_ball
        linarith [hb i]
  have hassembledEdgeEndpointRoles :
      ∀ i ⦃m : ℕ⦄,
        (hm : m + 1 < (assembledVertices i).length) →
          ((centerParams i).attach = [] ∧
              (assembledVertices i)[m] = a i ∧
                (assembledVertices i)[m + 1] = b i) ∨
            (∃ t ts X,
              (centerParams i).attach = t :: ts ∧
                (localArcAtParam i t).vertices.head? = some X ∧
                  (assembledVertices i)[m] = a i ∧
                    (assembledVertices i)[m + 1] = X) ∨
            (∃ (pre : List {t : ℝ // t ∈ centerParams i})
                (t : {t : ℝ // t ∈ centerParams i})
                (post : List {t : ℝ // t ∈ centerParams i}) (q : ℕ),
              ∃ hq : q + 1 < (localArcAtParam i t).vertices.length,
                (centerParams i).attach = pre ++ t :: post ∧
                  (assembledVertices i)[m] = (localArcAtParam i t).vertices[q] ∧
                    (assembledVertices i)[m + 1] =
                      (localArcAtParam i t).vertices[q + 1]) ∨
            (∃ (pre : List {t : ℝ // t ∈ centerParams i})
                (t1 : {t : ℝ // t ∈ centerParams i})
                (t2 : {t : ℝ // t ∈ centerParams i})
                (post : List {t : ℝ // t ∈ centerParams i})
                (X Y : EuclideanSpace ℝ (Fin 2)),
              (centerParams i).attach = pre ++ t1 :: t2 :: post ∧
                (localArcAtParam i t1).vertices.getLast? = some X ∧
                  (localArcAtParam i t2).vertices.head? = some Y ∧
                    (assembledVertices i)[m] = X ∧
                      (assembledVertices i)[m + 1] = Y) ∨
            (∃ (pre : List {t : ℝ // t ∈ centerParams i})
                (t : {t : ℝ // t ∈ centerParams i})
                (X : EuclideanSpace ℝ (Fin 2)),
              (centerParams i).attach = pre ++ [t] ∧
                (localArcAtParam i t).vertices.getLast? = some X ∧
                  (assembledVertices i)[m] = X ∧
                    (assembledVertices i)[m + 1] = b i) := by
    intro i m hm
    have hblock_nonempty :
        ∀ t ∈ (centerParams i).attach,
          0 < ((localArcAtParam i t).vertices).length := by
      intro t _ht
      have hlen := (localArcAtParam i t).length_ge_two
      omega
    simpa [assembledVertices, orderedLocalVertexBlocks] using
      EndpointUnitDiskAlternatingVertexListEdgeEndpointRoles
        (A := a i) (B := b i)
        (items := (centerParams i).attach)
        (block := fun t => (localArcAtParam i t).vertices)
        hblock_nonempty
        (m := m)
        (hm := by simpa [assembledVertices, orderedLocalVertexBlocks] using hm)
  have hassembledVertices_avoid :
      ∀ i ⦃m k : ℕ⦄,
        (hm : m + 1 < (assembledVertices i).length) →
          (hk : k < (assembledVertices i).length) →
            k ≠ m →
              k ≠ m + 1 →
                (assembledVertices i)[k] ∉
                  openSegment ℝ
                    (assembledVertices i)[m]
                    (assembledVertices i)[m + 1] := by
    apply endpointUnitDiskAssembly_assembledVerticesAvoid
      a b centerParams localArcAtParam entryPoint exitPoint assembledVertices
    · intro i
      simp [assembledVertices, orderedLocalVertexBlocks,
        EndpointUnitDiskAlternatingVertexList]
    · exact hendpoint_ne
    · exact hcenterParams_sorted
    · exact hentryExitParameters
    · intro i t
      exact ⟨(hlocalArcAtParam_props i t).1,
        (hlocalArcAtParam_props i t).2.1⟩
    · exact horderedCutSeparation
    · exact hchordGapLocalCarrierPosition
    · exact hinitialGapMeetsLocalCarrierOnly
    · exact hterminalGapMeetsLocalCarrierOnly
    · exact horderedOutsideGapMeetsNeighboringLocalCarriersOnly
    · exact hassembledVertices_nodup
    · exact hlocalEdgeAvoidsAssembledVertices
    · exact hassembledEdgeEndpointRoles
  have hlineSegmentInterAdjacent :
      ∀ i {α β γ : ℝ}, α < β → β < γ →
        segment ℝ (AffineMap.lineMap (a i) (b i) α)
            (AffineMap.lineMap (a i) (b i) β) ∩
          segment ℝ (AffineMap.lineMap (a i) (b i) β)
            (AffineMap.lineMap (a i) (b i) γ) =
        {AffineMap.lineMap (a i) (b i) β} := by
    intro i α β γ hαβ hβγ
    let f : ℝ →ᵃ[ℝ] EuclideanSpace ℝ (Fin 2) :=
      AffineMap.lineMap (a i) (b i)
    have hf : Function.Injective f :=
      AffineMap.lineMap_injective (k := ℝ) (hendpoint_ne i)
    have hseg_left : segment ℝ (f α) (f β) = f '' segment ℝ α β := by
      simp [f]
    have hseg_right : segment ℝ (f β) (f γ) = f '' segment ℝ β γ := by
      simp [f]
    rw [hseg_left, hseg_right, ← Set.image_inter hf]
    have hinter : segment ℝ α β ∩ segment ℝ β γ = ({β} : Set ℝ) := by
      rw [segment_eq_Icc hαβ.le, segment_eq_Icc hβγ.le]
      ext x
      constructor
      · intro hx
        exact Set.mem_singleton_iff.mpr (le_antisymm hx.1.2 hx.2.1)
      · intro hx
        rw [Set.mem_singleton_iff] at hx
        subst x
        exact ⟨⟨hαβ.le, le_rfl⟩, ⟨le_rfl, hβγ.le⟩⟩
    rw [hinter]
    simp [f]
  have hlineSegmentInterSeparated :
      ∀ i {α β γ δ : ℝ}, α ≤ β → γ ≤ δ → β < γ →
        segment ℝ (AffineMap.lineMap (a i) (b i) α)
            (AffineMap.lineMap (a i) (b i) β) ∩
          segment ℝ (AffineMap.lineMap (a i) (b i) γ)
            (AffineMap.lineMap (a i) (b i) δ) =
        (∅ : Set (EuclideanSpace ℝ (Fin 2))) := by
    intro i α β γ δ hαβ hγδ hβγ
    let f : ℝ →ᵃ[ℝ] EuclideanSpace ℝ (Fin 2) :=
      AffineMap.lineMap (a i) (b i)
    have hf : Function.Injective f :=
      AffineMap.lineMap_injective (k := ℝ) (hendpoint_ne i)
    have hseg_left : segment ℝ (f α) (f β) = f '' segment ℝ α β := by
      simp [f]
    have hseg_right : segment ℝ (f γ) (f δ) = f '' segment ℝ γ δ := by
      simp [f]
    rw [hseg_left, hseg_right, ← Set.image_inter hf]
    have hinter : segment ℝ α β ∩ segment ℝ γ δ = (∅ : Set ℝ) := by
      rw [segment_eq_Icc hαβ, segment_eq_Icc hγδ]
      ext x
      constructor
      · intro hx
        exfalso
        exact (not_lt_of_ge (le_trans hx.2.1 hx.1.2)) hβγ
      · intro hx
        exact False.elim hx
    rw [hinter]
    simp [f]
  have hsegments :=
    endpointUnitDiskAssembly_segments a b T r centerParams centerOfParam
      (by intro i t; rfl) localArcAtParam entryPoint exitPoint orderedLocalVertexBlocks
      assembledVertices (by intro i; rfl) (by intro i; rfl) hendpoint_ne
      hcenterParams_sorted hcenterOfParam_T hlocalArcAtParam_props
      hentryExitParameters horderedCutSeparation
      hchordGapLocalCarrierPosition hinitialGapMeetsLocalCarrierOnly
      hterminalGapMeetsLocalCarrierOnly
      horderedOutsideGapMeetsNeighboringLocalCarriersOnly hdisjoint
      hassembledVertices_nodup hassembledVertices_avoid
      hassembledEdgeEndpointRoles hlineSegmentInterSeparated
  have hfixedChordArcs :
      ∀ i,
        ∃ Γi : PolygonalArc,
          Γi.vertices = assembledVertices i ∧
            Γi.source = a i ∧
              Γi.target = b i ∧
                Γi.carrier = assembledEdgeSet i ∧
                  Γi.relativeInterior =
                    assembledEdgeSet i \ ({a i, b i} : Set (EuclideanSpace ℝ (Fin 2))) ∧
                    Γi.carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ∧
                      Γi.relativeInterior ⊆
                        Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
    intro i
    simpa [assembledVertices, assembledEdgeSet] using
      EndpointUnitDiskAlternatingVertexListArc
        (A := a i) (B := b i) (blocks := orderedLocalVertexBlocks i)
        (C := Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1)
        (U := Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1)
        (hassembledVertices_nodup i) (hsegments i)
        (hassembledVertices_avoid i) (hassembledEdgeUnitContainment i)
        (hassembledEdgeUnitOpenContainment i)
  choose Gamma hGamma_spec using hfixedChordArcs
  have hentryPoint_open_chord :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}),
        entryPoint i t ∈ openSegment ℝ (a i) (b i) := by
    intro i t
    rcases hentryExitParameters i t with
      ⟨⟨e, he_pos, he_lt_t, hentry⟩, _⟩
    have ht_bounds := hcenterOfParam_bounds i t
    rw [hentry]
    exact lineMap_mem_openSegment (𝕜 := ℝ) (a i) (b i)
      ⟨he_pos, by linarith⟩
  have hexitPoint_open_chord :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}),
        exitPoint i t ∈ openSegment ℝ (a i) (b i) := by
    intro i t
    rcases hentryExitParameters i t with
      ⟨_, ⟨x, ht_lt_x, hx_lt_one, hexit⟩⟩
    have ht_bounds := hcenterOfParam_bounds i t
    rw [hexit]
    exact lineMap_mem_openSegment (𝕜 := ℝ) (a i) (b i)
      ⟨by linarith, hx_lt_one⟩
  have hchosenCenterOnChord_param :
      ∀ i ⦃z : EuclideanSpace ℝ (Fin 2)⦄,
        z ∈ T →
          z ∈ segment ℝ (a i) (b i) →
            ∃ t : {t : ℝ // t ∈ centerParams i}, centerOfParam i t = z := by
    intro i z hzT hzseg
    have hz_unit :
        z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1 :=
      ((hT z).1 hzT).1
    have hz_dist : dist z (0 : EuclideanSpace ℝ (Fin 2)) < 1 := by
      simpa [Metric.mem_ball] using hz_unit
    have hz_ne_a : z ≠ a i := by
      intro hz_eq
      subst z
      linarith [ha i]
    have hz_ne_b : z ≠ b i := by
      intro hz_eq
      subst z
      linarith [hb i]
    have hzopen : z ∈ openSegment ℝ (a i) (b i) :=
      mem_openSegment_of_ne_left_right (𝕜 := ℝ)
        hz_ne_a.symm hz_ne_b.symm hzseg
    rw [openSegment_eq_image_lineMap] at hzopen
    rcases hzopen with ⟨s, hs, hzs⟩
    have hs_mem : s ∈ centerParams i := by
      exact (hcenterParams_mem i s).2
        ⟨hs.1, hs.2, by simpa [hzs] using hzT⟩
    refine ⟨⟨s, hs_mem⟩, ?_⟩
    simpa [centerOfParam] using hzs
  have hattach_pairwise_lt_all :
      ∀ i,
        (centerParams i).attach.Pairwise
          (fun t1 t2 : {t : ℝ // t ∈ centerParams i} => t1.1 < t2.1) := by
    intro i
    have hmap :
        ((centerParams i).attach.map
            (fun t : {t : ℝ // t ∈ centerParams i} => t.1)).Pairwise
          (fun x y : ℝ => x < y) := by
      simpa [List.attach_map_subtype_val] using
        (List.sortedLT_iff_pairwise.mp (hcenterParams_sorted i))
    rw [List.pairwise_map] at hmap
    exact hmap
  have hchordGapDiskPosition :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}) {α β e x : ℝ},
        entryPoint i t = AffineMap.lineMap (a i) (b i) e →
          exitPoint i t = AffineMap.lineMap (a i) (b i) x →
            0 ≤ α → α ≤ β → β ≤ 1 → e < x →
              (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
                p ∈ segment ℝ (AffineMap.lineMap (a i) (b i) α)
                    (AffineMap.lineMap (a i) (b i) β) →
                  p ∈ Metric.closedBall (centerOfParam i t) (r (centerOfParam i t)) →
                    β < e → False) ∧
                (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
                  p ∈ segment ℝ (AffineMap.lineMap (a i) (b i) α)
                      (AffineMap.lineMap (a i) (b i) β) →
                    p ∈ Metric.closedBall (centerOfParam i t) (r (centerOfParam i t)) →
                      β = e → p = entryPoint i t) ∧
                  (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
                    p ∈ segment ℝ (AffineMap.lineMap (a i) (b i) α)
                        (AffineMap.lineMap (a i) (b i) β) →
                      p ∈ Metric.closedBall (centerOfParam i t) (r (centerOfParam i t)) →
                        x < α → False) ∧
                    (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
                      p ∈ segment ℝ (AffineMap.lineMap (a i) (b i) α)
                          (AffineMap.lineMap (a i) (b i) β) →
                        p ∈ Metric.closedBall (centerOfParam i t) (r (centerOfParam i t)) →
                          x = α → p = exitPoint i t) := by
    intro i t α β e x hentry hexit hα0 hαβ hβ1 hex
    exact EndpointUnitDiskChordGapCutDiskIntersections
      (A := a i) (B := b i) (z := centerOfParam i t)
      (u := entryPoint i t) (v := exitPoint i t)
      (rho := r (centerOfParam i t)) (α := α) (β := β) (e := e) (x := x)
      (hendpoint_ne i) (hentry_exit_local i t).2.2.2.2 hentry hexit
      hα0 hαβ hβ1 hex
  have hfinalPointRoles :=
    endpointUnitDiskAssembly_finalPointRoles a b ha hb T r hT hmiss
      centerParams centerOfParam localArcAtParam entryPoint exitPoint
      assembledVertices assembledEdgeSet (by intro i p; rfl) Gamma
      (fun i => (hGamma_spec i).2.2.2.2.1)
      hassembledEdgeEndpointRoles hcenterParams_mem hlocalArcAtParam_props
      hentry_exit_local hentryPoint_open_chord hexitPoint_open_chord
      hchosenCenterOnChord_param hentryExitParameters horderedCutSeparation
      hattach_pairwise_lt_all hendpoint_ne hchordGapDiskPosition
  have hsplicePoint_not_other :=
    endpointUnitDiskAssembly_splicePoint_not_other
      a b T r centerParams centerOfParam localArcAtParam entryPoint exitPoint
      Gamma hrpos hdisjoint hmiss hpairOnly hcenterOfParam_T hfinalPointRoles
  have hsharedPointRoles :
      ∀ ⦃i j : ι⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        i ≠ j →
          p ∈ (Gamma i).relativeInterior →
            p ∈ (Gamma j).relativeInterior →
              ((p ∈ openSegment ℝ (a i) (b i) ∧
                    ∀ z : EuclideanSpace ℝ (Fin 2),
                      z ∈ T → p ∉ Metric.closedBall z (r z)) ∧
                  (p ∈ openSegment ℝ (a j) (b j) ∧
                    ∀ z : EuclideanSpace ℝ (Fin 2),
                      z ∈ T → p ∉ Metric.closedBall z (r z))) ∨
                (∃ (z : Center) (ii jj : Incident z.1),
                  ii.1 = i ∧ jj.1 = j ∧
                    p ∈ (localXi z ii).relativeInterior ∧
                      p ∈ (localXi z jj).relativeInterior) := by
    intro i j p hij hpi hpj
    rcases hfinalPointRoles i hpi with houtside_i | hlocal_or_splice_i
    · rcases hfinalPointRoles j hpj with houtside_j | hlocal_or_splice_j
      · exact Or.inl ⟨houtside_i, houtside_j⟩
      rcases hlocal_or_splice_j with hlocal_j | hsplice_j
      · rcases hlocal_j with ⟨tj, _hpj_local, hpj_ball⟩
        have hpj_closed :
            p ∈ Metric.closedBall (centerOfParam j tj) (r (centerOfParam j tj)) :=
          Metric.ball_subset_closedBall hpj_ball
        exact False.elim
          (houtside_i.2 (centerOfParam j tj) (hcenterOfParam_T j tj) hpj_closed)
      · rcases hsplice_j with ⟨tj, hsplice_j⟩
        have hji : j ≠ i := by
          intro hji
          exact hij hji.symm
        exact False.elim
          (hsplicePoint_not_other (i := j) (j := i) (p := p) tj hji hsplice_j hpi)
    rcases hlocal_or_splice_i with hlocal_i | hsplice_i
    · rcases hlocal_i with ⟨ti, hpi_local, hpi_ball⟩
      rcases hfinalPointRoles j hpj with houtside_j | hlocal_or_splice_j
      · have hpi_closed :
            p ∈ Metric.closedBall (centerOfParam i ti) (r (centerOfParam i ti)) :=
          Metric.ball_subset_closedBall hpi_ball
        exact False.elim
          (houtside_j.2 (centerOfParam i ti) (hcenterOfParam_T i ti) hpi_closed)
      rcases hlocal_or_splice_j with hlocal_j | hsplice_j
      · rcases hlocal_j with ⟨tj, hpj_local, _hpj_ball⟩
        have hcenter_eq :
            centerOfParam i ti = centerOfParam j tj :=
          hlocalSameCenter (hcenterOfParam_T i ti) (hcenterOfParam_T j tj)
            (hlocalArcAtParam_props i ti).2.2.1
            (hlocalArcAtParam_props j tj).2.2.1 hpi_local hpj_local
        let z : Center := centerAtParam i ti
        let ii : Incident z.1 := incidentAtParam i ti
        let jj : Incident z.1 :=
          ⟨j, by
            simpa [z, centerAtParam, hcenter_eq] using hcenterOfParam_open j tj⟩
        refine Or.inr ⟨z, ii, jj, rfl, rfl, ?_, ?_⟩
        · simpa [z, ii, localArcAtParam, centerAtParam, incidentAtParam] using hpi_local
        · dsimp [z, jj, localArcAtParam, centerAtParam, incidentAtParam]
          dsimp [localArcAtParam, centerAtParam, incidentAtParam] at hpj_local
          convert hpj_local using 4
          funext k
          simp [hcenter_eq]
      · rcases hsplice_j with ⟨tj, hsplice_j⟩
        have hji : j ≠ i := by
          intro hji
          exact hij hji.symm
        exact False.elim
          (hsplicePoint_not_other (i := j) (j := i) (p := p) tj hji hsplice_j hpi)
    · rcases hsplice_i with ⟨ti, hsplice_i⟩
      exact False.elim
        (hsplicePoint_not_other (i := i) (j := j) (p := p) ti hij hsplice_i hpj)
  have hsharedPointTransverseRoles :=
    endpointUnitDiskAssembly_sharedPointTransverseRoles
      a b T r Gamma localXi hsharedPointRoles hchordControl.2.2.2.2
      (fun z => (hlocalAtCenter_spec z).2.2.2.2.1)
  have hsharedPointUnique :
      ∀ ⦃i j : ι⦄ ⦃p q : EuclideanSpace ℝ (Fin 2)⦄,
        i ≠ j →
          p ∈ (Gamma i).relativeInterior →
            p ∈ (Gamma j).relativeInterior →
              q ∈ (Gamma i).relativeInterior →
                q ∈ (Gamma j).relativeInterior →
                  p = q := by
    intro i j p q hij hpi hpj hqi hqj
    rcases hsharedPointRoles hij hpi hpj with hp_outside | hp_local
    · rcases hsharedPointRoles hij hqi hqj with hq_outside | hq_local
      · exact hchordControl.2.2.2.1 hij hp_outside.1.1 hp_outside.2.1
          hq_outside.1.1 hq_outside.2.1
      · rcases hq_local with ⟨zq, iq, jq, hiq, hjq, _hqiq, _hqjq⟩
        have hzq_i : zq.1 ∈ openSegment ℝ (a i) (b i) := by
          simpa [hiq] using iq.2
        have hzq_j : zq.1 ∈ openSegment ℝ (a j) (b j) := by
          simpa [hjq] using jq.2
        have hp_eq_zq : p = zq.1 :=
          hchordControl.2.2.2.1 hij hp_outside.1.1 hp_outside.2.1 hzq_i hzq_j
        have hzq_closed : zq.1 ∈ Metric.closedBall zq.1 (r zq.1) := by
          rw [Metric.mem_closedBall, dist_self]
          exact le_of_lt (hrpos zq.1 zq.2)
        have hp_closed : p ∈ Metric.closedBall zq.1 (r zq.1) := by
          simpa [hp_eq_zq] using hzq_closed
        exact False.elim (hp_outside.1.2 zq.1 zq.2 hp_closed)
    · rcases hp_local with ⟨zp, ip, jp, hip, hjp, hpip, hpjp⟩
      rcases hsharedPointRoles hij hqi hqj with hq_outside | hq_local
      · have hzp_i : zp.1 ∈ openSegment ℝ (a i) (b i) := by
          simpa [hip] using ip.2
        have hzp_j : zp.1 ∈ openSegment ℝ (a j) (b j) := by
          simpa [hjp] using jp.2
        have hq_eq_zp : q = zp.1 :=
          hchordControl.2.2.2.1 hij hq_outside.1.1 hq_outside.2.1 hzp_i hzp_j
        have hzp_closed : zp.1 ∈ Metric.closedBall zp.1 (r zp.1) := by
          rw [Metric.mem_closedBall, dist_self]
          exact le_of_lt (hrpos zp.1 zp.2)
        have hq_closed : q ∈ Metric.closedBall zp.1 (r zp.1) := by
          simpa [hq_eq_zp] using hzp_closed
        exact False.elim (hq_outside.1.2 zp.1 zp.2 hq_closed)
      · rcases hq_local with ⟨zq, iq, jq, hiq, hjq, hqiq, hqjq⟩
        have hzp_i : zp.1 ∈ openSegment ℝ (a i) (b i) := by
          simpa [hip] using ip.2
        have hzp_j : zp.1 ∈ openSegment ℝ (a j) (b j) := by
          simpa [hjp] using jp.2
        have hzq_i : zq.1 ∈ openSegment ℝ (a i) (b i) := by
          simpa [hiq] using iq.2
        have hzq_j : zq.1 ∈ openSegment ℝ (a j) (b j) := by
          simpa [hjq] using jq.2
        have hz_val : zp.1 = zq.1 :=
          hchordControl.2.2.2.1 hij hzp_i hzp_j hzq_i hzq_j
        have hz_eq : zp = zq := Subtype.ext hz_val
        subst zq
        have hi_eq : ip = iq := by
          apply Subtype.ext
          rw [hip, hiq]
        have hj_eq : jp = jq := by
          apply Subtype.ext
          rw [hjp, hjq]
        subst iq
        subst jq
        have hij_inc : ip ≠ jp := by
          intro hipj
          apply hij
          have hval : ip.1 = jp.1 := congrArg Subtype.val hipj
          rwa [hip, hjp] at hval
        exact (hlocalAtCenter_spec zp).2.2.2.2.2.1 hij_inc hpip hpjp hqiq hqjq
  have hlineMapVecLeft :
      ∀ (A B : EuclideanSpace ℝ (Fin 2)) (e : ℝ),
        AffineMap.lineMap A B e - A = e • (B - A) := by
    intro A B e
    simp [AffineMap.lineMap_apply_module]
    module
  have hlineMapVecBetween :
      ∀ (A B : EuclideanSpace ℝ (Fin 2)) (x y : ℝ),
        AffineMap.lineMap A B y - AffineMap.lineMap A B x =
          (y - x) • (B - A) := by
    intro A B x y
    simp [AffineMap.lineMap_apply_module, sub_smul]
    module
  have hlineMapVecRight :
      ∀ (A B : EuclideanSpace ℝ (Fin 2)) (x : ℝ),
        B - AffineMap.lineMap A B x = (1 - x) • (B - A) := by
    intro A B x
    simp [AffineMap.lineMap_apply_module, sub_smul]
    module
  have hscalarTransfer :
      ∀ {vi vj ei ej : EuclideanSpace ℝ (Fin 2)} {ci cj t : ℝ},
        cj ≠ 0 →
          ei = ci • vi →
            ej = cj • vj →
              ej = t • ei →
                vj = (cj⁻¹ * t * ci) • vi := by
    intro vi vj ei ej ci cj t hcj hi hj h
    rw [hj, hi] at h
    have hscaled := congrArg (fun x : EuclideanSpace ℝ (Fin 2) => cj⁻¹ • x) h
    simpa [smul_smul, mul_assoc, mul_left_comm, mul_comm, hcj] using hscaled
  have horderedLocalVertexBlocks_def :
      ∀ i,
        orderedLocalVertexBlocks i =
          (centerParams i).attach.map
            (fun t => (localArcAtParam i t).vertices) := by
    intro i
    rfl
  have hassembledVertices_def :
      ∀ i,
        assembledVertices i =
          EndpointUnitDiskAlternatingVertexList
            (a i) (b i) (orderedLocalVertexBlocks i) := by
    intro i
    rfl
  have hassembledEdgeSet_mem :
      ∀ i p,
        p ∈ assembledEdgeSet i ↔
          ∃ m : ℕ, ∃ hm : m + 1 < (assembledVertices i).length,
            p ∈ segment ℝ (assembledVertices i)[m]
              (assembledVertices i)[m + 1] := by
    intro i p
    rfl
  have hcenterAtParam_val :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}),
        (centerAtParam i t).1 = centerOfParam i t := by
    intro i t
    rfl
  have hincidentAtParam_val :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}),
        (incidentAtParam i t).1 = i := by
    intro i t
    rfl
  have hlocalArcAtParam_def :
      ∀ i (t : {t : ℝ // t ∈ centerParams i}),
        localArcAtParam i t =
          localXi (centerAtParam i t) (incidentAtParam i t) := by
    intro i t
    rfl
  have hlocalEdgeInAssembled :=
    endpointUnitDiskAssembly_localEdgeInAssembled
      a b centerParams localArcAtParam orderedLocalVertexBlocks
      assembledVertices horderedLocalVertexBlocks_def hassembledVertices_def
  have houtsideEdgeDirection :=
    endpointUnitDiskAssembly_outsideEdgeDirection
      a b T r centerParams centerOfParam localArcAtParam entryPoint exitPoint
      assembledVertices hassembledEdgeEndpointRoles hlocalArcAtParam_props
      hcenterOfParam_T hentryExitParameters hattach_pairwise_lt_all
      horderedCutSeparation hendpoint_ne hlineMapVecLeft hlineMapVecBetween
      hlineMapVecRight
  have hGammaInteriorEdges :=
    endpointUnitDiskAssembly_interiorEdgeWitness
      a b assembledVertices assembledEdgeSet Gamma hassembledEdgeSet_mem
      (fun i => (hGamma_spec i).2.2.2.2.1)
  have hlocalArcRealize :=
    endpointUnitDiskAssembly_localArcRealize
      a b T centerParams centerOfParam centerAtParam incidentAtParam
      localXi localArcAtParam hcenterAtParam_val hincidentAtParam_val
      hlocalArcAtParam_def hchosenCenterOnChord_param
  have hsharedPointTransverse :=
    endpointUnitDiskAssembly_sharedPointTransverse
      a b T r centerParams localArcAtParam assembledVertices Gamma localXi
      (fun i => (hGamma_spec i).1) hGammaInteriorEdges
      hsharedPointTransverseRoles hlocalArcRealize hlocalEdgeInAssembled
      houtsideEdgeDirection hscalarTransfer
  have hassembledVertices_cases :=
    endpointUnitDiskAssembly_assembledVertexCases
      a b centerParams localArcAtParam orderedLocalVertexBlocks
      assembledVertices horderedLocalVertexBlocks_def hassembledVertices_def
  have hsharedPointOpen :=
    endpointUnitDiskAssembly_sharedPointOpen
      a b T r centerParams centerOfParam localArcAtParam assembledVertices
      Gamma localXi hsharedPointRoles hendpoint_ne
      (fun i => (hGamma_spec i).1) hGammaInteriorEdges
      hassembledVertices_cases
      (fun i t => (hlocalArcAtParam_props i t).2.2.1)
      hcenterOfParam_T
      (fun z => (hlocalAtCenter_spec z).2.2.2.2.2.2)
      hlocalArcRealize hlocalEdgeInAssembled
  have hnoTriple :=
    endpointUnitDiskAssembly_noTriple
      a b T r hT hrpos hdisjoint Gamma localXi hsharedPointRoles
      (fun i => (hGamma_spec i).2.2.2.2.2.2)
      (fun z ii => ((hlocalAtCenter_spec z).2.1 ii).2.2.1)
      (fun z ii => ((hlocalAtCenter_spec z).2.1 ii).2.2.2)
      (fun z => (hlocalAtCenter_spec z).2.2.2.1)
  have hclean :=
    endpointUnitDiskAssembly_clean
      a b ha hb Gamma
      (fun i => (hGamma_spec i).2.1)
      (fun i => (hGamma_spec i).2.2.1)
      (fun i => (hGamma_spec i).2.2.2.2.2.2)
      hsharedPointOpen hsharedPointTransverse hnoTriple hsharedPointUnique
  have hGammaProperties :
      ∀ i,
        (Gamma i).source = a i ∧
          (Gamma i).target = b i ∧
            (Gamma i).carrier ⊆
                Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ∧
              (Gamma i).relativeInterior ⊆
                Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
    intro i
    exact ⟨(hGamma_spec i).2.1,
      (hGamma_spec i).2.2.1,
      (hGamma_spec i).2.2.2.2.2.1,
      (hGamma_spec i).2.2.2.2.2.2⟩
  have hnoCommonSegment :=
    endpointUnitDiskAssembly_noCommonSegment Gamma hsharedPointUnique
  exact
    { Gamma := Gamma
      properties := hGammaProperties
      noCommonSegment := hnoCommonSegment
      noTriple := hnoTriple
      transverse := hsharedPointTransverse
      unique := hsharedPointUnique
      clean := hclean }

lemma EndpointUnitDiskAssemblyFromLocalReplacements {ι : Type*} [Fintype ι]
    (a b : ι → EuclideanSpace ℝ (Fin 2))
    (ha : ∀ i, dist (a i) (0 : EuclideanSpace ℝ (Fin 2)) = 1)
    (hb : ∀ i, dist (b i) (0 : EuclideanSpace ℝ (Fin 2)) = 1)
    (hdistinct : Function.Injective (fun x : ι ⊕ ι => Sum.elim a b x))
    (T : Finset (EuclideanSpace ℝ (Fin 2)))
    (r : EuclideanSpace ℝ (Fin 2) → ℝ)
    (hT : ∀ z, z ∈ T ↔
      z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1 ∧
        ∃ i j k : ι,
          i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
            z ∈ openSegment ℝ (a i) (b i) ∧
              z ∈ openSegment ℝ (a j) (b j) ∧
                z ∈ openSegment ℝ (a k) (b k))
    (hrpos : ∀ z ∈ T, 0 < r z)
    (hclosed : ∀ z ∈ T,
      Metric.closedBall z (r z) ⊆
        Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1)
    (hdisjoint : ∀ ⦃z w : EuclideanSpace ℝ (Fin 2)⦄,
      z ∈ T → w ∈ T → z ≠ w →
        Disjoint (Metric.closedBall z (r z)) (Metric.closedBall w (r w)))
    (hmiss : ∀ ⦃z : EuclideanSpace ℝ (Fin 2)⦄,
      z ∈ T → ∀ i,
        z ∉ segment ℝ (a i) (b i) →
          Disjoint (Metric.closedBall z (r z)) (segment ℝ (a i) (b i)))
    (hpairOnly : ∀ ⦃z y : EuclideanSpace ℝ (Fin 2)⦄,
      z ∈ T →
        y ∈ Metric.closedBall z (r z) →
          (∃ i j : ι,
            i ≠ j ∧
              y ∈ segment ℝ (a i) (b i) ∧
                y ∈ segment ℝ (a j) (b j)) →
            y = z)
    (hlocal : ∀ z, z ∈ T →
      let κ := {i : ι // z ∈ openSegment ℝ (a i) (b i)}
      ∃ u v : κ → EuclideanSpace ℝ (Fin 2),
        ∃ Ξ : κ → PolygonalArc,
          (∀ i : κ,
            u i ∈ Metric.sphere z (r z) ∧
              v i ∈ Metric.sphere z (r z) ∧
                u i ∈ openSegment ℝ (a i.1) z ∧
                  v i ∈ openSegment ℝ z (b i.1) ∧
                    Metric.closedBall z (r z) ∩ segment ℝ (a i.1) (b i.1) =
                      segment ℝ (u i) (v i)) ∧
            (∀ i : κ,
              (Ξ i).source = u i ∧
                (Ξ i).target = v i ∧
                  (Ξ i).carrier ⊆ Metric.closedBall z (r z) ∧
                    (Ξ i).relativeInterior ⊆ Metric.ball z (r z)) ∧
              (∀ ⦃i j : κ⦄,
                i ≠ j →
                  ¬ ∃ m n : ℕ,
                    ∃ (hm : m + 1 < (Ξ i).vertices.length)
                      (hn : n + 1 < (Ξ j).vertices.length),
                      ∃ p q : EuclideanSpace ℝ (Fin 2),
                        p ≠ q ∧
                          segment ℝ p q ⊆
                            segment ℝ (Ξ i).vertices[m] (Ξ i).vertices[m + 1] ∩
                              segment ℝ (Ξ j).vertices[n] (Ξ j).vertices[n + 1]) ∧
                (∀ ⦃i j k : κ⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
                  i ≠ j → i ≠ k → j ≠ k →
                    p ∈ (Ξ i).relativeInterior →
                      p ∈ (Ξ j).relativeInterior →
                        p ∈ (Ξ k).relativeInterior → False) ∧
                  (∀ ⦃i j : κ⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
                    i ≠ j →
                      p ∈ (Ξ i).relativeInterior →
                        p ∈ (Ξ j).relativeInterior →
                          ∃ m n : ℕ,
                            ∃ (hm : m + 1 < (Ξ i).vertices.length)
                              (hn : n + 1 < (Ξ j).vertices.length),
                              p ∈ segment ℝ (Ξ i).vertices[m] (Ξ i).vertices[m + 1] ∧
                                p ∈ segment ℝ (Ξ j).vertices[n] (Ξ j).vertices[n + 1] ∧
                                  ¬ ∃ t : ℝ,
                                    (Ξ j).vertices[n + 1] - (Ξ j).vertices[n] =
                                      t • ((Ξ i).vertices[m + 1] -
                                        (Ξ i).vertices[m])) ∧
                    (∀ ⦃i j : κ⦄ ⦃p q : EuclideanSpace ℝ (Fin 2)⦄,
                      i ≠ j →
                        p ∈ (Ξ i).relativeInterior →
                          p ∈ (Ξ j).relativeInterior →
                            q ∈ (Ξ i).relativeInterior →
                              q ∈ (Ξ j).relativeInterior →
                                p = q) ∧
                    (∀ ⦃i j : κ⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
                      i ≠ j →
                        p ∈ (Ξ i).relativeInterior →
                          p ∈ (Ξ j).relativeInterior →
                            Nonempty (OrdinaryCleanLocalCrossing Ξ i j p))) :
    ∃ Γ : ι → PolygonalArc,
      (∀ i,
        (Γ i).source = a i ∧
          (Γ i).target = b i ∧
            (Γ i).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ∧
              (Γ i).relativeInterior ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1) ∧
      (∀ ⦃i j : ι⦄,
        i ≠ j →
          ¬ ∃ m n : ℕ,
            ∃ (hm : m + 1 < (Γ i).vertices.length)
              (hn : n + 1 < (Γ j).vertices.length),
              ∃ p q : EuclideanSpace ℝ (Fin 2),
                p ≠ q ∧
                  segment ℝ p q ⊆
                    segment ℝ (Γ i).vertices[m] (Γ i).vertices[m + 1] ∩
                      segment ℝ (Γ j).vertices[n] (Γ j).vertices[n + 1]) ∧
      (∀ ⦃i j k : ι⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        i ≠ j → i ≠ k → j ≠ k →
          p ∈ (Γ i).relativeInterior →
            p ∈ (Γ j).relativeInterior →
              p ∈ (Γ k).relativeInterior → False) ∧
      (∀ ⦃i j : ι⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        i ≠ j →
          p ∈ (Γ i).relativeInterior →
            p ∈ (Γ j).relativeInterior →
              ∃ m n : ℕ,
                ∃ (hm : m + 1 < (Γ i).vertices.length)
                  (hn : n + 1 < (Γ j).vertices.length),
                  p ∈ segment ℝ (Γ i).vertices[m] (Γ i).vertices[m + 1] ∧
                    p ∈ segment ℝ (Γ j).vertices[n] (Γ j).vertices[n + 1] ∧
                      ¬ ∃ t : ℝ,
                        (Γ j).vertices[n + 1] - (Γ j).vertices[n] =
                          t • ((Γ i).vertices[m + 1] - (Γ i).vertices[m])) ∧
      (∀ ⦃i j : ι⦄ ⦃p q : EuclideanSpace ℝ (Fin 2)⦄,
        i ≠ j →
          p ∈ (Γ i).relativeInterior →
            p ∈ (Γ j).relativeInterior →
              q ∈ (Γ i).relativeInterior →
                q ∈ (Γ j).relativeInterior →
                  p = q) ∧
      (∀ ⦃i j : ι⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        i ≠ j →
          p ∈ (Γ i).relativeInterior →
            p ∈ (Γ j).relativeInterior →
              Nonempty (OrdinaryCleanLocalCrossing Γ i j p)) := by
  let P :=
    endpointUnitDiskAssembly_prepare
      a b ha hb hdistinct T r hT hrpos hclosed hdisjoint hmiss hpairOnly hlocal
  exact ⟨P.Gamma, P.properties, P.noCommonSegment, P.noTriple,
    P.transverse, P.unique, P.clean⟩
