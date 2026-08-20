import ErdosProblems.Erdos733.ST.ArcCrossingAttachmentClearance
import ErdosProblems.Erdos733.ST.ArcCrossingCollarBridgeData
import ErdosProblems.Erdos733.ST.ArcCrossingFirstSegmentPrefixPoint
import ErdosProblems.Erdos733.ST.ArcCrossingFirstSegmentIndex
import ErdosProblems.Erdos733.ST.ArcCrossingOrderedTailArc
import ErdosProblems.Erdos733.ST.ArcCrossingOrientedCrossingData
import ErdosProblems.Erdos733.ST.ArcCrossingTailSourcePrefixData
import ErdosProblems.Erdos733.ST.ArcCrossingTerminalSlitDiskData
import ErdosProblems.Erdos733.ST.ComplementComponent
import ErdosProblems.Erdos733.ST.FinitePolygonalSet
import ErdosProblems.Erdos733.ST.OpenConnectedComponentPolygonallyConnected
import ErdosProblems.Erdos733.ST.PlanarSlitDiskEndpointConesAvoidRay
import ErdosProblems.Erdos733.ST.PolygonalArc
import ErdosProblems.Erdos733.ST.PolygonalArcCollarCompatibleOrientedTubeData
import ErdosProblems.Erdos733.ST.PolygonalArcCollarCompatibleOrientedTubeDataExistsBelow
import ErdosProblems.Erdos733.ST.PolygonalArcCollarControlRadiiExistsBelow
import ErdosProblems.Erdos733.ST.PolygonalArcCollarLocalSideData
import ErdosProblems.Erdos733.ST.PolygonalArcCollarLocalSideDataExistsWithEndpointLeftCones
import ErdosProblems.Erdos733.ST.PolygonalArcCollarMiddleForbiddenMarginsExists
import ErdosProblems.Erdos733.ST.PolygonalArcCollarMiddleSegmentDataExists
import ErdosProblems.Erdos733.ST.PolygonalArcCollarOrientedSeparatedTubeData
import ErdosProblems.Erdos733.ST.PolygonalArcCollarSeparatedTubeData
import ErdosProblems.Erdos733.ST.PolygonalArcCollarVertexLocalPieceData
import ErdosProblems.Erdos733.ST.PolygonalArcEndpointIsolation
import ErdosProblems.Erdos733.ST.PolygonalArcEndpointIsolationExists
import ErdosProblems.Erdos733.ST.PolygonalArcInitialEndpointCone
import ErdosProblems.Erdos733.ST.PolygonalArcInitialEndpointLeftCone
import ErdosProblems.Erdos733.ST.PolygonalArcReverse
import ErdosProblems.Erdos733.ST.PolygonalArcSideStripAssembly
import ErdosProblems.Erdos733.ST.PolygonalArcTerminalEndpointLeftCone
import ErdosProblems.Erdos733.ST.PolygonalPathFiniteOccurrenceLocalCuts
import ErdosProblems.Erdos733.ST.PolygonalPathInGeneralPosition
import ErdosProblems.Erdos733.ST.PolygonallyPathConnected
import ErdosProblems.Erdos733.ST.PolygonalSideStrips
import ErdosProblems.Erdos733.ST.PositiveSeparation

open Classical
noncomputable section

-- [TABLET NODE: ArcCrossingBypassRegionData]
lemma ArcCrossingBypassRegionData
    (K : Set (EuclideanSpace ℝ (Fin 2))) (γ : PolygonalArc)
    (Γ : FinitePolygonalSet) (α : PolygonalPath) :
    IsCompact K →
      Γ.carrier = γ.carrier →
        (∀ v : EuclideanSpace ℝ (Fin 2), v ∈ γ.vertices → v ∈ Γ.points) →
          α.carrier ⊆ Kᶜ →
            α.source ∈ (K ∪ γ.carrier)ᶜ →
              α.target ∈ (K ∪ γ.carrier)ᶜ →
                γ.source ∉ α.carrier →
                  γ.target ∉ α.carrier →
                    PolygonalPathInGeneralPosition α Γ →
                      ((γ.carrier ∩ K =
                          ({γ.source} : Set (EuclideanSpace ℝ (Fin 2))) ∧
                            γ.target ∉ K) ∨
                        (γ.carrier ∩ K =
                          ({γ.target} : Set (EuclideanSpace ℝ (Fin 2))) ∧
                            γ.source ∉ K)) →
                        (α.carrier ∩ γ.carrier).Nonempty →
                          ∃ (W : Set (EuclideanSpace ℝ (Fin 2)))
                            (cutBefore cutAfter :
                              ∀ (i : ℕ), i + 1 < α.vertices.length →
                                EuclideanSpace ℝ (Fin 2) →
                                  EuclideanSpace ℝ (Fin 2)),
                            W ⊆ (K ∪ γ.carrier)ᶜ ∧
                              PolygonallyPathConnected W ∧
                                (∀ (i : ℕ) (hi : i + 1 < α.vertices.length)
                                    (x : EuclideanSpace ℝ (Fin 2)),
                                    x ∈ openSegment ℝ α.vertices[i]
                                        α.vertices[i + 1] →
                                      x ∈ γ.carrier →
                                        cutBefore i hi x ∈
                                            openSegment ℝ α.vertices[i] x ∧
                                          cutAfter i hi x ∈
                                            openSegment ℝ x α.vertices[i + 1] ∧
                                            cutBefore i hi x ∈ W ∧
                                              cutAfter i hi x ∈ W ∧
                                                segment ℝ (cutBefore i hi x)
                                                    (cutAfter i hi x) ∩
                                                    γ.carrier =
                                                  {x}) ∧
                                  (∀ (i : ℕ) (hi : i + 1 < α.vertices.length)
                                      (x y : EuclideanSpace ℝ (Fin 2)),
                                      x ∈ openSegment ℝ α.vertices[i]
                                          α.vertices[i + 1] →
                                        y ∈ openSegment ℝ α.vertices[i]
                                            α.vertices[i + 1] →
                                          x ∈ γ.carrier →
                                            y ∈ γ.carrier →
                                              x ≠ y →
                                                Disjoint
                                                  (segment ℝ (cutBefore i hi x)
                                                    (cutAfter i hi x))
                                                  (segment ℝ (cutBefore i hi y)
                                                    (cutAfter i hi y))) ∧
                                    (∀ (i : ℕ) (hi : i + 1 < α.vertices.length)
                                        (y : EuclideanSpace ℝ (Fin 2)),
                                        y ∈ segment ℝ α.vertices[i]
                                            α.vertices[i + 1] →
                                          y ∈ γ.carrier →
                                            ∃ x : EuclideanSpace ℝ (Fin 2),
                                              x ∈ openSegment ℝ α.vertices[i]
                                                  α.vertices[i + 1] ∧
                                                x ∈ γ.carrier ∧
                                                  y ∈ segment ℝ (cutBefore i hi x)
                                                    (cutAfter i hi x)) := by
-- BODY
  intro hK hΓcarrier hγvertices hαK hαsource hαtarget hγsourceα hγtargetα
    hgp hattach hXnonempty
  obtain ⟨δ, hδcarrier, hδrelativeInterior, hδvertices, hδverticesAvoid,
      hXfiniteδ, hδsourceα, hδtargetα, hδK, hδtargetK⟩ :=
    ArcCrossingOrientedCrossingData K γ Γ α hΓcarrier hγvertices hγsourceα
      hγtargetα hgp hattach
  have hXnonemptyδ : (α.carrier ∩ δ.carrier).Nonempty := by
    rwa [hδcarrier]
  obtain ⟨ε, hεpos, hεle_dist, hδfarCompact, hδfarDisjointK⟩ :=
    ArcCrossingAttachmentClearance K δ α δ.source hδsourceα hXfiniteδ
      hXnonemptyδ hδK
  obtain ⟨j₀, hj₀, hfirstSegmentNonempty, hfirstSegment_min,
      hbeforeFirstSegment_disjoint⟩ :=
    ArcCrossingFirstSegmentIndex δ α hXnonemptyδ
  obtain ⟨c, hcseg, hc_ne_left, hc_ne_right, hc_notα, hprefix_subset⟩ :=
    ArcCrossingFirstSegmentPrefixPoint δ α j₀ hj₀ hXfiniteδ
      hfirstSegmentNonempty
      (hδverticesAvoid δ.vertices[j₀]
        (List.getElem_mem (l := δ.vertices) (n := j₀)
          (Nat.lt_of_succ_lt hj₀)))
      (hδverticesAvoid δ.vertices[j₀ + 1]
        (List.getElem_mem (l := δ.vertices) (n := j₀ + 1) hj₀))
  have hcOpenδ : c ∈ openSegment ℝ δ.vertices[j₀] δ.vertices[j₀ + 1] := by
    exact mem_openSegment_of_ne_left_right (𝕜 := ℝ)
      hc_ne_left.symm hc_ne_right.symm hcseg
  have hprefix_disjoint :
      Disjoint (segment ℝ δ.vertices[j₀] c) α.carrier := by
    rw [Set.disjoint_left]
    intro z hzprefix hzα
    exact (hprefix_subset hzprefix).2 hzα
  obtain ⟨τ, hτvertices, hτsource, hτtarget, hτcarrier_subset,
      hcrossings_tail, hτKdisjoint⟩ :=
    ArcCrossingOrderedTailArc K δ α j₀ c hj₀ hcOpenδ hc_notα
      hbeforeFirstSegment_disjoint hprefix_disjoint hδverticesAvoid hδK
  obtain ⟨r₀, r₁, d, η, hτEndpointIsolation, hdOpen, hdist_cd_lt,
      hnear_germ_ball, hnear_germ_negative, hfarPrefixCompact,
      hfarPrefixDisjointTail, hηpos, hηsep⟩ :=
    ArcCrossingTailSourcePrefixData K δ τ j₀ c hK hj₀ hcOpenδ hτvertices
      hτKdisjoint
  obtain ⟨ρT, rT, K₁, hρTpos, hrTpos, hrTlt, hK₁pos, hDstar_subset,
      hDstar_open, hDstar_connected, hτEndpointIsolationT,
      hterminalLeftCone_Dstar, hterminalRightCone_Dstar⟩ :=
    ArcCrossingTerminalSlitDiskData K δ τ j₀ c d r₀ r₁ η hj₀ hcOpenδ
      hτvertices hτtarget hτEndpointIsolation hηpos hηsep
  let hprevτ : τ.vertices.length - 2 < τ.vertices.length := by
    have hlen := τ.length_ge_two
    omega
  let base : EuclideanSpace ℝ (Fin 2) :=
    τ.vertices[τ.vertices.length - 2]'hprevτ - τ.target
  let ray : Set (EuclideanSpace ℝ (Fin 2)) :=
    {q | ∃ t : ℝ, 0 < t ∧ q = τ.target + t • base}
  let Dstar : Set (EuclideanSpace ℝ (Fin 2)) :=
    Metric.ball τ.target ρT \
      (ray ∪ ({τ.target} : Set (EuclideanSpace ℝ (Fin 2))))
  have hDstar_subset' : Dstar ⊆ (K ∪ δ.carrier)ᶜ := by
    simpa [Dstar, ray, base, hprevτ] using hDstar_subset
  have hDstar_open' : IsOpen Dstar := by
    simpa [Dstar, ray, base, hprevτ] using hDstar_open
  have hDstar_connected' : IsConnected Dstar := by
    simpa [Dstar, ray, base, hprevτ] using hDstar_connected
  have hterminalLeftCone_Dstar' :
      PolygonalArcTerminalEndpointLeftCone τ rT K₁ ⊆ Dstar := by
    simpa [Dstar, ray, base, hprevτ] using hterminalLeftCone_Dstar
  have hterminalRightCone_Dstar' :
      PolygonalArcInitialEndpointLeftCone (PolygonalArcReverse τ) rT K₁ ⊆
        Dstar := by
    simpa [Dstar, ray, base, hprevτ] using hterminalRightCone_Dstar
  have hcarrier_cover :
      δ.carrier ⊆
        (ArcCrossingEarlierPrefix δ j₀ hj₀ ∪ segment ℝ δ.vertices[j₀] d) ∪
          segment ℝ d c ∪ τ.carrier := by
    intro p hpδ
    let u : EuclideanSpace ℝ (Fin 2) := δ.vertices[j₀]
    let v : EuclideanSpace ℝ (Fin 2) := δ.vertices[j₀ + 1]
    have hcOpen_uv : c ∈ openSegment ℝ u v := by
      simpa [u, v] using hcOpenδ
    have hdOpen_uc : d ∈ openSegment ℝ u c := by
      simpa [u] using hdOpen
    have hτ_first_segment : segment ℝ c v ⊆ τ.carrier := by
      intro z hz
      rw [τ.carrier_eq]
      have hfirst : 0 + 1 < τ.vertices.length := by
        have hlen := τ.length_ge_two
        omega
      refine ⟨0, hfirst, ?_⟩
      have hτ0 : τ.vertices[0] = c := by
        simpa [hτvertices]
      have hτ1 : τ.vertices[1] = v := by
        have hgetτ : τ.vertices[1]? = some τ.vertices[1] :=
          List.getElem?_eq_getElem (by simpa using hfirst)
        have hget : τ.vertices[1]? = some v := by
          rw [hτvertices]
          dsimp [v]
          simp [List.getElem?_cons_succ, List.getElem?_drop]
        exact Option.some.inj (hgetτ.symm.trans hget)
      simpa [hτ0, hτ1] using hz
    rw [δ.carrier_eq] at hpδ
    rcases hpδ with ⟨m, hm, hpsegδ⟩
    rcases lt_trichotomy m j₀ with hm_lt | hm_eq | hj_lt_m
    · left
      left
      left
      dsimp [ArcCrossingEarlierPrefix]
      refine Set.mem_iUnion.2 ⟨⟨m, hm_lt⟩, ?_⟩
      simpa using hpsegδ
    · subst m
      have hp_in_uv : p ∈ segment ℝ u v := by
        simpa [u, v] using hpsegδ
      by_cases hp_u : p = u
      · left
        left
        right
        simpa [u, hp_u] using left_mem_segment ℝ u d
      by_cases hp_v : p = v
      · right
        exact hτ_first_segment (by simpa [hp_v] using right_mem_segment ℝ c v)
      have hpOpen_uv : p ∈ openSegment ℝ u v :=
        mem_openSegment_of_ne_left_right (𝕜 := ℝ)
          (by intro h; exact hp_u h.symm) (by intro h; exact hp_v h.symm)
          hp_in_uv
      have hcRange :
          c ∈ Set.range
            (AffineMap.lineMap u v : ℝ →ᵃ[ℝ] EuclideanSpace ℝ (Fin 2)) := by
        have hcseg : c ∈ segment ℝ u v :=
          openSegment_subset_segment ℝ u v hcOpen_uv
        rw [segment_eq_image_lineMap] at hcseg
        rcases hcseg with ⟨t, _ht, ht⟩
        exact ⟨t, ht⟩
      have hp_split :=
        openSegment_subset_union (𝕜 := ℝ) u v hcRange hpOpen_uv
      rcases hp_split with hp_eq_c | hp_left_or_right
      · left
        right
        simpa [hp_eq_c] using right_mem_segment ℝ d c
      · rcases hp_left_or_right with hp_left | hp_right
        · have hdRange :
            d ∈ Set.range
              (AffineMap.lineMap u c : ℝ →ᵃ[ℝ] EuclideanSpace ℝ (Fin 2)) := by
            have hdseg : d ∈ segment ℝ u c :=
              openSegment_subset_segment ℝ u c hdOpen_uc
            rw [segment_eq_image_lineMap] at hdseg
            rcases hdseg with ⟨t, _ht, ht⟩
            exact ⟨t, ht⟩
          have hp_split_left :=
            openSegment_subset_union (𝕜 := ℝ) u c hdRange hp_left
          rcases hp_split_left with hp_eq_d | hp_ud_or_dc
          · left
            left
            right
            simpa [hp_eq_d] using right_mem_segment ℝ u d
          · rcases hp_ud_or_dc with hp_ud | hp_dc
            · left
              left
              right
              exact openSegment_subset_segment ℝ u d hp_ud
            · left
              right
              exact openSegment_subset_segment ℝ d c hp_dc
        · right
          exact hτ_first_segment (openSegment_subset_segment ℝ c v hp_right)
    · right
      rw [τ.carrier_eq]
      let n : ℕ := m - j₀
      have hn_pos : 0 < n := by
        dsimp [n]
        omega
      have hm_eq_jn : m = j₀ + n := by
        dsimp [n]
        omega
      have hnτ : n + 1 < τ.vertices.length := by
        rw [hτvertices]
        simp [List.length_drop]
        omega
      refine ⟨n, hnτ, ?_⟩
      have hτn : τ.vertices[n] = δ.vertices[m] := by
        have hgetτ : τ.vertices[n]? = some τ.vertices[n] :=
          List.getElem?_eq_getElem (Nat.lt_of_succ_lt hnτ)
        have hget : τ.vertices[n]? = some δ.vertices[m] := by
          obtain ⟨q, hq⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn_pos)
          have hidx : j₀ + 1 + q = m := by
            omega
          have hdrop :
              (δ.vertices.drop (j₀ + 1))[q]? = some δ.vertices[m] := by
            have hidx_lt : j₀ + 1 + q < δ.vertices.length := by
              omega
            rw [List.getElem?_drop]
            simpa [hidx] using
              (List.getElem?_eq_getElem (l := δ.vertices) hidx_lt)
          have hcons :
              (c :: δ.vertices.drop (j₀ + 1))[q + 1]? =
                (δ.vertices.drop (j₀ + 1))[q]? := by
            simp
          simpa [hτvertices, hq, Nat.succ_eq_add_one] using hcons.trans hdrop
        exact Option.some.inj (hgetτ.symm.trans hget)
      have hτn1 : τ.vertices[n + 1] = δ.vertices[m + 1] := by
        have hgetτ : τ.vertices[n + 1]? = some τ.vertices[n + 1] :=
          List.getElem?_eq_getElem hnτ
        have hget : τ.vertices[n + 1]? = some δ.vertices[m + 1] := by
          have hidx : j₀ + 1 + n = m + 1 := by
            dsimp [n] at hm_eq_jn
            omega
          have hdrop :
              (δ.vertices.drop (j₀ + 1))[n]? = some δ.vertices[m + 1] := by
            have hidx_lt : j₀ + 1 + n < δ.vertices.length := by
              omega
            rw [List.getElem?_drop]
            simpa [hidx] using
              (List.getElem?_eq_getElem (l := δ.vertices) hidx_lt)
          have hcons :
              (c :: δ.vertices.drop (j₀ + 1))[n + 1]? =
                (δ.vertices.drop (j₀ + 1))[n]? := by
            simp
          simpa [hτvertices] using hcons.trans hdrop
        exact Option.some.inj (hgetτ.symm.trans hget)
      simpa [hτn, hτn1] using hpsegδ
  obtain ⟨S, W, hW_eq, hW_subset_delta, hW_open, hW_connected, hW_path,
      hDstar_left, hDstar_right, hleft_subset_W, hright_subset_W,
      hτ_relativeInterior_subset_collar, hS_collar_open,
      hS_collar_without_tail⟩ :=
    ArcCrossingCollarBridgeData K Dstar δ τ j₀ c d r₀ rT K₁ η hj₀
      hcOpenδ hτvertices hτsource hτEndpointIsolationT hK₁pos
      hnear_germ_ball hnear_germ_negative hηpos hηsep hcarrier_cover
      hDstar_subset' hDstar_open' hDstar_connected' hterminalLeftCone_Dstar'
      hterminalRightCone_Dstar'
  have hW_subset : W ⊆ (K ∪ γ.carrier)ᶜ := by
    simpa [hδcarrier] using hW_subset_delta
  have hXfiniteγ : Set.Finite (α.carrier ∩ γ.carrier) := by
    simpa [hδcarrier] using hXfiniteδ
  have hαverticesAvoidγ :
      ∀ v : EuclideanSpace ℝ (Fin 2), v ∈ α.vertices → v ∉ γ.carrier := by
    intro v hv hvγ
    exact (hgp.1 v hv) (by simpa [hΓcarrier] using hvγ)
  have hoccurrence_in_collar :
      ∀ (i : ℕ) (hi : i + 1 < α.vertices.length)
          (x : EuclideanSpace ℝ (Fin 2)),
        x ∈ openSegment ℝ α.vertices[i] α.vertices[i + 1] →
          x ∈ γ.carrier → x ∈ S.collar := by
    intro i hi x hxOpen hxγ
    have hxSeg : x ∈ segment ℝ α.vertices[i] α.vertices[i + 1] :=
      openSegment_subset_segment ℝ α.vertices[i] α.vertices[i + 1] hxOpen
    have hxα : x ∈ α.carrier := by
      rw [α.carrier_eq]
      right
      exact ⟨i, hi, hxSeg⟩
    have hxδ : x ∈ δ.carrier := by
      simpa [hδcarrier] using hxγ
    exact hτ_relativeInterior_subset_collar (hcrossings_tail ⟨hxα, hxδ⟩)
  obtain ⟨cutBefore, cutAfter, hlocalCuts, hlocalDisjoint, hcover⟩ :=
    PolygonalPathFiniteOccurrenceLocalCuts α γ.carrier S.collar hXfiniteγ
      hS_collar_open hoccurrence_in_collar hαverticesAvoidγ
  have hcollar_not_gamma_subset_W :
      ∀ ⦃z : EuclideanSpace ℝ (Fin 2)⦄,
        z ∈ S.collar → z ∉ γ.carrier → z ∈ W := by
    intro z hzCollar hzNotγ
    have hzNotRel : z ∉ τ.relativeInterior := by
      intro hzRel
      have hzτcarrier : z ∈ τ.carrier := by
        have hzRel' :
            z ∈ τ.carrier \ ({τ.source, τ.target} :
              Set (EuclideanSpace ℝ (Fin 2))) := by
          simpa [τ.relativeInterior_eq] using hzRel
        exact hzRel'.1
      have hzδ : z ∈ δ.carrier := hτcarrier_subset hzτcarrier
      exact hzNotγ (by simpa [hδcarrier] using hzδ)
    have hzSide : z ∈ S.leftStrip ∪ S.rightStrip := by
      have hzDiff : z ∈ S.collar \ τ.relativeInterior := ⟨hzCollar, hzNotRel⟩
      simpa [hS_collar_without_tail] using hzDiff
    rcases hzSide with hzLeft | hzRight
    · exact hleft_subset_W hzLeft
    · exact hright_subset_W hzRight
  have hcut :
      ∀ (i : ℕ) (hi : i + 1 < α.vertices.length)
          (x : EuclideanSpace ℝ (Fin 2)),
        x ∈ openSegment ℝ α.vertices[i] α.vertices[i + 1] →
          x ∈ γ.carrier →
            cutBefore i hi x ∈ openSegment ℝ α.vertices[i] x ∧
              cutAfter i hi x ∈ openSegment ℝ x α.vertices[i + 1] ∧
                cutBefore i hi x ∈ W ∧
                  cutAfter i hi x ∈ W ∧
                    segment ℝ (cutBefore i hi x) (cutAfter i hi x) ∩
                        γ.carrier =
                      {x} := by
    intro i hi x hxOpen hxγ
    rcases hlocalCuts i hi x hxOpen hxγ with
      ⟨hbefore, hafter, hbeforeUF, hafterUF, hseg⟩
    exact ⟨hbefore, hafter,
      hcollar_not_gamma_subset_W hbeforeUF.1 hbeforeUF.2,
      hcollar_not_gamma_subset_W hafterUF.1 hafterUF.2, hseg⟩
  refine ⟨W, cutBefore, cutAfter, hW_subset, hW_path, hcut, ?_, hcover⟩
  intro i hi x y hxOpen hyOpen hxγ hyγ hxy
  exact hlocalDisjoint i hi x y hxOpen hyOpen hxγ hyγ hxy
