import ErdosProblems.Erdos733.ST.ArcCrossingSegmentOccurrenceParameters
import ErdosProblems.Erdos733.ST.ArcCrossingSegmentParameterGapPiece
import ErdosProblems.Erdos733.ST.ArcCrossingSegmentBoundaryGapPiece
import ErdosProblems.Erdos733.ST.ArcCrossingCutWindowParameters
import ErdosProblems.Erdos733.ST.ArcCrossingSegmentOrderedWindowParameters
import ErdosProblems.Erdos733.ST.ArcCrossingSegmentOrderedPieceList
import ErdosProblems.Erdos733.ST.ArcCrossingSegmentChainAssembly
import ErdosProblems.Erdos733.ST.PolygonalArc
import ErdosProblems.Erdos733.ST.PolygonalPathOriginalSegmentGap
import ErdosProblems.Erdos733.ST.PolygonalPathFiniteChainConcat
import ErdosProblems.Erdos733.ST.PolygonalPath
import ErdosProblems.Erdos733.ST.PolygonallyPathConnected

open Classical
noncomputable section

-- [TABLET NODE: ArcCrossingLocalSideApproaches]
lemma ArcCrossingLocalSideApproaches
    (K : Set (EuclideanSpace ℝ (Fin 2))) (γ : PolygonalArc) (α : PolygonalPath)
    (W : Set (EuclideanSpace ℝ (Fin 2)))
    (cutBefore cutAfter :
      ∀ (i : ℕ), i + 1 < α.vertices.length →
        EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)) :
    Set.Finite (α.carrier ∩ γ.carrier) →
      α.carrier ⊆ Kᶜ →
        α.source ∈ (K ∪ γ.carrier)ᶜ →
          α.target ∈ (K ∪ γ.carrier)ᶜ →
            W ⊆ (K ∪ γ.carrier)ᶜ →
              PolygonallyPathConnected W →
                (∀ v : EuclideanSpace ℝ (Fin 2), v ∈ α.vertices → v ∉ γ.carrier) →
                (∀ (i : ℕ) (hi : i + 1 < α.vertices.length)
                    (x : EuclideanSpace ℝ (Fin 2)),
                    x ∈ openSegment ℝ α.vertices[i] α.vertices[i + 1] →
                      x ∈ γ.carrier →
                        cutBefore i hi x ∈ openSegment ℝ α.vertices[i] x ∧
                          cutAfter i hi x ∈ openSegment ℝ x α.vertices[i + 1] ∧
                            cutBefore i hi x ∈ W ∧
                              cutAfter i hi x ∈ W ∧
                                segment ℝ (cutBefore i hi x) (cutAfter i hi x) ∩
                                    γ.carrier =
                                  {x}) →
                  (∀ (i : ℕ) (hi : i + 1 < α.vertices.length)
                      (x y : EuclideanSpace ℝ (Fin 2)),
                      x ∈ openSegment ℝ α.vertices[i] α.vertices[i + 1] →
                        y ∈ openSegment ℝ α.vertices[i] α.vertices[i + 1] →
                          x ∈ γ.carrier →
                            y ∈ γ.carrier →
                              x ≠ y →
                                Disjoint
                                  (segment ℝ (cutBefore i hi x) (cutAfter i hi x))
                                  (segment ℝ (cutBefore i hi y) (cutAfter i hi y))) →
                    (∀ (i : ℕ) (hi : i + 1 < α.vertices.length)
                        (y : EuclideanSpace ℝ (Fin 2)),
                        y ∈ segment ℝ α.vertices[i] α.vertices[i + 1] →
                          y ∈ γ.carrier →
                            ∃ x : EuclideanSpace ℝ (Fin 2),
                              x ∈ openSegment ℝ α.vertices[i] α.vertices[i + 1] ∧
                                x ∈ γ.carrier ∧
                                  y ∈ segment ℝ (cutBefore i hi x) (cutAfter i hi x)) →
                      ∃ α' : PolygonalPath,
                        α'.source = α.source ∧
                          α'.target = α.target ∧
                            α'.carrier ⊆ (K ∪ γ.carrier)ᶜ := by
-- BODY
  intro hfinite hαK hαsource hαtarget hWsub hWpath hαverticesAvoidγ hcut hordered hcover
  let Safe : Set (EuclideanSpace ℝ (Fin 2)) := (K ∪ γ.carrier)ᶜ
  by_cases hXempty :
      α.carrier ∩ γ.carrier = (∅ : Set (EuclideanSpace ℝ (Fin 2)))
  · refine ⟨α, rfl, rfl, ?_⟩
    intro z hzα hzSafe
    rcases hzSafe with hzK | hzγ
    · exact hαK hzα hzK
    · have hzX : z ∈ α.carrier ∩ γ.carrier := ⟨hzα, hzγ⟩
      rw [hXempty] at hzX
      exact hzX
  · suffices hpieces :
        ∃ (pieces : List PolygonalPath) (first last : PolygonalPath),
          pieces.head? = some first ∧
            pieces.getLast? = some last ∧
              first.source = α.source ∧
                last.target = α.target ∧
                  (∀ η : PolygonalPath, η ∈ pieces → η.carrier ⊆ Safe) ∧
                    (∀ (i : ℕ) (hi : i + 1 < pieces.length),
                      (pieces[i]).target = (pieces[i + 1]).source) by
      rcases hpieces with
        ⟨pieces, first, last, hhead, hlast, hfirst, hlast_target,
          hpieces_safe, hpieces_chain⟩
      rcases
          PolygonalPathFiniteChainConcat Safe pieces first last hhead hlast
            hpieces_safe hpieces_chain with
        ⟨α', hα'source, hα'target, hα'safe⟩
      refine ⟨α', ?_, ?_, ?_⟩
      · rw [hα'source, hfirst]
      · rw [hα'target, hlast_target]
      · simpa [Safe] using hα'safe
    -- The remaining finite-surgery work is to construct this ordered list of
    -- safe gap pieces and W-detour pieces from the occurrence windows.
    have originalGapPiece :
        ∀ (i : ℕ) (hi : i + 1 < α.vertices.length)
            (p q : EuclideanSpace ℝ (Fin 2)),
          segment ℝ p q ⊆ segment ℝ α.vertices[i] α.vertices[i + 1] →
            Disjoint (segment ℝ p q) γ.carrier →
              ∃ η : PolygonalPath,
                η.source = p ∧ η.target = q ∧ η.carrier ⊆ Safe := by
      intro i hi p q hpq_subset hpq_disjoint
      simpa [Safe] using
        PolygonalPathOriginalSegmentGap K γ.carrier α i hi p q hαK
          hpq_subset hpq_disjoint
    have detourPiece :
        ∀ (i : ℕ) (hi : i + 1 < α.vertices.length)
            (x : EuclideanSpace ℝ (Fin 2)),
          x ∈ openSegment ℝ α.vertices[i] α.vertices[i + 1] →
            x ∈ γ.carrier →
              ∃ η : PolygonalPath,
                η.source = cutBefore i hi x ∧
                  η.target = cutAfter i hi x ∧
                    η.carrier ⊆ Safe := by
      intro i hi x hxOpen hxγ
      rcases hcut i hi x hxOpen hxγ with
        ⟨_hbefore, _hafter, hbeforeW, hafterW, _hsegment⟩
      rcases hWpath hbeforeW hafterW with
        ⟨η, hηsource, hηtarget, hηcarrier⟩
      refine ⟨η, hηsource, hηtarget, ?_⟩
      intro z hz
      exact hWsub (hηcarrier hz)
    have segmentOccurrenceParameters :
        ∀ (i : ℕ) (hi : i + 1 < α.vertices.length),
          ∃ params : List ℝ,
            params.Nodup ∧
              params.SortedLT ∧
                (∀ t : ℝ, t ∈ params ↔
                  AffineMap.lineMap α.vertices[i] α.vertices[i + 1] t ∈
                    openSegment ℝ α.vertices[i] α.vertices[i + 1] ∩ γ.carrier) ∧
                  (∀ t : ℝ, t ∈ params → 0 < t ∧ t < 1) ∧
                    (∀ x : EuclideanSpace ℝ (Fin 2),
                      x ∈ openSegment ℝ α.vertices[i] α.vertices[i + 1] →
                        x ∈ γ.carrier →
                          ∃ t : ℝ,
                            t ∈ params ∧ 0 < t ∧ t < 1 ∧
                              AffineMap.lineMap α.vertices[i] α.vertices[i + 1] t = x) ∧
                      (∀ n (hn : n + 1 < params.length), params[n] < params[n + 1]) ∧
                        (∀ n (hn : n + 1 < params.length) t,
                          0 < t → t < 1 →
                            AffineMap.lineMap α.vertices[i] α.vertices[i + 1] t ∈
                              γ.carrier →
                              ¬ (params[n] < t ∧ t < params[n + 1])) := by
      intro i hi
      exact ArcCrossingSegmentOccurrenceParameters γ α i hi hfinite hαverticesAvoidγ
    have parameterGapPiece :
        ∀ (i : ℕ) (hi : i + 1 < α.vertices.length)
            (left right s t : ℝ),
          left < s →
            s ≤ t →
              t < right →
                0 < left →
                  right < 1 →
                    (∀ u : ℝ, 0 < u → u < 1 →
                      (AffineMap.lineMap α.vertices[i] α.vertices[i + 1]) u ∈ γ.carrier →
                        ¬ (left < u ∧ u < right)) →
                      ∃ η : PolygonalPath,
                        η.source =
                            (AffineMap.lineMap α.vertices[i] α.vertices[i + 1]) s ∧
                          η.target =
                            (AffineMap.lineMap α.vertices[i] α.vertices[i + 1]) t ∧
                            η.carrier ⊆ Safe := by
      intro i hi left right s t hleft_s hst ht_right hleft_pos hright_lt_one hno
      simpa [Safe] using
        ArcCrossingSegmentParameterGapPiece K γ α i hi left right s t hαK
          hleft_s hst ht_right hleft_pos hright_lt_one hno
    have boundaryGapPiece :
        ∀ (i : ℕ) (hi : i + 1 < α.vertices.length) (s t : ℝ),
          0 ≤ s →
            s ≤ t →
              t ≤ 1 →
                (∀ u : ℝ, 0 < u → u < 1 →
                  (AffineMap.lineMap α.vertices[i] α.vertices[i + 1]) u ∈ γ.carrier →
                    ¬ (s ≤ u ∧ u ≤ t)) →
                  ∃ η : PolygonalPath,
                    η.source =
                        (AffineMap.lineMap α.vertices[i] α.vertices[i + 1]) s ∧
                      η.target =
                        (AffineMap.lineMap α.vertices[i] α.vertices[i + 1]) t ∧
                        η.carrier ⊆ Safe := by
      intro i hi s t hs0 hst ht1 hno
      have hA_notγ :
          α.vertices[i] ∉ γ.carrier :=
        hαverticesAvoidγ α.vertices[i]
          (List.getElem_mem (l := α.vertices) (n := i) (Nat.lt_of_succ_lt hi))
      have hB_notγ :
          α.vertices[i + 1] ∉ γ.carrier :=
        hαverticesAvoidγ α.vertices[i + 1]
          (List.getElem_mem (l := α.vertices) (n := i + 1) hi)
      simpa [Safe] using
        ArcCrossingSegmentBoundaryGapPiece K γ α i hi s t hαK hs0 hst ht1
          hA_notγ hB_notγ hno
    have occurrenceFreeClosedGapPiece :
        ∀ (i : ℕ) (hi : i + 1 < α.vertices.length) (params : List ℝ)
            (s t : ℝ),
          (∀ u : ℝ, u ∈ params ↔
            AffineMap.lineMap α.vertices[i] α.vertices[i + 1] u ∈
              openSegment ℝ α.vertices[i] α.vertices[i + 1] ∩ γ.carrier) →
            0 ≤ s →
              s ≤ t →
                t ≤ 1 →
                  (∀ u : ℝ, u ∈ params → ¬ (s ≤ u ∧ u ≤ t)) →
                    ∃ η : PolygonalPath,
                      η.source =
                          (AffineMap.lineMap α.vertices[i] α.vertices[i + 1]) s ∧
                        η.target =
                          (AffineMap.lineMap α.vertices[i] α.vertices[i + 1]) t ∧
                          η.carrier ⊆ Safe := by
      intro i hi params s t hmem hs0 hst ht1 hnoParams
      exact
        boundaryGapPiece i hi s t hs0 hst ht1
          (by
            intro u hu0 hu1 huγ hu_bounds
            have huOpen :
                AffineMap.lineMap α.vertices[i] α.vertices[i + 1] u ∈
                  openSegment ℝ α.vertices[i] α.vertices[i + 1] :=
              lineMap_mem_openSegment (𝕜 := ℝ)
                α.vertices[i] α.vertices[i + 1] ⟨hu0, hu1⟩
            have hu_mem : u ∈ params := (hmem u).mpr ⟨huOpen, huγ⟩
            exact hnoParams u hu_mem hu_bounds)
    have noParamBeforeFirst :
        ∀ (params : List ℝ), params.SortedLT →
          ∀ (hpos : 0 < params.length) (left : ℝ),
            left < params[0]'hpos →
              ∀ u : ℝ, u ∈ params → ¬ (0 ≤ u ∧ u ≤ left) := by
      intro params hsorted hpos left hleft u hu hubounds
      rcases List.mem_iff_get.mp hu with ⟨k, hk⟩
      subst u
      have hle : params[0]'hpos ≤ params.get k := by
        have hzero_le : (⟨0, hpos⟩ : Fin params.length) ≤ k := by
          exact Nat.zero_le k.1
        exact hsorted.monotone hzero_le
      have hfirst_le_left : params[0]'hpos ≤ left := le_trans hle hubounds.2
      exact (not_lt_of_ge hfirst_le_left) hleft
    have noParamAfterLast :
        ∀ (params : List ℝ), params.SortedLT →
          ∀ (hpos : 0 < params.length) (right : ℝ),
            params[params.length - 1]'(Nat.sub_lt hpos (by decide)) < right →
              ∀ u : ℝ, u ∈ params → ¬ (right ≤ u ∧ u ≤ 1) := by
      intro params hsorted hpos right hright u hu hubounds
      rcases List.mem_iff_get.mp hu with ⟨k, hk⟩
      subst u
      let last : Fin params.length := ⟨params.length - 1, Nat.sub_lt hpos (by decide)⟩
      have hk_le_last : k ≤ last := by
        change (k : ℕ) ≤ params.length - 1
        exact Nat.le_pred_of_lt k.isLt
      have hle : params.get k ≤ params.get last := hsorted.monotone hk_le_last
      have hright_le_last : right ≤ params.get last := le_trans hubounds.1 hle
      exact (not_lt_of_ge hright_le_last) hright
    have noParamEmpty :
        ∀ (params : List ℝ), params = [] →
          ∀ u : ℝ, u ∈ params → False := by
      intro params hparams u hu
      simp [hparams] at hu
    have cutWindowParameters :
        ∀ (i : ℕ) (hi : i + 1 < α.vertices.length)
            (x : EuclideanSpace ℝ (Fin 2)) (p : ℝ),
          0 < p →
            p < 1 →
              AffineMap.lineMap α.vertices[i] α.vertices[i + 1] p = x →
                x ∈ openSegment ℝ α.vertices[i] α.vertices[i + 1] →
                  x ∈ γ.carrier →
                    ∃ b a : ℝ,
                      0 < b ∧ b < p ∧ p < a ∧ a < 1 ∧
                        AffineMap.lineMap α.vertices[i] α.vertices[i + 1] b =
                          cutBefore i hi x ∧
                          AffineMap.lineMap α.vertices[i] α.vertices[i + 1] a =
                            cutAfter i hi x := by
      intro i hi x p hp0 hp1 hp_eq hxOpen hxγ
      rcases hcut i hi x hxOpen hxγ with
        ⟨hbefore, hafter, _hbeforeW, _hafterW, _hsegment⟩
      exact
        ArcCrossingCutWindowParameters α i hi x (cutBefore i hi x) (cutAfter i hi x) p
          hp0 hp1 hp_eq hbefore hafter
    have orderedWindowParameters :
        ∀ (i : ℕ) (hi : i + 1 < α.vertices.length) (params : List ℝ),
          (∀ t : ℝ, t ∈ params ↔
            AffineMap.lineMap α.vertices[i] α.vertices[i + 1] t ∈
              openSegment ℝ α.vertices[i] α.vertices[i + 1] ∩ γ.carrier) →
            (∀ t : ℝ, t ∈ params → 0 < t ∧ t < 1) →
              (∀ n (hn : n + 1 < params.length), params[n] < params[n + 1]) →
                ∃ left right : (n : ℕ) → n < params.length → ℝ,
                  (∀ n (hn : n < params.length),
                    0 < left n hn ∧ left n hn < params[n] ∧
                      params[n] < right n hn ∧ right n hn < 1 ∧
                        AffineMap.lineMap α.vertices[i] α.vertices[i + 1]
                            (left n hn) =
                          cutBefore i hi
                            (AffineMap.lineMap α.vertices[i] α.vertices[i + 1]
                              params[n]) ∧
                          AffineMap.lineMap α.vertices[i] α.vertices[i + 1]
                              (right n hn) =
                            cutAfter i hi
                              (AffineMap.lineMap α.vertices[i] α.vertices[i + 1]
                                params[n])) ∧
                    (∀ n (hn : n + 1 < params.length),
                      right n (Nat.lt_of_succ_lt hn) < left (n + 1) hn) := by
      intro i hi params hmem hbounds hparam_order
      refine
        ArcCrossingSegmentOrderedWindowParameters α i hi
          (fun x => cutBefore i hi x) (fun x => cutAfter i hi x) params ?_ hparam_order ?_
      · intro n hn
        have hn_mem : params[n] ∈ params := List.getElem_mem hn
        have hp_bounds := hbounds params[n] hn_mem
        have hx_occ := (hmem params[n]).mp hn_mem
        exact
          cutWindowParameters i hi
            (AffineMap.lineMap α.vertices[i] α.vertices[i + 1] params[n])
            params[n] hp_bounds.1 hp_bounds.2 rfl hx_occ.1 hx_occ.2
      · intro n hn
        have hn0 : n < params.length := Nat.lt_of_succ_lt hn
        have hn1 : n + 1 < params.length := hn
        have hx_occ := (hmem params[n]).mp (List.getElem_mem hn0)
        have hy_occ := (hmem params[n + 1]).mp (List.getElem_mem hn1)
        have hxy :
            AffineMap.lineMap α.vertices[i] α.vertices[i + 1] params[n] ≠
              AffineMap.lineMap α.vertices[i] α.vertices[i + 1] params[n + 1] := by
          have hA_notγ :
              α.vertices[i] ∉ γ.carrier :=
            hαverticesAvoidγ α.vertices[i]
              (List.getElem_mem (l := α.vertices) (n := i) (Nat.lt_of_succ_lt hi))
          have hAB : α.vertices[i] ≠ α.vertices[i + 1] := by
            intro hABeq
            have hx_eq : AffineMap.lineMap α.vertices[i] α.vertices[i + 1] params[n] =
                α.vertices[i] := by
              simpa [hABeq] using hx_occ.1
            exact hA_notγ (by simpa [hx_eq] using hx_occ.2)
          intro hsame
          have hparam_same :
              params[n] = params[n + 1] :=
            (AffineMap.lineMap_injective ℝ hAB) hsame
          exact (ne_of_lt (hparam_order n hn)) hparam_same
        exact
          hordered i hi
            (AffineMap.lineMap α.vertices[i] α.vertices[i + 1] params[n])
            (AffineMap.lineMap α.vertices[i] α.vertices[i + 1] params[n + 1])
            hx_occ.1 hy_occ.1 hx_occ.2 hy_occ.2 hxy
    have segmentPieceList :
        ∀ (i : ℕ) (hi : i + 1 < α.vertices.length),
          ∃ (pieces : List PolygonalPath) (first last : PolygonalPath),
            pieces.head? = some first ∧
              pieces.getLast? = some last ∧
                first.source = α.vertices[i] ∧
                  last.target = α.vertices[i + 1] ∧
                    (∀ η : PolygonalPath, η ∈ pieces → η.carrier ⊆ Safe) ∧
                      (∀ (j : ℕ) (hj : j + 1 < pieces.length),
                        (pieces[j]).target = (pieces[j + 1]).source) := by
      intro i hi
      rcases segmentOccurrenceParameters i hi with
        ⟨params, _hnodup, hsorted, hmem, hbounds, _hexists,
          hparam_order, hno_between⟩
      rcases orderedWindowParameters i hi params hmem hbounds hparam_order with
        ⟨left, right, hwindow, hwindow_order⟩
      refine
        ArcCrossingSegmentOrderedPieceList γ α Safe i hi params left right
          ?_ hwindow_order hno_between ?_ ?_ ?_ ?_ ?_ ?_
      · intro n hn
        have h := hwindow n hn
        exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
      · intro hpos u hu
        exact
          noParamBeforeFirst params hsorted hpos (left 0 hpos)
            (hwindow 0 hpos).2.1 u hu
      · intro hpos u hu
        let lastIdx : ℕ := params.length - 1
        have hlast : lastIdx < params.length := Nat.sub_lt hpos (by decide)
        exact
          noParamAfterLast params hsorted hpos (right lastIdx hlast)
            (hwindow lastIdx hlast).2.2.1 u hu
      · intro hparams
        exact noParamEmpty params hparams
      · intro s t hs0 hst ht1 hnoParams
        exact occurrenceFreeClosedGapPiece i hi params s t hmem hs0 hst ht1 hnoParams
      · intro leftBound rightBound s t hleft_s hst ht_right hleft_pos hright_lt_one hno
        exact
          parameterGapPiece i hi leftBound rightBound s t hleft_s hst ht_right
            hleft_pos hright_lt_one hno
      · intro n hn
        have hn_mem : params[n] ∈ params := List.getElem_mem hn
        have hx_occ := (hmem params[n]).mp hn_mem
        rcases
            detourPiece i hi
              (AffineMap.lineMap α.vertices[i] α.vertices[i + 1] params[n])
              hx_occ.1 hx_occ.2 with
          ⟨η, hηsource, hηtarget, hηsafe⟩
        have h := hwindow n hn
        refine ⟨η, ?_, ?_, hηsafe⟩
        · rw [h.2.2.2.2.1]
          exact hηsource
        · rw [h.2.2.2.2.2]
          exact hηtarget
    have hlen : 1 < α.vertices.length := by
      by_contra hnot
      have hle : α.vertices.length ≤ 1 := Nat.le_of_not_gt hnot
      have hcarrier_subset :
          α.carrier ⊆
            ({α.source, α.target} : Set (EuclideanSpace ℝ (Fin 2))) := by
        intro z hz
        rw [α.carrier_eq] at hz
        rcases hz with hz_end | hz_seg
        · exact hz_end
        · rcases hz_seg with ⟨i, hi, _hz⟩
          have hge : 2 ≤ α.vertices.length := by omega
          omega
      have hsource_notγ : α.source ∉ γ.carrier := by
        intro hγ
        exact hαsource (Or.inr hγ)
      have htarget_notγ : α.target ∉ γ.carrier := by
        intro hγ
        exact hαtarget (Or.inr hγ)
      have hempty :
          α.carrier ∩ γ.carrier =
            (∅ : Set (EuclideanSpace ℝ (Fin 2))) := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro z hz
        have hz_end := hcarrier_subset hz.1
        rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hz_end
        rcases hz_end with hz_source | hz_target
        · exact hsource_notγ (by simpa [hz_source] using hz.2)
        · exact htarget_notγ (by simpa [hz_target] using hz.2)
      exact hXempty hempty
    have segmentPath :
        ∀ (i : ℕ) (hi : i + 1 < α.vertices.length),
          ∃ η : PolygonalPath,
            η.source = α.vertices[i] ∧
              η.target = α.vertices[i + 1] ∧
                η.carrier ⊆ Safe := by
      intro i hi
      rcases segmentPieceList i hi with
        ⟨pieces, first, last, hhead, hlast, hfirst, hlast_target,
          hpieces_safe, hpieces_chain⟩
      rcases
          PolygonalPathFiniteChainConcat Safe pieces first last hhead hlast
            hpieces_safe hpieces_chain with
        ⟨η, hηsource, hηtarget, hηsafe⟩
      refine ⟨η, ?_, ?_, hηsafe⟩
      · rw [hηsource, hfirst]
      · rw [hηtarget, hlast_target]
    exact
      ArcCrossingSegmentChainAssembly α.vertices α.source α.target Safe
        α.source_eq_head α.target_eq_last hlen segmentPath
