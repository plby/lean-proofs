import ErdosProblems.Erdos733.ST.FinitePolygonalSetCyclicGlobalElementaryPieceSkeleton
import ErdosProblems.Erdos733.ST.FinitePolygonalSetCyclicActualNormalizedSourceCycle
import ErdosProblems.Erdos733.ST.FinitePolygonalSetCyclicActualStreamEndpointContinuityBridge
import ErdosProblems.Erdos733.ST.FinitePolygonalSetCyclicActualStreamIntervalBlocks
import ErdosProblems.Erdos733.ST.FinitePolygonalSetCyclicGlobalSourceSeparation
import ErdosProblems.Erdos733.ST.FiniteSortedRealCutListCoversUnitInterval
import ErdosProblems.Erdos733.ST.FinitePolygonalSetCyclicActualPieceCoverage
import Mathlib.Tactic

open Classical
noncomputable section

lemma FinitePolygonalSetCyclicActualEveryPieceInOrder
    (J : SimpleClosedPolygonalCurve) (K : FinitePolygonalSet)
    (hKJ : K.carrier = J.carrier) {PieceIndex : Type}
    (successor :
      Equiv.Perm {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points})
    (pieceSource : PieceIndex → EuclideanSpace ℝ (Fin 2))
    (pieceStream : List PieceIndex)
    (sourceOccurrenceList :
      List {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points})
    (sourceOption :
      PieceIndex →
        Option {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points})
    (hsourceOption :
      ∀ i,
        sourceOption i =
          if h : pieceSource i ∈ K.points then
            some (⟨pieceSource i, h⟩ :
              {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points})
          else none)
    (arcPieceOrder :
      {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points} → List PieceIndex)
    (hstream_nodup : pieceStream.Nodup)
    (hstream_mem : ∀ i : PieceIndex, i ∈ pieceStream)
    (hsource_covers :
      ∀ p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points},
        p ∈ sourceOccurrenceList)
    (hsource_filter :
      sourceOccurrenceList = pieceStream.filterMap sourceOption)
    (hsource_unique :
      ∀ {x y : PieceIndex}
        {p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points}},
        x ∈ pieceStream → y ∈ pieceStream →
          sourceOption x = some p → sourceOption y = some p → x = y)
    (arcPieceOrder_cases :
      ∀ p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points},
        (∃ (pre : List PieceIndex) (head : PieceIndex)
            (middle : List PieceIndex) (next : PieceIndex)
            (suffix : List PieceIndex),
          arcPieceOrder p = head :: middle ∧
            pieceStream =
              pre ++ arcPieceOrder p ++ (next :: suffix) ∧
            pieceSource head = p.1 ∧
            pieceSource next = (successor p).1 ∧
            ∀ i ∈ middle, pieceSource i ∉ K.points) ∨
        (∃ (pre : List PieceIndex) (next : PieceIndex)
            (middle : List PieceIndex) (head : PieceIndex)
            (suffix : List PieceIndex),
          arcPieceOrder p = head :: (suffix ++ pre) ∧
            pieceStream =
              pre ++ (next :: middle) ++ (head :: suffix) ∧
            pieceSource head = p.1 ∧
            pieceSource next = (successor p).1 ∧
            ∀ i ∈ suffix ++ pre, pieceSource i ∉ K.points)) :
    ∀ i : PieceIndex,
      ∃ p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points},
        i ∈ arcPieceOrder p := by
  classical
  have idx_at_cons :
      ∀ {a : PieceIndex} {pre post : List PieceIndex},
        pieceStream = pre ++ a :: post →
          pieceStream.idxOf a = pre.length := by
    intro a pre post hsplit
    have hpos : pre.length < pieceStream.length := by
      rw [hsplit]
      simp
    have hidx := List.Nodup.idxOf_getElem hstream_nodup pre.length hpos
    simpa [hsplit] using hidx
  have mem_prefix_of_idx_lt :
      ∀ {x : PieceIndex} {pref suffix : List PieceIndex},
        pieceStream = pref ++ suffix →
          pieceStream.idxOf x < pref.length → x ∈ pref := by
    intro x pref suffix hsplit hlt
    have hpref : pref <+: pieceStream := by
      rw [hsplit]
      exact ⟨suffix, rfl⟩
    exact (hpref.mem_iff_idxOf_lt_length x).2 hlt
  have mem_suffix_of_idx_ge :
      ∀ {x : PieceIndex} {pref suffix : List PieceIndex},
        pieceStream = pref ++ suffix →
          x ∈ pieceStream →
            pref.length ≤ pieceStream.idxOf x → x ∈ suffix := by
    intro x pref suffix hsplit hx hge
    have hx_pref_or_suffix : x ∈ pref ∨ x ∈ suffix := by
      simpa [hsplit] using hx
    rcases hx_pref_or_suffix with hxpref | hxsuf
    · have hpref : pref <+: pieceStream := by
        rw [hsplit]
        exact ⟨suffix, rfl⟩
      have hlt := (hpref.mem_iff_idxOf_lt_length x).1 hxpref
      omega
    · exact hxsuf
  have mem_block_of_idx_between :
      ∀ {x : PieceIndex} {pre block suffix : List PieceIndex},
        pieceStream = pre ++ block ++ suffix →
          x ∈ pieceStream →
            pre.length ≤ pieceStream.idxOf x →
              pieceStream.idxOf x < pre.length + block.length →
                x ∈ block := by
    intro x pre block suffix hsplit hx hge hlt
    have hprefix :
        x ∈ pre ++ block := by
      apply mem_prefix_of_idx_lt
        (x := x) (pref := pre ++ block) (suffix := suffix)
      · simpa [List.append_assoc] using hsplit
      · simpa [List.length_append] using hlt
    have hx_not_pre : x ∉ pre := by
      intro hxpre
      have hpref : pre <+: pieceStream := by
        rw [hsplit]
        exact ⟨block ++ suffix, by simp [List.append_assoc]⟩
      have hlt_pre := (hpref.mem_iff_idxOf_lt_length x).1 hxpre
      omega
    simpa [List.mem_append, hx_not_pre] using hprefix
  have hpiece_mem_arcPieceOrder :
      ∀ i : PieceIndex,
        ∃ p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points},
          i ∈ arcPieceOrder p := by
    intro i
    by_cases hi_source : pieceSource i ∈ K.points
    · let p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points} :=
        ⟨pieceSource i, hi_source⟩
      refine ⟨p, ?_⟩
      rcases arcPieceOrder_cases p with hcase | hcase
      · rcases hcase with
          ⟨pre, head, middle, next, suffix, horder, hstream,
            hhead_source, _hnext_source, _hmiddle⟩
        have hhead_mem_stream : head ∈ pieceStream := by
          rw [hstream]
          simp [horder]
        have hi_mem_stream : i ∈ pieceStream := hstream_mem i
        have hhead_ret :
            sourceOption head = some p := by
          have hhead_listed : pieceSource head ∈ K.points := by
            simp [hhead_source, hi_source]
          have hp_eq :
              (⟨pieceSource head, hhead_listed⟩ :
                {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points}) = p := by
            exact Subtype.ext hhead_source
          simp [hsourceOption, hhead_listed, hp_eq]
        have hi_ret :
            sourceOption i = some p := by
          simp [hsourceOption, p, hi_source]
        have hhead_eq_i :
            head = i :=
          hsource_unique hhead_mem_stream hi_mem_stream hhead_ret hi_ret
        subst i
        simp [horder]
      · rcases hcase with
          ⟨pre, next, middle, head, suffix, horder, hstream,
            hhead_source, _hnext_source, _hmiddle⟩
        have hhead_mem_stream : head ∈ pieceStream := by
          rw [hstream]
          simp
        have hi_mem_stream : i ∈ pieceStream := hstream_mem i
        have hhead_ret :
            sourceOption head = some p := by
          have hhead_listed : pieceSource head ∈ K.points := by
            simp [hhead_source, hi_source]
          have hp_eq :
              (⟨pieceSource head, hhead_listed⟩ :
                {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points}) = p := by
            exact Subtype.ext hhead_source
          simp [hsourceOption, hhead_listed, hp_eq]
        have hi_ret :
            sourceOption i = some p := by
          simp [hsourceOption, p, hi_source]
        have hhead_eq_i :
            head = i :=
          hsource_unique hhead_mem_stream hi_mem_stream hhead_ret hi_ret
        subst i
        simp [horder]
    ·
      have hi_none : sourceOption i = none := by
        simp [hsourceOption, hi_source]
      rcases List.getElem_of_mem (hstream_mem i) with ⟨n, hn, hget_i⟩
      let preI : List PieceIndex := pieceStream.take n
      let postI : List PieceIndex := pieceStream.drop (n + 1)
      have hsplit_i : pieceStream = preI ++ i :: postI := by
        calc
          pieceStream = pieceStream.take n ++ pieceStream.drop n := by
            rw [List.take_append_drop]
          _ = pieceStream.take n ++ pieceStream[n] :: pieceStream.drop (n + 1) := by
            rw [List.drop_eq_getElem_cons hn]
          _ = preI ++ i :: postI := by
            simp [preI, postI, hget_i]
      have hidx_i : pieceStream.idxOf i = preI.length :=
        idx_at_cons hsplit_i
      have hfilter_split :
          sourceOccurrenceList =
            preI.filterMap sourceOption ++ postI.filterMap sourceOption := by
        rw [hsource_filter, hsplit_i]
        simp [hi_none]
      cases hpost_ret : postI.filterMap sourceOption with
      | cons q qs =>
          rcases
            (List.filterMap_eq_cons_iff
              (f := sourceOption) (l := postI) (b := q) (bs := qs)).1
              hpost_ret with
            ⟨noneBefore, nextAfter, after, hpost_decomp, hnoneBefore_filter,
              hnextAfter_ret, _hafter_filter⟩
          have hnoneBefore :
              ∀ x ∈ noneBefore, sourceOption x = none :=
            hnoneBefore_filter
          have hsplit_next :
              pieceStream =
                (preI ++ [i]) ++ noneBefore ++ (nextAfter :: after) := by
            rw [hsplit_i, hpost_decomp]
            simp [List.append_assoc]
          have hidx_nextAfter :
              pieceStream.idxOf nextAfter =
                (preI ++ [i] ++ noneBefore).length := by
            apply idx_at_cons
            rw [hsplit_next]
          have hidx_i_lt_nextAfter :
              pieceStream.idxOf i < pieceStream.idxOf nextAfter := by
            rw [hidx_i, hidx_nextAfter]
            simp
          let p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points} :=
            successor.symm q
          have hsucc_p : successor p = q := by
            simp [p]
          refine ⟨p, ?_⟩
          rcases arcPieceOrder_cases p with hcase | hcase
          · rcases hcase with
              ⟨pre, head, middle, next, suffix, horder, hstream,
                hhead_source, hnext_source, _hmiddle⟩
            have hhead_mem_stream : head ∈ pieceStream := by
              rw [hstream]
              simp [horder]
            have hnext_mem_stream : next ∈ pieceStream := by
              rw [hstream]
              simp
            have hhead_ret :
                sourceOption head = some p := by
              have hhead_listed : pieceSource head ∈ K.points := by
                simpa [hhead_source] using p.2
              have hp_eq :
                  (⟨pieceSource head, hhead_listed⟩ :
                    {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points}) = p := by
                exact Subtype.ext hhead_source
              simp [hsourceOption, hhead_listed, hp_eq]
            have hnext_ret :
                sourceOption next = some q := by
              have hnext_listed : pieceSource next ∈ K.points := by
                have hqmem : (successor p).1 ∈ K.points := (successor p).2
                simpa [hnext_source] using hqmem
              have hq_eq :
                  (⟨pieceSource next, hnext_listed⟩ :
                    {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points}) = q := by
                apply Subtype.ext
                calc
                  pieceSource next = (successor p).1 := hnext_source
                  _ = q.1 := by rw [hsucc_p]
              simp [hsourceOption, hnext_listed, hq_eq]
            have hnext_eq :
                next = nextAfter :=
              hsource_unique hnext_mem_stream
                (by
                  rw [hsplit_next]
                  simp)
                hnext_ret hnextAfter_ret
            have hstream_head :
                pieceStream = pre ++ head :: (middle ++ next :: suffix) := by
              rw [hstream, horder]
              simp [List.append_assoc]
            have hidx_head : pieceStream.idxOf head = pre.length :=
              idx_at_cons hstream_head
            have hstream_next :
                pieceStream = (pre ++ head :: middle) ++ next :: suffix := by
              rw [hstream, horder]
            have hidx_next : pieceStream.idxOf next =
                (pre ++ head :: middle).length :=
              idx_at_cons hstream_next
            have hi_mem_arc :
                i ∈ pre ∨ i ∈ arcPieceOrder p ∨ i = next ∨ i ∈ suffix := by
              have hi_stream : i ∈ pre ++ arcPieceOrder p ++ next :: suffix := by
                simpa [hstream] using hstream_mem i
              simpa [List.mem_append, or_assoc] using hi_stream
            rcases hi_mem_arc with hi_pre | hi_rest
            · have hidx_i_lt_head : pieceStream.idxOf i < pieceStream.idxOf head := by
                rw [hidx_head]
                have hpref : pre <+: pieceStream := by
                  rw [hstream_head]
                  exact ⟨head :: (middle ++ next :: suffix), rfl⟩
                exact (hpref.mem_iff_idxOf_lt_length i).1 hi_pre
              have hhead_lt_next :
                  pieceStream.idxOf head < pieceStream.idxOf nextAfter := by
                rw [← hnext_eq, hidx_head, hidx_next]
                simp
              have hhead_in_none :
                  head ∈ noneBefore := by
                apply mem_block_of_idx_between
                  (x := head) (pre := preI ++ [i]) (block := noneBefore)
                  (suffix := nextAfter :: after)
                · exact hsplit_next
                · exact hhead_mem_stream
                · rw [hidx_i] at hidx_i_lt_head
                  simpa using hidx_i_lt_head
                · rw [hidx_nextAfter] at hhead_lt_next
                  simp [List.length_append] at hhead_lt_next ⊢
                  omega
              have hnone := hnoneBefore head hhead_in_none
              rw [hhead_ret] at hnone
              simp at hnone
            · rcases hi_rest with hi_block | hi_rest
              · exact hi_block
              · rcases hi_rest with hi_eq_next | hi_suffix
                · have hnone_next : sourceOption next = none := by
                    simpa [hi_eq_next] using hi_none
                  rw [hnext_ret] at hnone_next
                  simp at hnone_next
                · have hprefix_len_le_i :
                      (pre ++ arcPieceOrder p ++ [next]).length ≤
                        pieceStream.idxOf i := by
                    apply le_of_not_gt
                    intro hlt
                    have hi_pref :
                        i ∈ pre ++ arcPieceOrder p ++ [next] := by
                      apply mem_prefix_of_idx_lt
                        (x := i)
                        (pref := pre ++ arcPieceOrder p ++ [next])
                        (suffix := suffix)
                      · rw [hstream]
                        simp [List.append_assoc]
                      · exact hlt
                    have hnod :
                        (pre ++ arcPieceOrder p ++ [next] ++ suffix).Nodup := by
                      simpa [hstream, List.append_assoc] using hstream_nodup
                    have hdisj :=
                      List.disjoint_of_nodup_append
                        (l₁ := pre ++ arcPieceOrder p ++ [next])
                        (l₂ := suffix) hnod
                    exact hdisj hi_pref hi_suffix
                  have hnext_lt_i :
                      pieceStream.idxOf next < pieceStream.idxOf i := by
                    rw [horder] at hprefix_len_le_i
                    rw [hidx_next]
                    simp [List.length_append] at hprefix_len_le_i ⊢
                    omega
                  have hi_lt_next :
                      pieceStream.idxOf i < pieceStream.idxOf next := by
                    rw [hnext_eq]
                    exact hidx_i_lt_nextAfter
                  omega
          · rcases hcase with
              ⟨pre, next, middle, head, suffix, horder, hstream,
                _hhead_source, hnext_source, _hmiddle⟩
            have hnext_mem_stream : next ∈ pieceStream := by
              rw [hstream]
              simp
            have hnext_ret :
                sourceOption next = some q := by
              have hnext_listed : pieceSource next ∈ K.points := by
                have hqmem : (successor p).1 ∈ K.points := (successor p).2
                simpa [hnext_source] using hqmem
              have hq_eq :
                  (⟨pieceSource next, hnext_listed⟩ :
                    {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points}) = q := by
                apply Subtype.ext
                calc
                  pieceSource next = (successor p).1 := hnext_source
                  _ = q.1 := by rw [hsucc_p]
              simp [hsourceOption, hnext_listed, hq_eq]
            have hnext_eq :
                next = nextAfter :=
              hsource_unique hnext_mem_stream
                (by
                  rw [hsplit_next]
                  simp)
                hnext_ret hnextAfter_ret
            have hstream_next :
                pieceStream = pre ++ next :: (middle ++ head :: suffix) := by
              rw [hstream]
              simp [List.append_assoc]
            have hidx_next : pieceStream.idxOf next = pre.length :=
              idx_at_cons hstream_next
            have hi_mem_arc :
                i ∈ pre ∨ i = next ∨ i ∈ middle ∨ i = head ∨ i ∈ suffix := by
              have hi_stream :
                  i ∈ pre ++ (next :: middle) ++ (head :: suffix) := by
                simpa [hstream] using hstream_mem i
              simpa [List.mem_append, or_assoc] using hi_stream
            rcases hi_mem_arc with hi_pre | hi_rest
            · simp [horder, hi_pre]
            · rcases hi_rest with hi_eq_next | hi_rest
              · have hnone_next : sourceOption next = none := by
                  simpa [hi_eq_next] using hi_none
                rw [hnext_ret] at hnone_next
                simp at hnone_next
              · rcases hi_rest with hi_middle | hi_rest
                · have hprefix_len_le_i :
                      (pre ++ [next]).length ≤ pieceStream.idxOf i := by
                    apply le_of_not_gt
                    intro hlt
                    have hi_pref : i ∈ pre ++ [next] := by
                      apply mem_prefix_of_idx_lt
                        (x := i) (pref := pre ++ [next])
                        (suffix := middle ++ head :: suffix)
                      · rw [hstream_next]
                        simp [List.append_assoc]
                      · exact hlt
                    have hnod :
                        (pre ++ [next] ++ (middle ++ head :: suffix)).Nodup := by
                      simpa [hstream_next, List.append_assoc] using hstream_nodup
                    have hdisj :=
                      List.disjoint_of_nodup_append
                        (l₁ := pre ++ [next])
                        (l₂ := middle ++ head :: suffix) hnod
                    exact hdisj hi_pref (by simp [hi_middle])
                  have hnext_lt_i :
                      pieceStream.idxOf next < pieceStream.idxOf i := by
                    rw [hidx_next]
                    simp [List.length_append] at hprefix_len_le_i ⊢
                    omega
                  have hi_lt_next :
                      pieceStream.idxOf i < pieceStream.idxOf next := by
                    rw [hnext_eq]
                    exact hidx_i_lt_nextAfter
                  omega
                · rcases hi_rest with hi_eq_head | hi_suffix
                  · rw [hi_eq_head]
                    simp [horder]
                  · simp [horder, hi_suffix]
      | nil =>
          have hpost_none :
              ∀ x ∈ postI, sourceOption x = none := by
            exact
              (List.filterMap_eq_nil_iff (f := sourceOption) (l := postI)).1
                hpost_ret
          have hpoints_two : 1 < K.points.card := by
            have htwo := FinitePolygonalSetCarrierEqSimpleClosedCurvePointsTwo J K hKJ
            omega
          rcases Finset.one_lt_card.1 hpoints_two with ⟨a, ha, b, hb, hab⟩
          let qa : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points} :=
            ⟨a, ha⟩
          have hsource_nonempty : sourceOccurrenceList ≠ [] := by
            intro hnil
            have hmem := hsource_covers qa
            simp [hnil] at hmem
          have hpre_filter_nonempty : preI.filterMap sourceOption ≠ [] := by
            intro hnil
            apply hsource_nonempty
            rw [hfilter_split, hpost_ret, hnil]
            simp
          cases hpre_ret : preI.filterMap sourceOption with
          | nil =>
              exact False.elim (hpre_filter_nonempty hpre_ret)
          | cons q qs =>
              rcases
                (List.filterMap_eq_cons_iff
                  (f := sourceOption) (l := preI) (b := q) (bs := qs)).1
                  hpre_ret with
                ⟨noneBefore, nextAfter, beforeAfter, hpre_decomp,
                  hnoneBefore_filter, hnextAfter_ret, _hbeforeAfter_filter⟩
              have hnoneBefore :
                  ∀ x ∈ noneBefore, sourceOption x = none :=
                hnoneBefore_filter
              have hsplit_first :
                  pieceStream =
                    noneBefore ++ nextAfter :: (beforeAfter ++ i :: postI) := by
                rw [hsplit_i, hpre_decomp]
                simp [List.append_assoc]
              have hidx_nextAfter :
                  pieceStream.idxOf nextAfter = noneBefore.length :=
                idx_at_cons hsplit_first
              let p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points} :=
                successor.symm q
              have hsucc_p : successor p = q := by
                simp [p]
              refine ⟨p, ?_⟩
              rcases arcPieceOrder_cases p with hcase | hcase
              · rcases hcase with
                  ⟨pre, head, middle, next, suffix, horder, hstream,
                    hhead_source, hnext_source, _hmiddle⟩
                have hhead_mem_stream : head ∈ pieceStream := by
                  rw [hstream]
                  simp [horder]
                have hnext_mem_stream : next ∈ pieceStream := by
                  rw [hstream]
                  simp
                have hhead_ret :
                    sourceOption head = some p := by
                  have hhead_listed : pieceSource head ∈ K.points := by
                    simpa [hhead_source] using p.2
                  have hp_eq :
                      (⟨pieceSource head, hhead_listed⟩ :
                        {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points}) = p := by
                    exact Subtype.ext hhead_source
                  simp [hsourceOption, hhead_listed, hp_eq]
                have hnext_ret :
                    sourceOption next = some q := by
                  have hnext_listed : pieceSource next ∈ K.points := by
                    have hqmem : (successor p).1 ∈ K.points := (successor p).2
                    simpa [hnext_source] using hqmem
                  have hq_eq :
                      (⟨pieceSource next, hnext_listed⟩ :
                        {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points}) = q := by
                    apply Subtype.ext
                    calc
                      pieceSource next = (successor p).1 := hnext_source
                      _ = q.1 := by rw [hsucc_p]
                  simp [hsourceOption, hnext_listed, hq_eq]
                have hnext_eq :
                    next = nextAfter :=
                  hsource_unique hnext_mem_stream
                    (by
                      rw [hsplit_first]
                      simp)
                    hnext_ret hnextAfter_ret
                have hstream_head :
                    pieceStream = pre ++ head :: (middle ++ next :: suffix) := by
                  rw [hstream, horder]
                  simp [List.append_assoc]
                have hidx_head : pieceStream.idxOf head = pre.length :=
                  idx_at_cons hstream_head
                have hstream_next :
                    pieceStream = (pre ++ head :: middle) ++ next :: suffix := by
                  rw [hstream, horder]
                have hidx_next :
                    pieceStream.idxOf next =
                      (pre ++ head :: middle).length :=
                  idx_at_cons hstream_next
                have hhead_lt_nextAfter :
                    pieceStream.idxOf head < pieceStream.idxOf nextAfter := by
                  rw [← hnext_eq, hidx_head, hidx_next]
                  simp
                have hhead_in_none :
                    head ∈ noneBefore := by
                  apply mem_prefix_of_idx_lt
                    (x := head) (pref := noneBefore)
                    (suffix := nextAfter :: (beforeAfter ++ i :: postI))
                  · exact hsplit_first
                  · simpa [hidx_nextAfter] using hhead_lt_nextAfter
                have hnone := hnoneBefore head hhead_in_none
                rw [hhead_ret] at hnone
                simp at hnone
              · rcases hcase with
                  ⟨pre, next, middle, head, suffix, horder, hstream,
                    hhead_source, hnext_source, _hmiddle⟩
                have hhead_mem_stream : head ∈ pieceStream := by
                  rw [hstream]
                  simp
                have hnext_mem_stream : next ∈ pieceStream := by
                  rw [hstream]
                  simp
                have hhead_ret :
                    sourceOption head = some p := by
                  have hhead_listed : pieceSource head ∈ K.points := by
                    simpa [hhead_source] using p.2
                  have hp_eq :
                      (⟨pieceSource head, hhead_listed⟩ :
                        {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points}) = p := by
                    exact Subtype.ext hhead_source
                  simp [hsourceOption, hhead_listed, hp_eq]
                have hnext_ret :
                    sourceOption next = some q := by
                  have hnext_listed : pieceSource next ∈ K.points := by
                    have hqmem : (successor p).1 ∈ K.points := (successor p).2
                    simpa [hnext_source] using hqmem
                  have hq_eq :
                      (⟨pieceSource next, hnext_listed⟩ :
                        {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points}) = q := by
                    apply Subtype.ext
                    calc
                      pieceSource next = (successor p).1 := hnext_source
                      _ = q.1 := by rw [hsucc_p]
                  simp [hsourceOption, hnext_listed, hq_eq]
                have hnext_eq :
                    next = nextAfter :=
                  hsource_unique hnext_mem_stream
                    (by
                      rw [hsplit_first]
                      simp)
                    hnext_ret hnextAfter_ret
                have hstream_head :
                    pieceStream =
                      (pre ++ next :: middle) ++ head :: suffix := by
                  rw [hstream]
                have hidx_head :
                    pieceStream.idxOf head =
                      (pre ++ next :: middle).length :=
                  idx_at_cons hstream_head
                have hi_mem_arc :
                    i ∈ pre ∨ i = next ∨ i ∈ middle ∨ i = head ∨ i ∈ suffix := by
                  have hi_stream :
                      i ∈ pre ++ (next :: middle) ++ (head :: suffix) := by
                    simpa [hstream] using hstream_mem i
                  simpa [List.mem_append, or_assoc] using hi_stream
                rcases hi_mem_arc with hi_pre | hi_rest
                · simp [horder, hi_pre]
                · rcases hi_rest with hi_eq_next | hi_rest
                  · have hnone_next : sourceOption next = none := by
                      simpa [hi_eq_next] using hi_none
                    rw [hnext_ret] at hnone_next
                    simp at hnone_next
                  · rcases hi_rest with hi_middle | hi_rest
                    · have hprefix_len_le_head :
                          (preI ++ [i]).length ≤ pieceStream.idxOf head := by
                        have hidx_i_lt_head :
                            pieceStream.idxOf i < pieceStream.idxOf head := by
                          rw [hidx_head]
                          have hpref : pre ++ next :: middle <+: pieceStream := by
                            rw [hstream]
                            exact ⟨head :: suffix, by simp [List.append_assoc]⟩
                          exact
                            (hpref.mem_iff_idxOf_lt_length i).1
                              (by simp [hi_middle])
                        rw [hidx_i] at hidx_i_lt_head
                        simp [List.length_append] at hidx_i_lt_head ⊢
                        omega
                      have hhead_in_post : head ∈ postI := by
                        apply mem_suffix_of_idx_ge
                          (x := head) (pref := preI ++ [i])
                          (suffix := postI)
                        · simpa [List.append_assoc] using hsplit_i
                        · exact hhead_mem_stream
                        · exact hprefix_len_le_head
                      have hnone := hpost_none head hhead_in_post
                      rw [hhead_ret] at hnone
                      simp at hnone
                    · rcases hi_rest with hi_eq_head | hi_suffix
                      · rw [hi_eq_head]
                        simp [horder]
                      · simp [horder, hi_suffix]
  exact hpiece_mem_arcPieceOrder

-- [TABLET NODE: FinitePolygonalSetCyclicActualPieceStreamCases]
lemma FinitePolygonalSetCyclicActualPieceStreamCases
    (J : SimpleClosedPolygonalCurve) (K : FinitePolygonalSet)
    (hKJ : K.carrier = J.carrier) :
    ∃ (PieceIndex : Type) (_pieceIndex_fintype : Fintype PieceIndex)
      (successor : Equiv.Perm {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points})
      (pieceArc : PieceIndex → {γ : PolygonalArc // γ ∈ J.edgeArcs})
      (pieceSegmentIndex :
        (i : PieceIndex) → {n : ℕ // n + 1 < (pieceArc i).1.vertices.length})
      (pieceSource pieceTarget : PieceIndex → EuclideanSpace ℝ (Fin 2))
      (pieceSourceParam pieceTargetParam : PieceIndex → Set.Icc (0 : ℝ) 1)
      (pieceCarrier : PieceIndex → Set (EuclideanSpace ℝ (Fin 2)))
      (arcPieceOrder :
        {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points} → List PieceIndex),
        (∀ i, pieceSourceParam i < pieceTargetParam i) ∧
          (∀ i,
            pieceSource i =
              AffineMap.lineMap
                ((pieceArc i).1.vertices[(pieceSegmentIndex i).1]'
                  (Nat.lt_of_succ_lt (pieceSegmentIndex i).2))
                ((pieceArc i).1.vertices[(pieceSegmentIndex i).1 + 1]'
                  (pieceSegmentIndex i).2)
                (pieceSourceParam i).1) ∧
          (∀ i,
            pieceTarget i =
              AffineMap.lineMap
                ((pieceArc i).1.vertices[(pieceSegmentIndex i).1]'
                  (Nat.lt_of_succ_lt (pieceSegmentIndex i).2))
                ((pieceArc i).1.vertices[(pieceSegmentIndex i).1 + 1]'
                  (pieceSegmentIndex i).2)
                (pieceTargetParam i).1) ∧
          (∀ i, pieceCarrier i = segment ℝ (pieceSource i) (pieceTarget i)) ∧
          (∀ i (v : EuclideanSpace ℝ (Fin 2)),
            v ∈ K.points → v ∉ openSegment ℝ (pieceSource i) (pieceTarget i)) ∧
          (∀ p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points},
            (arcPieceOrder p).length ≠ 0) ∧
          (∀ (p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points}) i,
            (arcPieceOrder p).head? = some i → pieceSource i = p.1) ∧
          (∀ (p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points}) i,
            (arcPieceOrder p).getLast? = some i →
              pieceTarget i = (successor p).1) ∧
          (∀ (p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points})
            n (hn : n + 1 < (arcPieceOrder p).length),
            pieceTarget ((arcPieceOrder p)[n]) =
                pieceSource ((arcPieceOrder p)[n + 1]) ∧
              ((pieceArc ((arcPieceOrder p)[n]) =
                    pieceArc ((arcPieceOrder p)[n + 1]) ∧
                  (pieceSegmentIndex ((arcPieceOrder p)[n])).1 =
                    (pieceSegmentIndex ((arcPieceOrder p)[n + 1])).1 ∧
                  pieceTargetParam ((arcPieceOrder p)[n]) =
                    pieceSourceParam ((arcPieceOrder p)[n + 1])) ∨
                (pieceArc ((arcPieceOrder p)[n]) =
                    pieceArc ((arcPieceOrder p)[n + 1]) ∧
                  (pieceSegmentIndex ((arcPieceOrder p)[n])).1 + 1 =
                    (pieceSegmentIndex ((arcPieceOrder p)[n + 1])).1 ∧
                  (pieceTargetParam ((arcPieceOrder p)[n])).1 = 1 ∧
                  (pieceSourceParam ((arcPieceOrder p)[n + 1])).1 = 0) ∨
                (pieceArc ((arcPieceOrder p)[n + 1]) =
                    J.successor (pieceArc ((arcPieceOrder p)[n])) ∧
                  (pieceSegmentIndex ((arcPieceOrder p)[n])).1 + 2 =
                    (pieceArc ((arcPieceOrder p)[n])).1.vertices.length ∧
                  (pieceSegmentIndex ((arcPieceOrder p)[n + 1])).1 = 0 ∧
                  (pieceTargetParam ((arcPieceOrder p)[n])).1 = 1 ∧
                  (pieceSourceParam ((arcPieceOrder p)[n + 1])).1 = 0))) ∧
          (∀ (p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points}) i,
            i ∈ (arcPieceOrder p).tail → pieceSource i ∉ K.points) ∧
          (∀ (p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points}) i,
            i ∈ arcPieceOrder p → pieceSource i ∈ K.points →
              pieceSource i = p.1) ∧
          (∀ (p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points}) i,
            i ∈ arcPieceOrder p → pieceTarget i ∈ K.points →
              pieceTarget i = (successor p).1) ∧
          (∀ p q : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points},
            ∃ n : ℕ, (successor^[n]) p = q) ∧
          (∀ p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points},
            p.1 ≠ (successor p).1) ∧
          J.carrier ⊆ ⋃ i : PieceIndex, pieceCarrier i ∧
          (∀ i : PieceIndex,
            ∃ p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points},
              i ∈ arcPieceOrder p) ∧
          ∃ pieceStream : List PieceIndex,
            pieceStream.Nodup ∧
              (∀ i : PieceIndex, i ∈ pieceStream) ∧
                (∀ (p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points}) i,
                  i ∈ arcPieceOrder p → i ∈ pieceStream) ∧
                  (∀ p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points},
                    ((∃ (pre : List PieceIndex) (head : PieceIndex)
                          (middle : List PieceIndex) (next : PieceIndex)
                          (suffix : List PieceIndex),
                        arcPieceOrder p = head :: middle ∧
                          pieceStream =
                            pre ++ arcPieceOrder p ++ (next :: suffix) ∧
                          pieceSource head = p.1 ∧
                          pieceSource next = (successor p).1 ∧
                          ∀ i ∈ middle, pieceSource i ∉ K.points) ∨
                      (∃ (pre : List PieceIndex) (next : PieceIndex)
                          (middle : List PieceIndex) (head : PieceIndex)
                          (suffix : List PieceIndex),
                        arcPieceOrder p = head :: (suffix ++ pre) ∧
                          pieceStream =
                            pre ++ (next :: middle) ++ (head :: suffix) ∧
                          pieceSource head = p.1 ∧
                          pieceSource next = (successor p).1 ∧
                          ∀ i ∈ suffix ++ pre,
                            pieceSource i ∉ K.points))) ∧
                    (∀ n (hn : n + 1 < pieceStream.length),
                      pieceTarget pieceStream[n] =
                          pieceSource pieceStream[n + 1] ∧
                        ((pieceArc pieceStream[n] =
                              pieceArc pieceStream[n + 1] ∧
                            (pieceSegmentIndex pieceStream[n]).1 =
                              (pieceSegmentIndex pieceStream[n + 1]).1 ∧
                            pieceTargetParam pieceStream[n] =
                              pieceSourceParam pieceStream[n + 1]) ∨
                          (pieceArc pieceStream[n] =
                              pieceArc pieceStream[n + 1] ∧
                            (pieceSegmentIndex pieceStream[n]).1 + 1 =
                              (pieceSegmentIndex pieceStream[n + 1]).1 ∧
                            (pieceTargetParam pieceStream[n]).1 = 1 ∧
                            (pieceSourceParam pieceStream[n + 1]).1 = 0) ∨
                          (pieceArc pieceStream[n + 1] =
                              J.successor (pieceArc pieceStream[n]) ∧
                            (pieceSegmentIndex pieceStream[n]).1 + 2 =
                              (pieceArc pieceStream[n]).1.vertices.length ∧
                            (pieceSegmentIndex pieceStream[n + 1]).1 = 0 ∧
                            (pieceTargetParam pieceStream[n]).1 = 1 ∧
                            (pieceSourceParam pieceStream[n + 1]).1 = 0))) ∧
                    (∀ i, pieceStream.getLast? = some i →
                      ∀ j, pieceStream.head? = some j →
                        pieceTarget i = pieceSource j ∧
                          ((pieceArc i = pieceArc j ∧
                              (pieceSegmentIndex i).1 =
                                (pieceSegmentIndex j).1 ∧
                              pieceTargetParam i = pieceSourceParam j) ∨
                            (pieceArc i = pieceArc j ∧
                              (pieceSegmentIndex i).1 + 1 =
                                (pieceSegmentIndex j).1 ∧
                              (pieceTargetParam i).1 = 1 ∧
                              (pieceSourceParam j).1 = 0) ∨
                            (pieceArc j = J.successor (pieceArc i) ∧
                              (pieceSegmentIndex i).1 + 2 =
                                (pieceArc i).1.vertices.length ∧
                              (pieceSegmentIndex j).1 = 0 ∧
                              (pieceTargetParam i).1 = 1 ∧
                              (pieceSourceParam j).1 = 0))) ∧
                    (∀ i j : PieceIndex,
                      i ∈ pieceStream → j ∈ pieceStream →
                        pieceSource i ∈ K.points → pieceSource j ∈ K.points →
                          pieceSource i = pieceSource j → i = j) ∧
                    (∀ i j : PieceIndex, pieceSource i = pieceSource j → i = j) ∧
                    (∀ i j : PieceIndex, i ≠ j →
                      pieceArc i = pieceArc j →
                        (pieceSegmentIndex i).1 = (pieceSegmentIndex j).1 →
                          ∀ x : EuclideanSpace ℝ (Fin 2),
                            x ∈ pieceCarrier i → x ∈ pieceCarrier j →
                              x ∈ K.points) := by
-- BODY
  classical
  rcases FinitePolygonalSetCyclicGlobalElementaryPieceSkeleton J K with
    ⟨E, hEnodup, hEall, hEpos, hEsucc, hEwrap,
      segmentIndex_lt, cutList, cutList_nodup, cutList_sorted, cutList_mem,
      cutList_zero, cutList_one, cutList_bounds, cutList_lt,
      localPieceIndex, localPieceFintype, pieceIndexFintype,
      pieceNumber, pieceNumber_lt, pieceEdgePosition, pieceArc,
      pieceSegmentIndexRaw, pieceSourceParam, pieceTargetParam, pieceSource,
      pieceTarget, pieceCarrier, pieceEdgePosition_eq, pieceArc_eq_raw,
      pieceSegmentIndexRaw_eq, pieceNumber_surjective, pieceNumber_injective,
      pieceSourceParam_lt, pieceSourceParam_eq, pieceTargetParam_eq,
      pieceSource_eq_global, pieceTarget_eq_global, pieceCarrier_eq,
      no_listed_open_piece⟩
  let PieceIndex : Type :=
    Sigma (fun e : Fin E.length =>
      Sigma (fun n : Fin ((E[e.1]'e.2).1.vertices.length - 1) =>
        localPieceIndex e n))
  have pieceArc_eq :
      ∀ i : PieceIndex, pieceArc i = E[i.1.1]'i.1.2 := by
    intro i
    calc
      pieceArc i = E[(pieceEdgePosition i).1]'(pieceEdgePosition i).2 :=
        pieceArc_eq_raw i
      _ = E[i.1.1]'i.1.2 := by
        rw [pieceEdgePosition_eq i]
  let pieceSegmentIndex :
      (i : PieceIndex) → {n : ℕ // n + 1 < (pieceArc i).1.vertices.length} :=
    fun i =>
      ⟨(pieceSegmentIndexRaw i).1, by
        simpa [pieceArc_eq i] using (pieceSegmentIndexRaw i).2⟩
  have pieceSegmentIndex_eq :
      ∀ i : PieceIndex, (pieceSegmentIndex i).1 = i.2.1.1 := by
    intro i
    exact pieceSegmentIndexRaw_eq i
  have pieceSource_eq_arc :
      ∀ i : PieceIndex,
        pieceSource i =
          AffineMap.lineMap
            ((pieceArc i).1.vertices[(pieceSegmentIndex i).1]'
              (Nat.lt_of_succ_lt (pieceSegmentIndex i).2))
            ((pieceArc i).1.vertices[(pieceSegmentIndex i).1 + 1]'
              (pieceSegmentIndex i).2)
            (pieceSourceParam i).1 := by
    intro i
    simpa [pieceSegmentIndex, pieceArc_eq i, pieceSegmentIndexRaw_eq i]
      using pieceSource_eq_global i
  have pieceTarget_eq_arc :
      ∀ i : PieceIndex,
        pieceTarget i =
          AffineMap.lineMap
            ((pieceArc i).1.vertices[(pieceSegmentIndex i).1]'
              (Nat.lt_of_succ_lt (pieceSegmentIndex i).2))
            ((pieceArc i).1.vertices[(pieceSegmentIndex i).1 + 1]'
              (pieceSegmentIndex i).2)
            (pieceTargetParam i).1 := by
    intro i
    simpa [pieceSegmentIndex, pieceArc_eq i, pieceSegmentIndexRaw_eq i]
      using pieceTarget_eq_global i
  rcases
    FinitePolygonalSetCyclicActualNormalizedSourceCycle
      J K hKJ E hEnodup hEall hEpos hEsucc hEwrap segmentIndex_lt
      cutList cutList_nodup cutList_sorted cutList_mem cutList_zero
      cutList_one cutList_bounds localPieceIndex pieceNumber pieceNumber_lt
      pieceNumber_surjective pieceNumber_injective pieceSourceParam
      pieceTargetParam pieceSourceParam_lt pieceSourceParam_eq
      pieceTargetParam_eq pieceArc pieceSegmentIndex pieceSource pieceTarget
      pieceArc_eq pieceSegmentIndex_eq pieceSource_eq_global
      pieceTarget_eq_global pieceSource_eq_arc pieceTarget_eq_arc with
    ⟨pieceAt, pieceStream, horder_nodup, horder_mem, hpieceAt_edge,
      hpieceAt_segment, hpieceAt_number, hpieceAt_injective, hstream_eq,
      hstream_nodup, hstream_mem, hstream_pos, hstream_consecutive_endpoint,
      hstream_cyclic_endpoint, sourceOccurrenceList, hsource_eq,
      hsource_nodup, hsource_listed, hsource_covers, hsource_cert,
      hsource_boundary⟩
  let ConsecutiveOK : PieceIndex → PieceIndex → Prop := fun i j =>
    pieceTarget i = pieceSource j ∧
      ((pieceArc i = pieceArc j ∧
          (pieceSegmentIndex i).1 = (pieceSegmentIndex j).1 ∧
          pieceTargetParam i = pieceSourceParam j) ∨
        (pieceArc i = pieceArc j ∧
          (pieceSegmentIndex i).1 + 1 = (pieceSegmentIndex j).1 ∧
          (pieceTargetParam i).1 = 1 ∧
          (pieceSourceParam j).1 = 0) ∨
        (pieceArc j = J.successor (pieceArc i) ∧
          (pieceSegmentIndex i).1 + 2 = (pieceArc i).1.vertices.length ∧
          (pieceSegmentIndex j).1 = 0 ∧
          (pieceTargetParam i).1 = 1 ∧
          (pieceSourceParam j).1 = 0))
  have hbridge :
      0 < pieceStream.length ∧
        (∀ n (hn : n + 1 < pieceStream.length),
          ConsecutiveOK pieceStream[n] pieceStream[n + 1]) ∧
        (∀ i, pieceStream.getLast? = some i →
          ∀ j, pieceStream.head? = some j → ConsecutiveOK i j) := by
    simpa [ConsecutiveOK] using
      FinitePolygonalSetCyclicActualStreamEndpointContinuityBridge
        J K E hEpos hEsucc hEwrap cutList cutList_sorted cutList_zero
        cutList_one cutList_bounds localPieceIndex pieceNumber pieceNumber_lt
        pieceSourceParam pieceTargetParam pieceSourceParam_eq
        pieceTargetParam_eq pieceArc pieceSegmentIndex pieceSource pieceTarget
        pieceArc_eq pieceSegmentIndex_eq pieceSource_eq_arc
        pieceTarget_eq_arc pieceAt pieceStream hpieceAt_edge
        hpieceAt_segment hpieceAt_number hstream_eq
  rcases hbridge with ⟨_hstream_pos_full, hstream_consecutive, hstream_cyclic⟩
  rcases
    FinitePolygonalSetCyclicActualStreamIntervalBlocks
      J K hKJ pieceStream pieceSource pieceTarget ConsecutiveOK
      (by intro i j h; exact h.1)
      hstream_consecutive hstream_cyclic sourceOccurrenceList hsource_eq
      hsource_nodup hsource_covers with
    ⟨successor, hsuccessor_eq, hsuccessor_cycle, hsuccessor_nondeg,
      hblocks⟩
  choose arcPieceOrder arcPieceOrder_nonempty arcPieceOrder_head_source
    arcPieceOrder_last_target arcPieceOrder_chain arcPieceOrder_tail_no_source
    arcPieceOrder_mem_stream arcPieceOrder_cases using hblocks
  have arcPieceOrder_consecutive_ok :
      ∀ (p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points})
        n (hn : n + 1 < (arcPieceOrder p).length),
        ConsecutiveOK (arcPieceOrder p)[n] (arcPieceOrder p)[n + 1] := by
    intro p n hn
    exact List.isChain_iff_getElem.mp (arcPieceOrder_chain p) n hn
  have pieceSource_listed_eq_start :
      ∀ (p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points}) i,
        i ∈ arcPieceOrder p → pieceSource i ∈ K.points →
          pieceSource i = p.1 := by
    exact
      FinitePolygonalSetCyclicActualSourceEqStart K pieceSource arcPieceOrder
        arcPieceOrder_nonempty arcPieceOrder_head_source
        arcPieceOrder_tail_no_source
  have pieceTarget_listed_eq_target :
      ∀ (p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points}) i,
        i ∈ arcPieceOrder p → pieceTarget i ∈ K.points →
          pieceTarget i = (successor p).1 := by
    exact
      FinitePolygonalSetCyclicActualTargetEqSuccessor K successor pieceSource
        pieceTarget arcPieceOrder arcPieceOrder_last_target
        (fun p n hn => (arcPieceOrder_consecutive_ok p n hn).1)
        arcPieceOrder_tail_no_source
  have hpieceCarrier_covers_curve :
      J.carrier ⊆ ⋃ i : PieceIndex, pieceCarrier i := by
    apply
      FinitePolygonalSetCyclicActualCarrierCoverage J E hEall
        segmentIndex_lt cutList cutList_sorted cutList_zero cutList_one
        cutList_bounds localPieceIndex
        (fun e n a => (⟨e, ⟨n, a⟩⟩ : PieceIndex)) pieceNumber
        (fun e n a => pieceNumber_lt (⟨e, ⟨n, a⟩⟩ : PieceIndex))
        pieceNumber_surjective pieceSourceParam pieceTargetParam pieceSource
        pieceTarget pieceCarrier
    · intro e n a
      exact pieceSourceParam_eq (⟨e, ⟨n, a⟩⟩ : PieceIndex)
    · intro e n a
      exact pieceTargetParam_eq (⟨e, ⟨n, a⟩⟩ : PieceIndex)
    · intro e n a
      exact pieceSource_eq_global (⟨e, ⟨n, a⟩⟩ : PieceIndex)
    · intro e n a
      exact pieceTarget_eq_global (⟨e, ⟨n, a⟩⟩ : PieceIndex)
    · intro e n a
      exact pieceCarrier_eq (⟨e, ⟨n, a⟩⟩ : PieceIndex)
  let sourceOption :
      PieceIndex → Option {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points} :=
    fun i =>
      if h : pieceSource i ∈ K.points then
        some (⟨pieceSource i, h⟩ :
          {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points})
      else none
  have hsource_filter :
      sourceOccurrenceList = pieceStream.filterMap sourceOption := by
    rw [hsource_eq, List.filterMap_eq_flatMap_toList]
    congr 1
    funext i
    by_cases h : pieceSource i ∈ K.points
    · simp [sourceOption, h]
    · simp [sourceOption, h]
  have hsource_unique :
      ∀ {x y : PieceIndex} {p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points}},
        x ∈ pieceStream → y ∈ pieceStream →
          sourceOption x = some p →
          sourceOption y = some p →
          x = y := by
    have filterMap_unique_of_nodup :
        ∀ {stream : List PieceIndex}
          {retain :
            PieceIndex →
              Option {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points}}
          {x y : PieceIndex}
          {p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points}},
          (stream.filterMap retain).Nodup →
          x ∈ stream → y ∈ stream →
          retain x = some p → retain y = some p → x = y := by
      intro stream retain x y p hnodup hx hy hxret hyret
      induction stream generalizing x y p with
      | nil =>
          simp at hx
      | cons a l ih =>
          simp only [List.mem_cons] at hx hy
          cases hreta : retain a with
          | none =>
              have hnodup_l : (l.filterMap retain).Nodup := by
                simpa [hreta] using hnodup
              rcases hx with hx_eq | hx_l
              · subst x
                simp [hreta] at hxret
              rcases hy with hy_eq | hy_l
              · subst y
                simp [hreta] at hyret
              exact ih hnodup_l hx_l hy_l hxret hyret
          | some q =>
              have hnodup_cons : (q :: l.filterMap retain).Nodup := by
                simpa [hreta] using hnodup
              have hq_notin : q ∉ l.filterMap retain := hnodup_cons.notMem
              have hnodup_l : (l.filterMap retain).Nodup := hnodup_cons.of_cons
              rcases hx with hx_eq | hx_l
              · subst x
                simp [hreta] at hxret
                subst q
                rcases hy with hy_eq | hy_l
                · subst y
                  rfl
                · have hp_mem : p ∈ l.filterMap retain := by
                    exact List.mem_filterMap.2 ⟨y, hy_l, hyret⟩
                  exact False.elim (hq_notin hp_mem)
              · rcases hy with hy_eq | hy_l
                · subst y
                  simp [hreta] at hyret
                  subst q
                  have hp_mem : p ∈ l.filterMap retain := by
                    exact List.mem_filterMap.2 ⟨x, hx_l, hxret⟩
                  exact False.elim (hq_notin hp_mem)
                · exact ih hnodup_l hx_l hy_l hxret hyret
    intro x y p hx hy hxret hyret
    have hnodup_filter : (pieceStream.filterMap sourceOption).Nodup := by
      simpa [hsource_filter] using hsource_nodup
    exact
      filterMap_unique_of_nodup
        (stream := pieceStream) (retain := sourceOption)
        (x := x) (y := y) (p := p)
        hnodup_filter hx hy hxret hyret
  have hpiece_mem_arcPieceOrder :
      ∀ i : PieceIndex,
        ∃ p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points},
          i ∈ arcPieceOrder p := by
    exact
      FinitePolygonalSetCyclicActualEveryPieceInOrder J K hKJ successor
        pieceSource pieceStream sourceOccurrenceList sourceOption
        (by
          intro i
          simp [sourceOption])
        arcPieceOrder hstream_nodup hstream_mem hsource_covers hsource_filter
        hsource_unique arcPieceOrder_cases
  have hretained_source_unique :
      ∀ i j : PieceIndex,
        i ∈ pieceStream → j ∈ pieceStream →
          pieceSource i ∈ K.points → pieceSource j ∈ K.points →
            pieceSource i = pieceSource j → i = j := by
    intro i j hi hj hi_source hj_source hsame_source
    let p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points} :=
      ⟨pieceSource i, hi_source⟩
    have hi_ret : sourceOption i = some p := by
      simp [sourceOption, p, hi_source]
    have hj_ret : sourceOption j = some p := by
      have hp_eq :
          (⟨pieceSource j, hj_source⟩ :
            {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points}) = p :=
        Subtype.ext hsame_source.symm
      simp [sourceOption, p, hj_source, hp_eq]
    exact hsource_unique hi hj hi_ret hj_ret
  have hsource_separation_all :
      ∀ i j : PieceIndex, pieceSource i = pieceSource j → i = j := by
    exact
      FinitePolygonalSetCyclicGlobalSourceSeparation
        J E hEnodup segmentIndex_lt cutList cutList_nodup cutList_bounds
        localPieceIndex pieceNumber pieceNumber_lt pieceNumber_injective
        pieceSourceParam pieceTargetParam pieceSourceParam_lt
        pieceSourceParam_eq pieceTargetParam_eq pieceSource pieceSource_eq_global
  refine
    ⟨PieceIndex, pieceIndexFintype, successor, pieceArc, pieceSegmentIndex,
      pieceSource, pieceTarget, pieceSourceParam, pieceTargetParam,
      pieceCarrier, arcPieceOrder, pieceSourceParam_lt, pieceSource_eq_arc,
      pieceTarget_eq_arc, pieceCarrier_eq, no_listed_open_piece,
      arcPieceOrder_nonempty, arcPieceOrder_head_source,
      arcPieceOrder_last_target, (by
        intro p n hn
        simpa only [ConsecutiveOK] using
          arcPieceOrder_consecutive_ok p n hn),
      arcPieceOrder_tail_no_source, pieceSource_listed_eq_start,
      pieceTarget_listed_eq_target, hsuccessor_cycle, hsuccessor_nondeg,
      hpieceCarrier_covers_curve, hpiece_mem_arcPieceOrder,
      ⟨pieceStream, hstream_nodup, hstream_mem, arcPieceOrder_mem_stream,
        arcPieceOrder_cases, (by
          intro n hn
          simpa only [ConsecutiveOK] using hstream_consecutive n hn), (by
          intro i hi j hj
          simpa only [ConsecutiveOK] using hstream_cyclic i hi j hj),
        hretained_source_unique, hsource_separation_all, ?_⟩⟩
  intro i j hij harc hseg x hxi hxj
  rcases i with ⟨e, n, a⟩
  rcases j with ⟨f, m, b⟩
  have hef_get :
      E[e.1]'e.2 = E[f.1]'f.2 := by
    calc
      E[e.1]'e.2 = pieceArc (⟨e, ⟨n, a⟩⟩ : PieceIndex) :=
        (pieceArc_eq (⟨e, ⟨n, a⟩⟩ : PieceIndex)).symm
      _ = pieceArc (⟨f, ⟨m, b⟩⟩ : PieceIndex) := harc
      _ = E[f.1]'f.2 := pieceArc_eq (⟨f, ⟨m, b⟩⟩ : PieceIndex)
  have hef : e = f := by
    exact Fin.ext ((hEnodup.getElem_inj_iff).mp hef_get)
  subst f
  have hnm : n = m := by
    apply Fin.ext
    simpa [pieceSegmentIndex_eq] using hseg
  subst m
  let A : EuclideanSpace ℝ (Fin 2) :=
    (E[e.1]'e.2).1.vertices[n.1]'(Nat.lt_of_succ_lt (segmentIndex_lt e n))
  let B : EuclideanSpace ℝ (Fin 2) :=
    (E[e.1]'e.2).1.vertices[n.1 + 1]'(segmentIndex_lt e n)
  let L : List ℝ := cutList e n
  have hAB : A ≠ B := by
    intro hEq
    have hidx : n.1 = n.1 + 1 := by
      exact ((E[e.1]'e.2).1.simple_vertices.getElem_inj_iff).mp hEq
    omega
  let ii : PieceIndex := ⟨e, ⟨n, a⟩⟩
  let jj : PieceIndex := ⟨e, ⟨n, b⟩⟩
  let ki : ℕ := pieceNumber ii
  let kj : ℕ := pieceNumber jj
  have hki : ki + 1 < L.length := by
    simpa [ki, ii, L] using pieceNumber_lt ii
  have hkj : kj + 1 < L.length := by
    simpa [kj, jj, L] using pieceNumber_lt jj
  have hnum_ne : ki ≠ kj := by
    intro hnum
    apply hij
    have hab : a = b := by
      apply pieceNumber_injective e n a b
      simpa [ki, kj, ii, jj] using hnum
    subst b
    rfl
  have param_of_piece_mem :
      ∀ (c : localPieceIndex e n) {y : EuclideanSpace ℝ (Fin 2)},
        y ∈ pieceCarrier (⟨e, ⟨n, c⟩⟩ : PieceIndex) →
          ∃ t : ℝ,
            L[pieceNumber (⟨e, ⟨n, c⟩⟩ : PieceIndex)]'
                (Nat.lt_of_succ_lt
                  (by simpa [L] using
                    (pieceNumber_lt (⟨e, ⟨n, c⟩⟩ : PieceIndex)))) ≤ t ∧
              t ≤
                L[pieceNumber (⟨e, ⟨n, c⟩⟩ : PieceIndex) + 1]'
                  (by simpa [L] using
                    (pieceNumber_lt (⟨e, ⟨n, c⟩⟩ : PieceIndex))) ∧
              y = AffineMap.lineMap A B t := by
    intro c y hy
    let q : PieceIndex := ⟨e, ⟨n, c⟩⟩
    let k : ℕ := pieceNumber q
    have hk : k + 1 < L.length := by
      simpa [k, q, L] using pieceNumber_lt q
    have hlt : L[k]'(Nat.lt_of_succ_lt hk) < L[k + 1]'hk := by
      simpa [L, k, q] using cutList_lt e n k (by simpa [L, k, q] using hk)
    have hyseg :
        y ∈ segment ℝ
            (AffineMap.lineMap A B (L[k]'(Nat.lt_of_succ_lt hk)))
            (AffineMap.lineMap A B (L[k + 1]'hk)) := by
      simpa [q, k, A, B, L, pieceCarrier_eq, pieceSource_eq_global,
        pieceTarget_eq_global, pieceSourceParam_eq, pieceTargetParam_eq] using hy
    have hseg_image :
        segment ℝ
            (AffineMap.lineMap A B (L[k]'(Nat.lt_of_succ_lt hk)))
            (AffineMap.lineMap A B (L[k + 1]'hk)) =
          (AffineMap.lineMap A B) '' Set.Icc
            (L[k]'(Nat.lt_of_succ_lt hk)) (L[k + 1]'hk) := by
      rw [← image_segment ℝ (AffineMap.lineMap A B)
        (L[k]'(Nat.lt_of_succ_lt hk)) (L[k + 1]'hk),
        segment_eq_Icc hlt.le]
    rw [hseg_image] at hyseg
    rcases hyseg with ⟨t, ht, hty⟩
    refine ⟨t, ht.1, ht.2, hty.symm⟩
  rcases param_of_piece_mem a (y := x) (by simpa [ii] using hxi) with
    ⟨t, hki_le_t, ht_le_ki, hxt⟩
  rcases param_of_piece_mem b (y := x) (by simpa [jj] using hxj) with
    ⟨s, hkj_le_s, hs_le_kj, hxs⟩
  have hts : t = s := by
    exact (AffineMap.lineMap_injective ℝ hAB) (by rw [← hxt, ← hxs])
  subst s
  have hendpoint :
      2 ≤ L.length ∧
        (∀ h : 0 < L.length, L[0]'h = 0) ∧
          (∀ h : L.length - 1 < L.length,
            L[L.length - 1]'h = 1) := by
    simpa [L] using
      FiniteSortedRealCutListEndpointEntries L (by simpa [L] using cutList_sorted e n)
        (by simpa [L] using cutList_zero e n)
        (by simpa [L] using cutList_one e n)
        (by simpa [L] using cutList_bounds e n)
  have listed_of_internal_cut :
      ∀ (r : ℕ) (hr : r < L.length), 0 < r → r + 1 < L.length →
        x = AffineMap.lineMap A B (L[r]'hr) → x ∈ K.points := by
    intro r hr hpos hnotlast hxcut
    have hmem : (L[r]'hr) ∈ L := List.getElem_mem (l := L) (n := r) hr
    have hcut_mem :
        (L[r]'hr = 0 ∨ L[r]'hr = 1 ∨
          (0 ≤ L[r]'hr ∧ L[r]'hr ≤ 1 ∧
            AffineMap.lineMap A B (L[r]'hr) ∈ K.points)) := by
      simpa [L, A, B] using (cutList_mem e n (L[r]'hr)).1 (by simpa [L] using hmem)
    rcases hcut_mem with hzero | hone | hmid
    · have hfirst : L[0]'(by omega) = 0 := hendpoint.2.1 (by omega)
      have hget :
          (cutList e n)[r]'(by simpa [L] using hr) =
            (cutList e n)[0]'(by simpa [L] using (show 0 < L.length by omega)) := by
        simpa [L, hfirst] using hzero
      have hr0 : r = 0 := (cutList_nodup e n).getElem_inj_iff.mp hget
      omega
    · have hlast_lt : L.length - 1 < L.length := by omega
      have hlast : L[L.length - 1]'hlast_lt = 1 := hendpoint.2.2 hlast_lt
      have hget :
          (cutList e n)[r]'(by simpa [L] using hr) =
            (cutList e n)[L.length - 1]'(by simpa [L] using hlast_lt) := by
        simpa [L, hlast] using hone
      have hrlast : r = L.length - 1 :=
        (cutList_nodup e n).getElem_inj_iff.mp hget
      omega
    · simpa [hxcut] using hmid.2.2
  rcases lt_or_gt_of_ne hnum_ne with hlt_num | hgt_num
  · have hle_adj : kj ≤ ki + 1 := by
      apply le_of_not_gt
      intro hgap
      have hcut_lt :
          L[ki + 1]'hki < L[kj]'(Nat.lt_of_succ_lt hkj) := by
        exact (cutList_sorted e n).getElem_lt_getElem_of_lt (by
          simpa [L] using hgap)
      nlinarith
    have hkj_eq : kj = ki + 1 := by omega
    have ht_eq : t = L[ki + 1]'hki := by
      have hleft : L[ki + 1]'hki ≤ t := by
        simpa [ki, kj, ii, jj, hkj_eq] using hkj_le_s
      exact le_antisymm ht_le_ki hleft
    apply listed_of_internal_cut (ki + 1) hki
    · omega
    · simpa [hkj_eq] using hkj
    · rw [hxt, ht_eq]
  · have hle_adj : ki ≤ kj + 1 := by
      apply le_of_not_gt
      intro hgap
      have hcut_lt :
          L[kj + 1]'hkj < L[ki]'(Nat.lt_of_succ_lt hki) := by
        exact (cutList_sorted e n).getElem_lt_getElem_of_lt (by
          simpa [L] using hgap)
      nlinarith
    have hki_eq : ki = kj + 1 := by omega
    have ht_eq : t = L[kj + 1]'hkj := by
      have hleft : L[kj + 1]'hkj ≤ t := by
        simpa [ki, kj, ii, jj, hki_eq] using hki_le_t
      have hright : t ≤ L[kj + 1]'hkj := by
        simpa [kj, jj] using hs_le_kj
      exact le_antisymm hright hleft
    apply listed_of_internal_cut (kj + 1) hkj
    · omega
    · simpa [hki_eq] using hki
    · rw [hxt, ht_eq]
