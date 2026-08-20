import ErdosProblems.Erdos733.ST.Preamble
import Mathlib.Tactic

open Classical
noncomputable section

-- [TABLET NODE: FinitePolygonalSetCyclicStreamPredecessorUnlistedInBlock]
lemma FinitePolygonalSetCyclicStreamPredecessorUnlistedInBlock
    {Point PieceIndex : Type} [DecidableEq PieceIndex]
    (points : Set Point)
    (successor : Equiv.Perm {p : Point // p ∈ points})
    (pieceSource : PieceIndex → Point)
    (arcPieceOrder : {p : Point // p ∈ points} → List PieceIndex)
    (pieceStream : List PieceIndex)
    (hpieceStream_nodup : pieceStream.Nodup)
    (horder_cases :
      ∀ p : {p : Point // p ∈ points},
        ((∃ (pre : List PieceIndex) (head : PieceIndex)
              (middle : List PieceIndex) (next : PieceIndex)
              (suffix : List PieceIndex),
            arcPieceOrder p = head :: middle ∧
              pieceStream =
                pre ++ arcPieceOrder p ++ (next :: suffix) ∧
              pieceSource head = p.1 ∧
              pieceSource next = (successor p).1 ∧
              ∀ i ∈ middle, pieceSource i ∉ points) ∨
          (∃ (pre : List PieceIndex) (next : PieceIndex)
              (middle : List PieceIndex) (head : PieceIndex)
              (suffix : List PieceIndex),
            arcPieceOrder p = head :: (suffix ++ pre) ∧
              pieceStream =
                pre ++ (next :: middle) ++ (head :: suffix) ∧
              pieceSource head = p.1 ∧
              pieceSource next = (successor p).1 ∧
              ∀ i ∈ suffix ++ pre, pieceSource i ∉ points)))
    (q : {p : Point // p ∈ points}) (i j : PieceIndex)
    (hj : j ∈ arcPieceOrder q)
    (hadj :
      (∃ (n : ℕ) (hn : n + 1 < pieceStream.length),
        pieceStream[n] = i ∧ pieceStream[n + 1] = j) ∨
      (pieceStream.getLast? = some i ∧ pieceStream.head? = some j))
    (hsource_unlisted : pieceSource j ∉ points) :
    i ∈ arcPieceOrder q := by
-- BODY
  classical
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
  have idx_bounds_of_mem_block :
      ∀ {x : PieceIndex} {pre block suffix : List PieceIndex},
        pieceStream = pre ++ block ++ suffix →
          x ∈ block →
            pre.length ≤ pieceStream.idxOf x ∧
              pieceStream.idxOf x < pre.length + block.length := by
    intro x pre block suffix hsplit hxblock
    have hxstream : x ∈ pieceStream := by
      rw [hsplit]
      simp [hxblock]
    constructor
    · apply le_of_not_gt
      intro hlt
      have hxpre : x ∈ pre :=
        mem_prefix_of_idx_lt (x := x) (pref := pre)
          (suffix := block ++ suffix) (by simpa [List.append_assoc] using hsplit) hlt
      have hnod : (pre ++ (block ++ suffix)).Nodup := by
        simpa [hsplit, List.append_assoc] using hpieceStream_nodup
      have hdisj := List.disjoint_of_nodup_append (l₁ := pre)
        (l₂ := block ++ suffix) hnod
      exact hdisj hxpre (by simp [hxblock])
    · apply lt_of_not_ge
      intro hge
      have hxsuf : x ∈ suffix :=
        mem_suffix_of_idx_ge (x := x) (pref := pre ++ block)
          (suffix := suffix) (by simpa [List.append_assoc] using hsplit)
          hxstream (by simpa [List.length_append] using hge)
      have hnod : ((pre ++ block) ++ suffix).Nodup := by
        simpa [hsplit, List.append_assoc] using hpieceStream_nodup
      have hdisj := List.disjoint_of_nodup_append (l₁ := pre ++ block)
        (l₂ := suffix) hnod
      exact hdisj (by simp [hxblock]) hxsuf
  have idx_step :
      ∀ {i j : PieceIndex} {n : ℕ} (hn : n + 1 < pieceStream.length),
        pieceStream[n] = i → pieceStream[n + 1] = j →
          pieceStream.idxOf j = pieceStream.idxOf i + 1 := by
    intro i j n hn hi hj
    have hn0 : n < pieceStream.length := by omega
    have hi_idx : pieceStream.idxOf i = n := by
      simpa [hi] using hpieceStream_nodup.idxOf_getElem n hn0
    have hj_idx : pieceStream.idxOf j = n + 1 := by
      simpa [hj] using hpieceStream_nodup.idxOf_getElem (n + 1) hn
    omega
  have idx_head_zero :
      ∀ {j : PieceIndex}, pieceStream.head? = some j →
        pieceStream.idxOf j = 0 := by
    intro j hhead
    cases hs : pieceStream with
    | nil =>
        simp [hs] at hhead
    | cons a l =>
        simp [hs] at hhead
        subst a
        simp [hs]
  have predecessor_mem_cons_block :
      ∀ {pre tail suffix : List PieceIndex} {head i j : PieceIndex},
        pieceStream = pre ++ (head :: tail) ++ suffix →
          j ∈ tail →
            ((∃ (n : ℕ) (hn : n + 1 < pieceStream.length),
              pieceStream[n] = i ∧ pieceStream[n + 1] = j) ∨
            (pieceStream.getLast? = some i ∧ pieceStream.head? = some j)) →
              i ∈ head :: tail := by
    intro pre tail suffix head i j hsplit hjtail hadj'
    have hjblock : j ∈ head :: tail := by simp [hjtail]
    have hbounds :=
      idx_bounds_of_mem_block (x := j) (pre := pre) (block := head :: tail)
        (suffix := suffix) hsplit hjblock
    have hhead_mem_stream : head ∈ pieceStream := by
      rw [hsplit]
      simp
    have hj_mem_stream : j ∈ pieceStream := by
      rw [hsplit]
      simp [hjtail]
    have hidx_head : pieceStream.idxOf head = pre.length := by
      have hsplit_head :
          pieceStream = pre ++ head :: (tail ++ suffix) := by
        rw [hsplit]
        simp [List.append_assoc]
      have hpos : pre.length < pieceStream.length := by
        rw [hsplit_head]
        simp
      have hidx := hpieceStream_nodup.idxOf_getElem pre.length hpos
      simpa [hsplit_head] using hidx
    have hj_ne_head : j ≠ head := by
      intro hEq
      subst j
      have htail_stream : head ∈ tail := hjtail
      have hnod : (pre ++ (head :: tail) ++ suffix).Nodup := by
        simpa [hsplit] using hpieceStream_nodup
      have hnod_block : (head :: tail).Nodup :=
        hnod.of_append_left.of_append_right
      exact hnod_block.notMem htail_stream
    have hpre_lt_idx_j : pre.length < pieceStream.idxOf j := by
      have hne : pieceStream.idxOf j ≠ pre.length := by
        intro hidxj
        have hidx_eq : pieceStream.idxOf j = pieceStream.idxOf head := by
          simpa [hidx_head] using hidxj
        have hEq : j = head :=
          (List.idxOf_inj (l := pieceStream) hj_mem_stream).1 hidx_eq
        exact hj_ne_head hEq
      omega
    rcases hadj' with hstep | hcyclic
    · rcases hstep with ⟨n, hn, hi_get, hj_get⟩
      have hi_mem_stream : i ∈ pieceStream :=
        by simpa [hi_get] using
          (List.getElem_mem (l := pieceStream) (n := n) (by omega))
      have hidx_rel := idx_step hn hi_get hj_get
      apply mem_block_of_idx_between (x := i) (pre := pre)
        (block := head :: tail) (suffix := suffix) hsplit hi_mem_stream
      · omega
      · omega
    · have hidx_j_zero : pieceStream.idxOf j = 0 := idx_head_zero hcyclic.2
      omega
  rcases horder_cases q with hcase | hcase
  · rcases hcase with
      ⟨pre, head, middle, next, suffix, horder, hstream,
        hhead_source, _hnext_source, _hmiddle⟩
    have hj_middle : j ∈ middle := by
      have hj' : j = head ∨ j ∈ middle := by
        simpa [horder] using hj
      rcases hj' with rfl | hjmid
      · exact False.elim (hsource_unlisted (by simpa [hhead_source] using q.2))
      · exact hjmid
    have hi_block :
        i ∈ head :: middle :=
      predecessor_mem_cons_block
        (pre := pre) (head := head) (tail := middle)
        (suffix := next :: suffix) (i := i) (j := j)
        (by simpa [horder, List.append_assoc] using hstream)
        hj_middle hadj
    simpa [horder] using hi_block
  · rcases hcase with
      ⟨pre, next, middle, head, suffix, horder, hstream,
        hhead_source, _hnext_source, _hmiddle⟩
    have hj_tail : j ∈ suffix ++ pre := by
      have hj' : j = head ∨ j ∈ suffix ++ pre := by
        simpa [horder] using hj
      rcases hj' with rfl | hjtail
      · exact False.elim (hsource_unlisted (by simpa [hhead_source] using q.2))
      · exact hjtail
    rcases (List.mem_append.mp hj_tail) with hj_suffix | hj_pre
    · have hi_block :
          i ∈ head :: suffix :=
        predecessor_mem_cons_block
          (pre := pre ++ (next :: middle)) (head := head) (tail := suffix)
          (suffix := []) (i := i) (j := j)
          (by
            rw [hstream]
            simp [List.append_assoc])
          hj_suffix hadj
      have hi_block_or : i = head ∨ i ∈ suffix := by
        simpa using hi_block
      rcases hi_block_or with hi_eq | hi_suffix
      ·
          rw [← hi_eq] at horder
          simpa [horder]
      ·
          simp [horder, hi_suffix]
    · rcases hadj with hstep | hcyclic
      · rcases hstep with ⟨n, hn, hi_get, hj_get⟩
        have hi_mem_stream : i ∈ pieceStream :=
          by simpa [hi_get] using
            (List.getElem_mem (l := pieceStream) (n := n) (by omega))
        have hj_mem_stream : j ∈ pieceStream :=
          by simpa [hj_get] using
            (List.getElem_mem (l := pieceStream) (n := n + 1) hn)
        have hidx_rel := idx_step hn hi_get hj_get
        have hbounds_pre :
            0 ≤ pieceStream.idxOf j ∧
              pieceStream.idxOf j < pre.length := by
          have hsplit_pre :
              pieceStream = [] ++ pre ++ ((next :: middle) ++ (head :: suffix)) := by
            rw [hstream]
            simp [List.append_assoc]
          simpa using
            (idx_bounds_of_mem_block (x := j) (pre := [])
              (block := pre) (suffix := (next :: middle) ++ (head :: suffix))
              hsplit_pre hj_pre)
        have hidx_j_pos : 0 < pieceStream.idxOf j := by
          have hidx_j_zero_or := Nat.eq_zero_or_pos (pieceStream.idxOf j)
          rcases hidx_j_zero_or with hzero | hpos
          · have hidx_i : pieceStream.idxOf i + 1 = 0 := by omega
            omega
          · exact hpos
        have hi_in_pre : i ∈ pre := by
          apply mem_block_of_idx_between (x := i) (pre := [])
            (block := pre) (suffix := (next :: middle) ++ (head :: suffix))
          · rw [hstream]
            simp [List.append_assoc]
          · exact hi_mem_stream
          · simp
          · omega
        simpa [horder, hi_in_pre]
      · have hlast_mem : i ∈ head :: suffix := by
          have hstream_last :
              pieceStream =
                (pre ++ (next :: middle)) ++ (head :: suffix) := by
            rw [hstream]
          have hlast_some : (head :: suffix).getLast? = some i := by
            have hlast_piece :
                pieceStream.getLast? =
                  (head :: suffix).getLast? := by
              rw [hstream_last, List.getLast?_append_of_ne_nil]
              simp
            simpa [hlast_piece] using hcyclic.1
          have hi_mem_option : i ∈ (head :: suffix).getLast? := by
            simpa [hlast_some]
          rcases List.mem_getLast?_eq_getLast hi_mem_option with ⟨h, hi_eq⟩
          rw [hi_eq]
          exact List.getLast_mem h
        have hlast_or : i = head ∨ i ∈ suffix := by
          simpa using hlast_mem
        rcases hlast_or with hi_eq | hi_suffix
        ·
            rw [← hi_eq] at horder
            simpa [horder]
        ·
            simp [horder, hi_suffix]
