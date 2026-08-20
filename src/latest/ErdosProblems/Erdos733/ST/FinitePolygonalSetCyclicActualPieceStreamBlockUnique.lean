import ErdosProblems.Erdos733.ST.FinitePolygonalSetCyclicActualPieceStreamCases
import Mathlib.Tactic

open Classical
noncomputable section

-- [TABLET NODE: FinitePolygonalSetCyclicActualPieceStreamBlockUnique]
lemma FinitePolygonalSetCyclicActualPieceStreamBlockUnique
    (K : FinitePolygonalSet)
    {PieceIndex : Type}
    (successor : Equiv.Perm {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points})
    (pieceSource : PieceIndex → EuclideanSpace ℝ (Fin 2))
    (arcPieceOrder :
      {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points} → List PieceIndex)
    (pieceStream : List PieceIndex)
    (hpieceStream_nodup : pieceStream.Nodup)
    (hsource_listed_eq_start :
      ∀ (p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points})
        (i : PieceIndex), i ∈ arcPieceOrder p → pieceSource i ∈ K.points →
          pieceSource i = p.1)
    (horder_cases :
      ∀ p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points},
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
              ∀ i ∈ suffix ++ pre, pieceSource i ∉ K.points))) :
    ∀ p q : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points},
      ∀ i : PieceIndex, i ∈ arcPieceOrder p → i ∈ arcPieceOrder q →
        p = q := by
-- BODY
  classical
  have idx_at_cons :
      ∀ {a : PieceIndex} {pre post : List PieceIndex},
        pieceStream = pre ++ a :: post →
          pieceStream.idxOf a = pre.length := by
    intro a pre post hsplit
    have hpos : pre.length < pieceStream.length := by
      rw [hsplit]
      simp
    have hidx := List.Nodup.idxOf_getElem hpieceStream_nodup pre.length hpos
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
  have idx_between_of_mem_block :
      ∀ {x : PieceIndex} {pre block suffix : List PieceIndex},
        pieceStream = pre ++ block ++ suffix →
          x ∈ block →
            pre.length ≤ pieceStream.idxOf x ∧
              pieceStream.idxOf x < pre.length + block.length := by
    intro x pre block suffix hsplit hxblock
    constructor
    · apply le_of_not_gt
      intro hlt
      have hxpre : x ∈ pre :=
        mem_prefix_of_idx_lt (x := x) (pref := pre)
          (suffix := block ++ suffix)
          (by simpa [List.append_assoc] using hsplit) hlt
      have hnod : (pre ++ (block ++ suffix)).Nodup := by
        simpa [hsplit, List.append_assoc] using hpieceStream_nodup
      have hdisj := List.disjoint_of_nodup_append hnod
      exact hdisj hxpre (by simp [hxblock])
    · have hpref : pre ++ block <+: pieceStream := by
        rw [hsplit]
        exact ⟨suffix, by simp [List.append_assoc]⟩
      have hmem_pref : x ∈ pre ++ block := by simp [hxblock]
      have hlt := (hpref.mem_iff_idxOf_lt_length x).1 hmem_pref
      simpa [List.length_append] using hlt
  have idx_wrap_of_mem :
      ∀ {x head next : PieceIndex}
        {pre middle suffix : List PieceIndex},
        pieceStream = pre ++ (next :: middle) ++ (head :: suffix) →
          x ∈ head :: (suffix ++ pre) →
            (pre ++ (next :: middle)).length ≤ pieceStream.idxOf x ∨
              pieceStream.idxOf x < pre.length := by
    intro x head next pre middle suffix hstream hxblock
    have hxsplit : x ∈ head :: suffix ∨ x ∈ pre := by
      simpa [List.mem_append, or_assoc] using hxblock
    rcases hxsplit with hx_tail | hxpre
    · left
      apply le_of_not_gt
      intro hlt
      have hxpref : x ∈ pre ++ (next :: middle) :=
        mem_prefix_of_idx_lt (x := x) (pref := pre ++ (next :: middle))
          (suffix := head :: suffix) hstream hlt
      have hnod : ((pre ++ (next :: middle)) ++ (head :: suffix)).Nodup := by
        simpa [hstream, List.append_assoc] using hpieceStream_nodup
      have hdisj := List.disjoint_of_nodup_append hnod
      exact hdisj hxpref hx_tail
    · right
      have hpref : pre <+: pieceStream := by
        rw [hstream]
        exact ⟨(next :: middle) ++ (head :: suffix),
          by simp [List.append_assoc]⟩
      exact (hpref.mem_iff_idxOf_lt_length x).1 hxpre
  have mem_wrap_of_idx :
      ∀ {x head next : PieceIndex}
        {pre middle suffix : List PieceIndex},
        pieceStream = pre ++ (next :: middle) ++ (head :: suffix) →
          x ∈ pieceStream →
            ((pre ++ (next :: middle)).length ≤ pieceStream.idxOf x ∨
              pieceStream.idxOf x < pre.length) →
              x ∈ head :: (suffix ++ pre) := by
    intro x head next pre middle suffix hstream hxstream hidx
    rcases hidx with hhigh | hlow
    · have hx_tail : x ∈ head :: suffix :=
        mem_suffix_of_idx_ge (x := x) (pref := pre ++ (next :: middle))
          (suffix := head :: suffix) hstream hxstream hhigh
      simpa [List.cons_append] using
        (List.mem_append_left pre hx_tail)
    · have hxpre : x ∈ pre :=
        mem_prefix_of_idx_lt (x := x) (pref := pre)
          (suffix := (next :: middle) ++ (head :: suffix))
          (by simpa [List.append_assoc] using hstream) hlow
      exact List.mem_cons_of_mem head (List.mem_append_right suffix hxpre)
  intro p q i hip hiq
  by_contra hpq
  rcases horder_cases p with hp_case | hp_case <;>
    rcases horder_cases q with hq_case | hq_case
  · rcases hp_case with
      ⟨preP, headP, middleP, nextP, suffixP, hp_order, hp_stream,
        hheadP_source, _hnextP_source, _hmiddleP⟩
    rcases hq_case with
      ⟨preQ, headQ, middleQ, nextQ, suffixQ, hq_order, hq_stream,
        hheadQ_source, _hnextQ_source, _hmiddleQ⟩
    let blockP : List PieceIndex := arcPieceOrder p
    let blockQ : List PieceIndex := arcPieceOrder q
    have hPsplit : pieceStream = preP ++ blockP ++ (nextP :: suffixP) := by
      simpa [blockP] using hp_stream
    have hQsplit : pieceStream = preQ ++ blockQ ++ (nextQ :: suffixQ) := by
      simpa [blockQ] using hq_stream
    have hPmem := idx_between_of_mem_block (x := i) hPsplit
      (by simpa [blockP] using hip)
    have hQmem := idx_between_of_mem_block (x := i) hQsplit
      (by simpa [blockQ] using hiq)
    have hHq_not_in_P :
        ¬ (preP.length ≤ pieceStream.idxOf headQ ∧
            pieceStream.idxOf headQ < preP.length + blockP.length) := by
      rintro ⟨hlo, hhi⟩
      have hheadQ_stream : headQ ∈ pieceStream := by
        rw [hq_stream, hq_order]
        simp
      have hheadQ_memP : headQ ∈ arcPieceOrder p := by
        simpa [blockP] using
          mem_block_of_idx_between (x := headQ) hPsplit hheadQ_stream hlo hhi
      have hlistedQ : pieceSource headQ ∈ K.points := by
        simp [hheadQ_source]
      have hsourceP := hsource_listed_eq_start p headQ hheadQ_memP hlistedQ
      exact hpq (Subtype.ext (hsourceP.symm.trans hheadQ_source))
    have hHp_not_in_Q :
        ¬ (preQ.length ≤ pieceStream.idxOf headP ∧
            pieceStream.idxOf headP < preQ.length + blockQ.length) := by
      rintro ⟨hlo, hhi⟩
      have hheadP_stream : headP ∈ pieceStream := by
        rw [hp_stream, hp_order]
        simp
      have hheadP_memQ : headP ∈ arcPieceOrder q := by
        simpa [blockQ] using
          mem_block_of_idx_between (x := headP) hQsplit hheadP_stream hlo hhi
      have hlistedP : pieceSource headP ∈ K.points := by
        simp [hheadP_source]
      have hsourceQ := hsource_listed_eq_start q headP hheadP_memQ hlistedP
      exact hpq (Subtype.ext (hheadP_source.symm.trans hsourceQ))
    have hidx_headP :
        pieceStream.idxOf headP = preP.length := by
      have hs : pieceStream = preP ++ headP :: (middleP ++ nextP :: suffixP) := by
        rw [hp_stream, hp_order]
        simp [List.append_assoc]
      exact idx_at_cons hs
    have hidx_headQ :
        pieceStream.idxOf headQ = preQ.length := by
      have hs : pieceStream = preQ ++ headQ :: (middleQ ++ nextQ :: suffixQ) := by
        rw [hq_stream, hq_order]
        simp [List.append_assoc]
      exact idx_at_cons hs
    by_cases hle : preP.length ≤ preQ.length
    · have hnot : preP.length + blockP.length ≤ preQ.length := by
        apply le_of_not_gt
        intro hlt
        apply hHq_not_in_P
        constructor
        · simpa [hidx_headQ] using hle
        · simpa [hidx_headQ, blockP] using hlt
      omega
    · have hlt : preQ.length < preP.length := by omega
      have hnot : preQ.length + blockQ.length ≤ preP.length := by
        apply le_of_not_gt
        intro hlt2
        apply hHp_not_in_Q
        constructor
        · simpa [hidx_headP] using (le_of_lt hlt)
        · simpa [hidx_headP, blockQ] using hlt2
      omega
  · rcases hp_case with
      ⟨preP, headP, middleP, nextP, suffixP, hp_order, hp_stream,
        hheadP_source, _hnextP_source, _hmiddleP⟩
    rcases hq_case with
      ⟨preQ, nextQ, middleQ, headQ, suffixQ, hq_order, hq_stream,
        hheadQ_source, _hnextQ_source, _hmiddleQ⟩
    let blockP : List PieceIndex := arcPieceOrder p
    let Hq : ℕ := (preQ ++ (nextQ :: middleQ)).length
    let Nq : ℕ := preQ.length
    have hPsplit : pieceStream = preP ++ blockP ++ (nextP :: suffixP) := by
      simpa [blockP] using hp_stream
    have hPmem := idx_between_of_mem_block (x := i) hPsplit
      (by simpa [blockP] using hip)
    have hQmem :
        Hq ≤ pieceStream.idxOf i ∨ pieceStream.idxOf i < Nq := by
      have hmem : i ∈ headQ :: (suffixQ ++ preQ) := by
        simpa [hq_order] using hiq
      simpa [Hq, Nq] using idx_wrap_of_mem (x := i) hq_stream hmem
    have hHq_not_in_P :
        ¬ (preP.length ≤ Hq ∧ Hq < preP.length + blockP.length) := by
      rintro ⟨hlo, hhi⟩
      have hheadQ_stream : headQ ∈ pieceStream := by
        rw [hq_stream]
        simp
      have hidx_headQ : pieceStream.idxOf headQ = Hq := by
        have hs : pieceStream =
            (preQ ++ (nextQ :: middleQ)) ++ headQ :: suffixQ := by
          rw [hq_stream]
        simpa [Hq] using idx_at_cons hs
      have hheadQ_memP : headQ ∈ arcPieceOrder p := by
        have hlo' : preP.length ≤ pieceStream.idxOf headQ := by
          simpa [hidx_headQ] using hlo
        have hhi' : pieceStream.idxOf headQ < preP.length + blockP.length := by
          simpa [hidx_headQ] using hhi
        simpa [blockP] using
          mem_block_of_idx_between (x := headQ) hPsplit hheadQ_stream hlo' hhi'
      have hlistedQ : pieceSource headQ ∈ K.points := by
        simp [hheadQ_source]
      have hsourceP := hsource_listed_eq_start p headQ hheadQ_memP hlistedQ
      exact hpq (Subtype.ext (hsourceP.symm.trans hheadQ_source))
    have hHp_not_in_Q :
        ¬ (Hq ≤ pieceStream.idxOf headP ∨ pieceStream.idxOf headP < Nq) := by
      intro hidx
      have hheadP_stream : headP ∈ pieceStream := by
        rw [hp_stream, hp_order]
        simp
      have hheadP_memQ : headP ∈ arcPieceOrder q := by
        have hmem := mem_wrap_of_idx (x := headP) hq_stream hheadP_stream
          (by simpa [Hq, Nq] using hidx)
        simpa [hq_order] using hmem
      have hlistedP : pieceSource headP ∈ K.points := by
        simp [hheadP_source]
      have hsourceQ := hsource_listed_eq_start q headP hheadP_memQ hlistedP
      exact hpq (Subtype.ext (hheadP_source.symm.trans hsourceQ))
    have hidx_headP :
        pieceStream.idxOf headP = preP.length := by
      have hs : pieceStream = preP ++ headP :: (middleP ++ nextP :: suffixP) := by
        rw [hp_stream, hp_order]
        simp [List.append_assoc]
      exact idx_at_cons hs
    rcases hQmem with hQhigh | hQlow
    · by_cases hle : preP.length ≤ Hq
      · have hnot : preP.length + blockP.length ≤ Hq := by
          apply le_of_not_gt
          intro hlt
          exact hHq_not_in_P ⟨hle, hlt⟩
        omega
      · have hltH : Hq < preP.length := by omega
        have hHpQ : Hq ≤ pieceStream.idxOf headP ∨ pieceStream.idxOf headP < Nq := by
          left
          simpa [hidx_headP] using le_of_lt hltH
        exact False.elim (hHp_not_in_Q hHpQ)
    · have hHpQ : Hq ≤ pieceStream.idxOf headP ∨ pieceStream.idxOf headP < Nq := by
        right
        have : pieceStream.idxOf i < Nq := hQlow
        omega
      exact False.elim (hHp_not_in_Q hHpQ)
  · rcases hp_case with
      ⟨preP, nextP, middleP, headP, suffixP, hp_order, hp_stream,
        hheadP_source, _hnextP_source, _hmiddleP⟩
    rcases hq_case with
      ⟨preQ, headQ, middleQ, nextQ, suffixQ, hq_order, hq_stream,
        hheadQ_source, _hnextQ_source, _hmiddleQ⟩
    let Hp : ℕ := (preP ++ (nextP :: middleP)).length
    let Np : ℕ := preP.length
    let blockQ : List PieceIndex := arcPieceOrder q
    have hQsplit : pieceStream = preQ ++ blockQ ++ (nextQ :: suffixQ) := by
      simpa [blockQ] using hq_stream
    have hPmem :
        Hp ≤ pieceStream.idxOf i ∨ pieceStream.idxOf i < Np := by
      have hmem : i ∈ headP :: (suffixP ++ preP) := by
        simpa [hp_order] using hip
      simpa [Hp, Np] using idx_wrap_of_mem (x := i) hp_stream hmem
    have hQmem := idx_between_of_mem_block (x := i) hQsplit
      (by simpa [blockQ] using hiq)
    have hHq_not_in_P :
        ¬ (Hp ≤ pieceStream.idxOf headQ ∨ pieceStream.idxOf headQ < Np) := by
      intro hidx
      have hheadQ_stream : headQ ∈ pieceStream := by
        rw [hq_stream, hq_order]
        simp
      have hheadQ_memP : headQ ∈ arcPieceOrder p := by
        have hmem := mem_wrap_of_idx (x := headQ) hp_stream hheadQ_stream
          (by simpa [Hp, Np] using hidx)
        simpa [hp_order] using hmem
      have hlistedQ : pieceSource headQ ∈ K.points := by
        simp [hheadQ_source]
      have hsourceP := hsource_listed_eq_start p headQ hheadQ_memP hlistedQ
      exact hpq (Subtype.ext (hsourceP.symm.trans hheadQ_source))
    have hHp_not_in_Q :
        ¬ (preQ.length ≤ Hp ∧ Hp < preQ.length + blockQ.length) := by
      rintro ⟨hlo, hhi⟩
      have hheadP_stream : headP ∈ pieceStream := by
        rw [hp_stream]
        simp
      have hidx_headP : pieceStream.idxOf headP = Hp := by
        have hs : pieceStream =
            (preP ++ (nextP :: middleP)) ++ headP :: suffixP := by
          rw [hp_stream]
        simpa [Hp] using idx_at_cons hs
      have hheadP_memQ : headP ∈ arcPieceOrder q := by
        have hlo' : preQ.length ≤ pieceStream.idxOf headP := by
          simpa [hidx_headP] using hlo
        have hhi' : pieceStream.idxOf headP < preQ.length + blockQ.length := by
          simpa [hidx_headP] using hhi
        simpa [blockQ] using
          mem_block_of_idx_between (x := headP) hQsplit hheadP_stream hlo' hhi'
      have hlistedP : pieceSource headP ∈ K.points := by
        simp [hheadP_source]
      have hsourceQ := hsource_listed_eq_start q headP hheadP_memQ hlistedP
      exact hpq (Subtype.ext (hheadP_source.symm.trans hsourceQ))
    have hidx_headQ :
        pieceStream.idxOf headQ = preQ.length := by
      have hs : pieceStream = preQ ++ headQ :: (middleQ ++ nextQ :: suffixQ) := by
        rw [hq_stream, hq_order]
        simp [List.append_assoc]
      exact idx_at_cons hs
    rcases hPmem with hPhigh | hPlow
    · have hHqP : Hp ≤ pieceStream.idxOf headQ ∨ pieceStream.idxOf headQ < Np := by
        left
        have : Hp ≤ pieceStream.idxOf i := hPhigh
        omega
      exact False.elim (hHq_not_in_P hHqP)
    · by_cases hle : preQ.length ≤ Hp
      · have hnot : preQ.length + blockQ.length ≤ Hp := by
          apply le_of_not_gt
          intro hlt
          exact hHp_not_in_Q ⟨hle, hlt⟩
        omega
      · have hlt : Hp < preQ.length := by omega
        have hHqP : Hp ≤ pieceStream.idxOf headQ ∨ pieceStream.idxOf headQ < Np := by
          right
          have hpreQ_lt_Np : preQ.length < Np :=
            lt_of_le_of_lt hQmem.1 hPlow
          simpa [hidx_headQ] using hpreQ_lt_Np
        exact False.elim (hHq_not_in_P hHqP)
  · rcases hp_case with
      ⟨preP, nextP, middleP, headP, suffixP, hp_order, hp_stream,
        hheadP_source, _hnextP_source, _hmiddleP⟩
    rcases hq_case with
      ⟨preQ, nextQ, middleQ, headQ, suffixQ, hq_order, hq_stream,
        hheadQ_source, _hnextQ_source, _hmiddleQ⟩
    let Hp : ℕ := (preP ++ (nextP :: middleP)).length
    let Np : ℕ := preP.length
    let Hq : ℕ := (preQ ++ (nextQ :: middleQ)).length
    let Nq : ℕ := preQ.length
    have hPmem :
        Hp ≤ pieceStream.idxOf i ∨ pieceStream.idxOf i < Np := by
      have hmem : i ∈ headP :: (suffixP ++ preP) := by
        simpa [hp_order] using hip
      simpa [Hp, Np] using idx_wrap_of_mem (x := i) hp_stream hmem
    have hQmem :
        Hq ≤ pieceStream.idxOf i ∨ pieceStream.idxOf i < Nq := by
      have hmem : i ∈ headQ :: (suffixQ ++ preQ) := by
        simpa [hq_order] using hiq
      simpa [Hq, Nq] using idx_wrap_of_mem (x := i) hq_stream hmem
    have hHq_not_in_P :
        ¬ (Hp ≤ pieceStream.idxOf headQ ∨ pieceStream.idxOf headQ < Np) := by
      intro hidx
      have hheadQ_stream : headQ ∈ pieceStream := by
        rw [hq_stream]
        simp
      have hheadQ_memP : headQ ∈ arcPieceOrder p := by
        have hmem := mem_wrap_of_idx (x := headQ) hp_stream hheadQ_stream
          (by simpa [Hp, Np] using hidx)
        simpa [hp_order] using hmem
      have hlistedQ : pieceSource headQ ∈ K.points := by
        simp [hheadQ_source]
      have hsourceP := hsource_listed_eq_start p headQ hheadQ_memP hlistedQ
      exact hpq (Subtype.ext (hsourceP.symm.trans hheadQ_source))
    have hHp_not_in_Q :
        ¬ (Hq ≤ pieceStream.idxOf headP ∨ pieceStream.idxOf headP < Nq) := by
      intro hidx
      have hheadP_stream : headP ∈ pieceStream := by
        rw [hp_stream]
        simp
      have hheadP_memQ : headP ∈ arcPieceOrder q := by
        have hmem := mem_wrap_of_idx (x := headP) hq_stream hheadP_stream
          (by simpa [Hq, Nq] using hidx)
        simpa [hq_order] using hmem
      have hlistedP : pieceSource headP ∈ K.points := by
        simp [hheadP_source]
      have hsourceQ := hsource_listed_eq_start q headP hheadP_memQ hlistedP
      exact hpq (Subtype.ext (hheadP_source.symm.trans hsourceQ))
    have hidx_headP : pieceStream.idxOf headP = Hp := by
      have hs : pieceStream =
          (preP ++ (nextP :: middleP)) ++ headP :: suffixP := by
        rw [hp_stream]
      simpa [Hp] using idx_at_cons hs
    have hidx_headQ : pieceStream.idxOf headQ = Hq := by
      have hs : pieceStream =
          (preQ ++ (nextQ :: middleQ)) ++ headQ :: suffixQ := by
        rw [hq_stream]
      simpa [Hq] using idx_at_cons hs
    by_cases hle : Hp ≤ Hq
    · have hbad : Hp ≤ pieceStream.idxOf headQ ∨ pieceStream.idxOf headQ < Np := by
        left
        simpa [hidx_headQ] using hle
      exact False.elim (hHq_not_in_P hbad)
    · have hbad : Hq ≤ pieceStream.idxOf headP ∨ pieceStream.idxOf headP < Nq := by
        left
        simpa [hidx_headP] using le_of_not_ge hle
      exact False.elim (hHp_not_in_Q hbad)
