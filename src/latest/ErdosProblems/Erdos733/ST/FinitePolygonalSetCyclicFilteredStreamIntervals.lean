import ErdosProblems.Erdos733.ST.Preamble
import Mathlib.Data.List.ReduceOption
import Mathlib.Data.List.Cycle
import Mathlib.Tactic

open Classical
noncomputable section

-- [TABLET NODE: FinitePolygonalSetCyclicFilteredStreamIntervals]
lemma FinitePolygonalSetCyclicFilteredStreamIntervals
    {ι α : Type*} [DecidableEq α]
    (stream : List ι) (retain : ι → Option α) (retained : List α)
    (hretained : retained = stream.filterMap retain)
    (hretained_nodup : retained.Nodup)
    (hretained_two : 2 ≤ retained.length) :
    ∀ p : α, p ∈ retained →
      retained.formPerm p ≠ p ∧
        ((∃ (pre : List ι) (head : ι) (middle : List ι) (next : ι)
              (suffix : List ι),
            stream = pre ++ (head :: middle) ++ (next :: suffix) ∧
            retain head = some p ∧
            retain next = some (retained.formPerm p) ∧
            ∀ x ∈ middle, retain x = none) ∨
          (∃ (pre : List ι) (next : ι) (middle : List ι) (head : ι)
              (suffix : List ι),
            stream = pre ++ (next :: middle) ++ (head :: suffix) ∧
            retain head = some p ∧
            retain next = some (retained.formPerm p) ∧
            ∀ x ∈ suffix ++ pre, retain x = none)) := by
-- BODY
  intro p hp
  have hfilter : stream.filterMap retain = retained := hretained.symm
  obtain ⟨k, hk, hkp⟩ := List.getElem_of_mem hp
  have hmove : retained.formPerm p ≠ p := by
    exact
      (List.formPerm_apply_mem_ne_self_iff retained hretained_nodup p hp).2
        hretained_two
  refine ⟨hmove, ?_⟩
  have hlen_pos : 0 < retained.length := by omega
  have hform_idx :
      retained.formPerm p =
        retained[(k + 1) % retained.length]'(Nat.mod_lt _ hlen_pos) := by
    rw [← hkp]
    exact List.formPerm_apply_getElem retained hretained_nodup k hk
  by_cases hk1 : k + 1 < retained.length
  · left
    have hmod : (k + 1) % retained.length = k + 1 :=
      Nat.mod_eq_of_lt hk1
    have hform_next : retained.formPerm p = retained[k + 1] := by
      simpa [hmod] using hform_idx
    have hprefix_eq :
        stream.filterMap retain =
          retained.take (k + 1) ++ retained.drop (k + 1) := by
      rw [hfilter, List.take_append_drop]
    rcases
        (List.filterMap_eq_append_iff (l := stream)
          (L₁ := retained.take (k + 1)) (L₂ := retained.drop (k + 1))
          (f := retain)).1 hprefix_eq with
      ⟨sBeforeSucc, sFromSucc, hstream_split, hbefore_filter, hfrom_filter⟩
    have htake_succ : retained.take (k + 1) = retained.take k ++ [p] := by
      rw [← List.take_concat_get' retained k hk, hkp]
    have hbefore_filter' :
        sBeforeSucc.filterMap retain = retained.take k ++ [p] := by
      simpa [htake_succ] using hbefore_filter
    rcases
        (List.filterMap_eq_append_iff (l := sBeforeSucc)
          (L₁ := retained.take k) (L₂ := [p]) (f := retain)).1
          hbefore_filter' with
      ⟨sPreP, sPChunk, hbefore_split, _hpre_filter, hpchunk_filter⟩
    rcases
        (List.filterMap_eq_cons_iff (f := retain) (l := sPChunk) (b := p)
          (bs := [])).1 hpchunk_filter with
      ⟨noneBeforeP, headP, noneAfterP, hpchunk_eq, _hnoneBeforeP, hheadP,
        hnoneAfterP_filter⟩
    have hnoneAfterP : ∀ x ∈ noneAfterP, retain x = none := by
      exact
        (List.filterMap_eq_nil_iff (f := retain) (l := noneAfterP)).1
          hnoneAfterP_filter
    have hdrop_succ :
        retained.drop (k + 1) = retained[k + 1] :: retained.drop (k + 2) := by
      exact List.drop_eq_getElem_cons hk1
    have hfrom_filter' :
        sFromSucc.filterMap retain =
          retained[k + 1] :: retained.drop (k + 2) := by
      rw [hdrop_succ] at hfrom_filter
      exact hfrom_filter
    rcases
        (List.filterMap_eq_cons_iff (f := retain) (l := sFromSucc)
          (b := retained[k + 1]) (bs := retained.drop (k + 2))).1
          hfrom_filter' with
      ⟨noneBeforeSucc, headSucc, afterSucc, hfrom_eq, hnoneBeforeSucc,
        hheadSucc, _hafter_filter⟩
    refine
      ⟨sPreP ++ noneBeforeP, headP, noneAfterP ++ noneBeforeSucc, headSucc,
        afterSucc, ?_, ?_, ?_, ?_⟩
    · calc
        stream = sBeforeSucc ++ sFromSucc := hstream_split
        _ = (sPreP ++ sPChunk) ++ sFromSucc := by rw [hbefore_split]
        _ = (sPreP ++ (noneBeforeP ++ headP :: noneAfterP)) ++
              (noneBeforeSucc ++ headSucc :: afterSucc) := by
            rw [hpchunk_eq, hfrom_eq]
        _ = (sPreP ++ noneBeforeP) ++ (headP :: noneAfterP ++ noneBeforeSucc) ++
              (headSucc :: afterSucc) := by
            simp only [List.append_assoc, List.cons_append]
    · exact hheadP
    · simpa [hform_next] using hheadSucc
    · intro x hx
      rw [List.mem_append] at hx
      rcases hx with hx | hx
      · exact hnoneAfterP x hx
      · exact hnoneBeforeSucc x hx
  · right
    have hk_last : k + 1 = retained.length := by omega
    have hmod : (k + 1) % retained.length = 0 := by
      rw [hk_last, Nat.mod_self]
    have hform_first : retained.formPerm p = retained[0] := by
      simpa [hmod] using hform_idx
    have htake_all : retained.take (k + 1) = retained := by
      rw [hk_last, List.take_length]
    have hretained_split_p : retained = retained.take k ++ [p] := by
      calc
        retained = retained.take (k + 1) := htake_all.symm
        _ = retained.take k ++ [p] := by
          rw [← List.take_concat_get' retained k hk, hkp]
    have hsplit_p : stream.filterMap retain = retained.take k ++ [p] := by
      exact hfilter.trans hretained_split_p
    rcases
        (List.filterMap_eq_append_iff (l := stream) (L₁ := retained.take k)
          (L₂ := [p]) (f := retain)).1 hsplit_p with
      ⟨sBeforeP, sPChunk, hstream_split, hbeforeP_filter, hpchunk_filter⟩
    rcases
        (List.filterMap_eq_cons_iff (f := retain) (l := sPChunk) (b := p)
          (bs := [])).1 hpchunk_filter with
      ⟨noneBeforeP, headP, noneAfterP, hpchunk_eq, _hnoneBeforeP, hheadP,
        hnoneAfterP_filter⟩
    have hnoneAfterP : ∀ x ∈ noneAfterP, retain x = none := by
      exact
        (List.filterMap_eq_nil_iff (f := retain) (l := noneAfterP)).1
          hnoneAfterP_filter
    have hk_pos : 0 < k := by omega
    have htake_nonempty : retained.take k ≠ [] := by
      have hlen_take : 0 < (retained.take k).length := by
        rw [List.length_take]
        omega
      exact List.ne_nil_of_length_pos hlen_take
    have htake_cons : retained.take k = retained[0] :: (retained.take k).tail := by
      calc
        retained.take k =
            (retained.take k).head htake_nonempty :: (retained.take k).tail :=
          (List.cons_head_tail htake_nonempty).symm
        _ = retained[0] :: (retained.take k).tail := by
          congr
          rw [List.head_eq_getElem htake_nonempty]
          exact List.getElem_take
    have hbeforeP_filter' :
        sBeforeP.filterMap retain = retained[0] :: (retained.take k).tail := by
      rw [htake_cons] at hbeforeP_filter
      exact hbeforeP_filter
    rcases
        (List.filterMap_eq_cons_iff (f := retain) (l := sBeforeP)
          (b := retained[0]) (bs := (retained.take k).tail)).1
          hbeforeP_filter' with
      ⟨prefixNone, headSucc, middleBeforeP, hbeforeP_eq, hprefixNone,
        hheadSucc, _hmiddle_filter⟩
    refine
      ⟨prefixNone, headSucc, middleBeforeP ++ noneBeforeP, headP, noneAfterP,
        ?_, ?_, ?_, ?_⟩
    · calc
        stream = sBeforeP ++ sPChunk := hstream_split
        _ = (prefixNone ++ headSucc :: middleBeforeP) ++
              (noneBeforeP ++ headP :: noneAfterP) := by
            rw [hbeforeP_eq, hpchunk_eq]
        _ = prefixNone ++ (headSucc :: middleBeforeP ++ noneBeforeP) ++
              (headP :: noneAfterP) := by
            simp only [List.append_assoc, List.cons_append]
    · exact hheadP
    · simpa [hform_first] using hheadSucc
    · intro x hx
      rw [List.mem_append] at hx
      rcases hx with hx | hx
      · exact hnoneAfterP x hx
      · exact hprefixNone x hx
