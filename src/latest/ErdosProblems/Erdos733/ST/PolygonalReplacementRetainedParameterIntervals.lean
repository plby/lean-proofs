import ErdosProblems.Erdos733.ST.Preamble

open Classical
noncomputable section

-- [TABLET NODE: PolygonalReplacementRetainedParameterIntervals]
lemma PolygonalReplacementRetainedParameterIntervals
    {α C : Type*} [LinearOrder α]
    (source target : α) (cuts : List C)
    (left center right : C → α)
    (source_lt_target : source < target)
    (source_lt_left : ∀ c, c ∈ cuts → source < left c)
    (cut_order : ∀ c, c ∈ cuts → left c < center c ∧ center c < right c)
    (right_lt_target : ∀ c, c ∈ cuts → right c < target)
    (consecutive_separation :
      ∀ n (hn : n + 1 < cuts.length), right cuts[n] < left cuts[n + 1]) :
    ∃ intervals : List (α × α),
      intervals.length = cuts.length + 1 ∧
        (∀ (n : ℕ) (a b : α), intervals[n]? = some (a, b) → a < b) ∧
        intervals.head?.map Prod.fst = some source ∧
        intervals.getLast?.map Prod.snd = some target ∧
        (∀ (n : ℕ) (hn : n < cuts.length),
          intervals[n]?.map Prod.snd = some (left cuts[n]) ∧
            intervals[n + 1]?.map Prod.fst = some (right cuts[n]) ∧
              left cuts[n] < center cuts[n] ∧
                center cuts[n] < right cuts[n]) := by
-- BODY
  classical
  let starts : List α := source :: cuts.map right
  let ends : List α := cuts.map left ++ [target]
  let intervals : List (α × α) := starts.zip ends
  have hstarts_len : starts.length = cuts.length + 1 := by
    simp [starts]
  have hends_len : ends.length = cuts.length + 1 := by
    simp [ends]
  have hintervals_len : intervals.length = cuts.length + 1 := by
    simp [intervals, hstarts_len, hends_len]
  have hstarts_zero (h : 0 < starts.length) : starts[0] = source := by
    simp [starts]
  have hstarts_succ :
      ∀ n (hn : n < cuts.length) (h : n + 1 < starts.length),
        starts[n + 1] = right cuts[n] := by
    intro n hn h
    simp [starts]
  have hends_of_lt :
      ∀ n (hn : n < cuts.length) (h : n < ends.length),
        ends[n] = left cuts[n] := by
    intro n hn h
    simp [ends, hn]
  have hends_last (h : cuts.length < ends.length) :
      ends[cuts.length] = target := by
    simp [ends]
  refine ⟨intervals, hintervals_len, ?_, ?_, ?_, ?_⟩
  · intro n a b hnSome
    have hn : n < intervals.length := by
      rw [List.getElem?_eq_some_iff] at hnSome
      exact hnSome.1
    rw [hintervals_len] at hn
    have hn_starts : n < starts.length := by omega
    have hn_ends : n < ends.length := by omega
    have hn_zip : n < (starts.zip ends).length := by
      rw [List.length_zip, hstarts_len, hends_len]
      omega
    have hget : intervals[n] = (starts[n], ends[n]) := by
      exact List.getElem_zip (l := starts) (l' := ends) (i := n) (h := hn_zip)
    have hab : (a, b) = (starts[n], ends[n]) := by
      rw [List.getElem?_eq_some_iff] at hnSome
      exact hnSome.2.symm.trans hget
    have ha : a = starts[n] := by
      exact congrArg Prod.fst hab
    have hb : b = ends[n] := by
      exact congrArg Prod.snd hab
    by_cases hnlast : n = cuts.length
    · subst n
      have hstart_cases : cuts.length = 0 ∨ ∃ k, cuts.length = k + 1 := by
        cases cuts.length with
        | zero => exact Or.inl rfl
        | succ k => exact Or.inr ⟨k, rfl⟩
      cases hstart_cases with
      | inl hzero =>
          have hs : starts[0] = source := by
            simpa [hzero] using hstarts_zero (by omega)
          have he : ends[0] = target := by
            simpa [hzero] using hends_last (by omega)
          simpa [ha, hb, hzero, hs, he] using source_lt_target
      | inr hk =>
          rcases hk with ⟨k, hk⟩
          have hklt : k < cuts.length := by omega
          have hs : starts[k + 1] = right cuts[k] :=
            hstarts_succ k hklt (by omega)
          have he : ends[k + 1] = target := by
            simpa [hk] using hends_last (by omega)
          have hmem : cuts[k] ∈ cuts := List.getElem_mem hklt
          have hrt : right cuts[k] < target := right_lt_target cuts[k] hmem
          simpa [ha, hb, hk, hs, he] using hrt
    · have hnltcuts : n < cuts.length := by omega
      by_cases hnzero : n = 0
      · subst n
        have hs : starts[0] = source := hstarts_zero (by omega)
        have he : ends[0] = left cuts[0] := hends_of_lt 0 hnltcuts (by omega)
        have hmem : cuts[0] ∈ cuts := List.getElem_mem hnltcuts
        have hsl : source < left cuts[0] := source_lt_left cuts[0] hmem
        simpa [ha, hb, hs, he] using hsl
      · rcases Nat.exists_eq_succ_of_ne_zero hnzero with ⟨k, hk⟩
        subst n
        have hk_succ_lt : k + 1 < cuts.length := by omega
        have hklt : k < cuts.length := by omega
        have hs : starts[k + 1] = right cuts[k] :=
          hstarts_succ k hklt (by omega)
        have he : ends[k + 1] = left cuts[k + 1] :=
          hends_of_lt (k + 1) hk_succ_lt (by omega)
        have hsep : right cuts[k] < left cuts[k + 1] :=
          consecutive_separation k hk_succ_lt
        simpa [ha, hb, hs, he] using hsep
  · cases cuts with
    | nil =>
        simp [intervals, starts, ends]
    | cons c cs =>
        simp [intervals, starts, ends]
  · rw [List.getLast?_eq_getElem?]
    have hidx : intervals.length - 1 = cuts.length := by
      rw [hintervals_len]
      omega
    rw [hidx]
    have hlast_interval : cuts.length < intervals.length := by
      rw [hintervals_len]
      omega
    have hlast_ends : cuts.length < ends.length := by omega
    have hlast_zip : cuts.length < (starts.zip ends).length := by
      rw [List.length_zip, hstarts_len, hends_len]
      omega
    have hgetlast : intervals[cuts.length] = (starts[cuts.length], ends[cuts.length]) := by
      exact
        List.getElem_zip (l := starts) (l' := ends) (i := cuts.length)
          (h := hlast_zip)
    have hendlast : ends[cuts.length] = target := hends_last hlast_ends
    have hsome : intervals[cuts.length]? =
        some (starts[cuts.length], ends[cuts.length]) := by
      rw [List.getElem?_eq_some_iff]
      exact ⟨hlast_interval, hgetlast⟩
    simp [hsome, hendlast]
  · intro n hn
    have hn_interval : n < intervals.length := by
      rw [hintervals_len]
      omega
    have hns_interval : n + 1 < intervals.length := by
      rw [hintervals_len]
      omega
    have hns_starts : n + 1 < starts.length := by omega
    have hn_ends : n < ends.length := by omega
    have hn_zip : n < (starts.zip ends).length := by
      rw [List.length_zip, hstarts_len, hends_len]
      omega
    have hns_zip : n + 1 < (starts.zip ends).length := by
      rw [List.length_zip, hstarts_len, hends_len]
      omega
    have hgetn : intervals[n] = (starts[n], ends[n]) := by
      exact List.getElem_zip (l := starts) (l' := ends) (i := n) (h := hn_zip)
    have hgetns : intervals[n + 1] = (starts[n + 1], ends[n + 1]) := by
      exact
        List.getElem_zip (l := starts) (l' := ends) (i := n + 1)
          (h := hns_zip)
    have hendn : ends[n] = left cuts[n] := hends_of_lt n hn hn_ends
    have hstartns : starts[n + 1] = right cuts[n] :=
      hstarts_succ n hn hns_starts
    have hmem : cuts[n] ∈ cuts := List.getElem_mem hn
    have hco := cut_order cuts[n] hmem
    constructor
    · have hsome : intervals[n]? = some (starts[n], ends[n]) := by
        rw [List.getElem?_eq_some_iff]
        exact ⟨hn_interval, hgetn⟩
      simp [hsome, hendn]
    constructor
    · have hsome : intervals[n + 1]? = some (starts[n + 1], ends[n + 1]) := by
        rw [List.getElem?_eq_some_iff]
        exact ⟨hns_interval, hgetns⟩
      simp [hsome, hstartns]
    constructor
    · exact hco.1
    · exact hco.2
