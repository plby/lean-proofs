/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.TilingDistinguishedTraceInvariant

/-!
# Threshold-hit records under deletion of subcritical sites

The threshold-hit sequence remembers the order in which sites acquire their
`m`-th visit.  For the low-gap screen we also need the whole retained prefix
at each such hit.  The records below supply exactly that extra information
and show that deleting sites whose final multiplicity is below `m` preserves
all records, after applying the same deletion to their stored prefixes.
-/

namespace Erdos1165.TilingThresholdHitRecordInvariant

open Erdos1165.TilingDistinguishedTraceInvariant
open HLOZPathEvents LazyDecomposition PreStoppingFiber PreStoppingSpatialLaw

variable {α : Type*} [BEq α] [LawfulBEq α] [DecidableEq α]

/-- The site which has just acquired its `m`-th visit, together with the
complete prefix through that visit. -/
def thresholdHitRecordsAux (m : ℕ) (seen : List α) :
    List α → List (α × List α)
  | [] => []
  | x :: xs =>
      if seen.count x + 1 = m then
        (x, seen ++ [x]) :: thresholdHitRecordsAux m (seen ++ [x]) xs
      else thresholdHitRecordsAux m (seen ++ [x]) xs

def thresholdHitRecords (m : ℕ) (p : List α) : List (α × List α) :=
  thresholdHitRecordsAux m [] p

theorem thresholdHitRecordsAux_map_fst (m : ℕ) (seen p : List α) :
    (thresholdHitRecordsAux m seen p).map Prod.fst =
      thresholdHitSequenceAux m seen p := by
  induction p generalizing seen with
  | nil => rfl
  | cons x xs ih =>
      by_cases hx : seen.count x + 1 = m
      · simp [thresholdHitRecordsAux, thresholdHitSequenceAux, hx, ih]
      · simp [thresholdHitRecordsAux, thresholdHitSequenceAux, hx, ih]

theorem thresholdHitRecords_map_fst (m : ℕ) (p : List α) :
    (thresholdHitRecords m p).map Prod.fst = thresholdHitSequence m p :=
  thresholdHitRecordsAux_map_fst m [] p

theorem length_thresholdHitRecords (m : ℕ) (hm : 0 < m) (p : List α) :
    (thresholdHitRecords m p).length = (listThresholdSites p m).card := by
  rw [← List.length_map, thresholdHitRecords_map_fst,
    length_thresholdHitSequence m hm]

theorem thresholdHitRecordsAux_append (m : ℕ) (seen p q : List α) :
    thresholdHitRecordsAux m seen (p ++ q) =
      thresholdHitRecordsAux m seen p ++
        thresholdHitRecordsAux m (seen ++ p) q := by
  induction p generalizing seen with
  | nil => simp [thresholdHitRecordsAux]
  | cons x xs ih =>
      by_cases hx : seen.count x + 1 = m
      · simp only [List.cons_append, thresholdHitRecordsAux, if_pos hx,
          List.cons.injEq, true_and]
        rw [ih]
        simp only [List.append_assoc, List.singleton_append]
      · simp only [List.cons_append, thresholdHitRecordsAux, if_neg hx]
        rw [ih]
        simp only [List.append_assoc, List.singleton_append]

theorem thresholdHitRecords_append_singleton_of_count (m : ℕ)
    (p : List α) (x : α) (hcount : p.count x + 1 = m) :
    thresholdHitRecords m (p ++ [x]) =
      thresholdHitRecords m p ++ [(x, p ++ [x])] := by
  unfold thresholdHitRecords
  rw [thresholdHitRecordsAux_append]
  simp [thresholdHitRecordsAux, hcount]

theorem thresholdHitRecords_prefix {m : ℕ} {p q : List α}
    (hpq : p <+: q) : thresholdHitRecords m p <+:
      thresholdHitRecords m q := by
  obtain ⟨tail, rfl⟩ := hpq
  unfold thresholdHitRecords
  rw [thresholdHitRecordsAux_append]
  exact List.prefix_append _ _

theorem thresholdHitRecords_at_creation {s : WalkPath} {m k n : ℕ}
    (hm : 0 < m) (hk : 0 < k)
    (hcreation : ThresholdCreation s m k n) :
    (thresholdHitRecords m
        (finitePathList (pathPrefix s n))).length = k ∧
      (thresholdHitRecords m
        (finitePathList (pathPrefix s n))).getLast? =
          some (s n, finitePathList (pathPrefix s n)) := by
  cases n with
  | zero =>
      have hkone : k = 1 := by
        have hle := thresholdCount_le_time_add_one s 0 m
        have hge := hcreation.1
        omega
      subst k
      have hmone : m = 1 := by
        have hmem := position_mem_thresholdSites_of_creation
          (s := s) (m := m) (k := 1) (n := 0) (by omega) hcreation
        have hlocal := (mem_thresholdSites s 0 m (s 0)).mp hmem |>.2
        simp [localTime, localTimePrefix, pathPrefix] at hlocal
        omega
      subst m
      simp [thresholdHitRecords, thresholdHitRecordsAux,
        finitePathList, pathPrefix]
  | succ q =>
      have hterminal :=
        (thresholdCreation_iff_terminal_count_and_new_localTime
          s m k (q + 1) hm hk (by omega)).mp hcreation
      have hcount : (finitePathList (pathPrefix s q)).count (s (q + 1)) + 1 = m := by
        change listLocalTime (finitePathList (pathPrefix s q)) (s (q + 1)) + 1 = m
        rw [← localTime_eq_listLocalTime]
        rw [← hterminal.2]
        simpa using (localTime_succ s q (s (q + 1))).symm
      rw [finitePathList_succ]
      rw [thresholdHitRecords_append_singleton_of_count m _ _ hcount]
      constructor
      · rw [List.length_append, List.length_singleton,
          ← List.length_map, thresholdHitRecords_map_fst,
          length_thresholdHitSequence_finitePathList s q m hm]
        have hprev := hcreation.2 q (Nat.lt_succ_self q)
        have hstep := thresholdCount_succ_le s q m
        omega
      · simp

theorem thresholdHitRecords_getElem?_of_creation_of_le
    {s : WalkPath} {m k n N : ℕ} (hm : 0 < m) (hk : 0 < k)
    (hcreation : ThresholdCreation s m k n) (hnN : n ≤ N) :
    (thresholdHitRecords m
      (finitePathList (pathPrefix s N)))[k - 1]? =
        some (s n, finitePathList (pathPrefix s n)) := by
  have hdata := thresholdHitRecords_at_creation hm hk hcreation
  have hp := thresholdHitRecords_prefix (m := m)
    (finitePathList_prefix_of_le s hnN)
  obtain ⟨tail, htail⟩ := hp
  rw [← htail, List.getElem?_append_left (by rw [hdata.1]; omega)]
  rw [← hdata.1, ← List.getLast?_eq_getElem?, hdata.2]

theorem thresholdHitRecordsAux_filter (m : ℕ) (hm : 0 < m)
    (P : α → Bool) (seen p : List α)
    (hout : ∀ y, P y = false → (seen ++ p).count y < m) :
    (thresholdHitRecordsAux m seen p).map
        (fun z ↦ (z.1, z.2.filter P)) =
      thresholdHitRecordsAux m (seen.filter P) (p.filter P) := by
  induction p generalizing seen with
  | nil => simp [thresholdHitRecordsAux]
  | cons x xs ih =>
      have hout' : ∀ y, P y = false →
          ((seen ++ [x]) ++ xs).count y < m := by
        intro y hy
        simpa only [List.append_assoc, List.singleton_append] using hout y hy
      by_cases hxP : P x = true
      · have hcount : (seen.filter P).count x = seen.count x :=
          List.count_filter hxP
        by_cases hx : seen.count x + 1 = m
        · simp only [thresholdHitRecordsAux, if_pos hx, List.map_cons,
            List.filter_cons, hxP, if_true, hcount, List.cons.injEq]
          constructor
          · simp [List.filter_append, hxP]
          · simpa [List.filter_append, hxP] using ih (seen ++ [x]) hout'
        · have hx' : (seen.filter P).count x + 1 ≠ m := by
            simpa only [hcount] using hx
          simp only [thresholdHitRecordsAux, if_neg hx, List.filter_cons,
            hxP, if_true, hcount, if_neg hx']
          simpa [List.filter_append, hxP] using ih (seen ++ [x]) hout'
      · have hxPfalse : P x = false := Bool.eq_false_of_not_eq_true hxP
        have hxlt : seen.count x + 1 < m := by
          have hfull := hout x hxPfalse
          simp only [List.count_append, List.count_cons, beq_self_eq_true,
            if_true] at hfull
          omega
        have hx : seen.count x + 1 ≠ m := by omega
        simp only [thresholdHitRecordsAux, if_neg hx, List.filter_cons,
          hxPfalse, Bool.false_eq_true, if_false]
        have hrec := ih (seen ++ [x]) hout'
        simpa [List.filter_append, hxPfalse] using hrec

theorem thresholdHitRecords_filter (m : ℕ) (hm : 0 < m)
    (P : α → Bool) (p : List α)
    (hout : ∀ y, P y = false → p.count y < m) :
    (thresholdHitRecords m p).map
        (fun z ↦ (z.1, z.2.filter P)) =
      thresholdHitRecords m (p.filter P) := by
  simpa [thresholdHitRecords] using
    thresholdHitRecordsAux_filter m hm P [] p (by simpa using hout)

/-- Equal retained paths, after deleting sites which never reach level `m`,
have equal creation locations and equal retained prefixes at every creation
rank occurring before the displayed terminal clocks. -/
theorem filtered_creation_record_eq
    {s s' : WalkPath} {m rank n n' N N' : ℕ}
    (hm : 0 < m) (hrank : 0 < rank)
    (hcreation : ThresholdCreation s m rank n)
    (hcreation' : ThresholdCreation s' m rank n')
    (hn : n ≤ N) (hn' : n' ≤ N')
    (P : Point → Bool)
    (hfilter :
      (finitePathList (pathPrefix s N)).filter P =
        (finitePathList (pathPrefix s' N')).filter P)
    (hout : ∀ y, P y = false →
      localTime s N y < m)
    (hout' : ∀ y, P y = false →
      localTime s' N' y < m) :
    s n = s' n' ∧
      (finitePathList (pathPrefix s n)).filter P =
        (finitePathList (pathPrefix s' n')).filter P := by
  let p := finitePathList (pathPrefix s N)
  let p' := finitePathList (pathPrefix s' N')
  have houtList : ∀ y, P y = false → p.count y < m := by
    intro y hy
    change listLocalTime p y < m
    rw [← localTime_eq_listLocalTime]
    exact hout y hy
  have houtList' : ∀ y, P y = false → p'.count y < m := by
    intro y hy
    change listLocalTime p' y < m
    rw [← localTime_eq_listLocalTime]
    exact hout' y hy
  have hrecords :
      (thresholdHitRecords m p).map
          (fun z ↦ (z.1, z.2.filter P)) =
        (thresholdHitRecords m p').map
          (fun z ↦ (z.1, z.2.filter P)) := by
    rw [thresholdHitRecords_filter m hm P p houtList,
      thresholdHitRecords_filter m hm P p' houtList', hfilter]
  have hleft := thresholdHitRecords_getElem?_of_creation_of_le
    hm hrank hcreation hn
  have hright := thresholdHitRecords_getElem?_of_creation_of_le
    hm hrank hcreation' hn'
  change (thresholdHitRecords m p)[rank - 1]? =
      some (s n, finitePathList (pathPrefix s n)) at hleft
  change (thresholdHitRecords m p')[rank - 1]? =
      some (s' n', finitePathList (pathPrefix s' n')) at hright
  have hget := congrArg (fun xs : List (Point × List Point) ↦
      xs[rank - 1]?) hrecords
  rw [List.getElem?_map, List.getElem?_map, hleft, hright] at hget
  simpa using Option.some.inj hget

end Erdos1165.TilingThresholdHitRecordInvariant
