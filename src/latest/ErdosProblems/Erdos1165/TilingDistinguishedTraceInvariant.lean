import ErdosProblems.Erdos1165.TilingFavoriteTraceSupport

namespace Erdos1165.TilingDistinguishedTraceInvariant
open TilingLazyDecomposition TilingSpatialInsertionFiber
open TilingCappedMarginalization TilingInsertedLocalTime
open SpatialInsertionFiber PathInsertion

noncomputable section
abbrev DominoTiling := Tilings.Tiling

def pointInTilingBases (t : DominoTiling) (D : Finset Point)
    (y : Point) : Bool := decide (tilingBase t y ∈ D)

def eraseAwayTilingReturns (t : DominoTiling) (D : Finset Point) :
    Point → List Block → List Block
  | _, [] => []
  | x, b :: bs =>
      if b = tilingRemovableBlock t x ∧ tilingBase t x ∉ D then
        eraseAwayTilingReturns t D x bs
      else b :: eraseAwayTilingReturns t D (blockEnd x b) bs

theorem filter_blockPathTail_eraseAwayTilingReturns
    (t : DominoTiling) (D : Finset Point) (x : Point) :
    ∀ bs : List Block,
      (blockPathTail x bs).filter (pointInTilingBases t D) =
        (blockPathTail x (eraseAwayTilingReturns t D x bs)).filter
          (pointInTilingBases t D) := by
  intro bs
  induction bs generalizing x with
  | nil => rfl
  | cons b bs ih =>
      by_cases hskip : b = tilingRemovableBlock t x ∧ tilingBase t x ∉ D
      · rcases hskip with ⟨rfl, hx⟩
        simp only [eraseAwayTilingReturns, true_and, hx, if_pos,
          blockPathTail, blockMiddle_tilingRemovableBlock,
          blockEnd_tilingRemovableBlock]
        have hpartner : tilingBase t (tilingPartner t x) ∉ D := by
          rw [tilingBase_partner]
          exact hx
        simp only [List.filter_cons, pointInTilingBases, decide_eq_false_iff_not,
          hpartner, Bool.false_eq_true, if_false, hx]
        exact ih x
      · simp only [eraseAwayTilingReturns, if_neg hskip, blockPathTail,
          List.filter_cons]
        rw [ih]

theorem filter_blockPath_eraseAwayTilingReturns
    (t : DominoTiling) (D : Finset Point) (x : Point) (bs : List Block) :
    (blockPath x bs).filter (pointInTilingBases t D) =
      (blockPath x (eraseAwayTilingReturns t D x bs)).filter
        (pointInTilingBases t D) := by
  simp only [blockPath, List.filter_cons]
  rw [filter_blockPathTail_eraseAwayTilingReturns]

@[simp] theorem eraseAwayTilingReturns_replicate_removable
    (t : DominoTiling) (D : Finset Point) (x : Point) (n : ℕ) :
    eraseAwayTilingReturns t D x
        (List.replicate n (tilingRemovableBlock t x)) =
      if tilingBase t x ∈ D then
        List.replicate n (tilingRemovableBlock t x) else [] := by
  induction n with
  | zero => simp [eraseAwayTilingReturns]
  | succ n ih =>
      rw [List.replicate_succ]
      by_cases hx : tilingBase t x ∈ D
      · simp [eraseAwayTilingReturns, hx, ih]
      · simp [eraseAwayTilingReturns, hx, ih]

theorem eraseAwayTilingReturns_append (t : DominoTiling)
    (D : Finset Point) (x : Point) (as bs : List Block) :
    eraseAwayTilingReturns t D x (as ++ bs) =
      eraseAwayTilingReturns t D x as ++
        eraseAwayTilingReturns t D (followBlocks x as) bs := by
  induction as generalizing x with
  | nil => rfl
  | cons a as ih =>
      by_cases hskip : a = tilingRemovableBlock t x ∧ tilingBase t x ∉ D
      · rcases hskip with ⟨rfl, hx⟩
        simp only [List.cons_append, eraseAwayTilingReturns, true_and, hx,
          if_pos, blockEnd_tilingRemovableBlock]
        rw [ih]
        simp [eraseAwayTilingReturns, hx, followBlocks]
      · simp only [List.cons_append, eraseAwayTilingReturns, if_neg hskip]
        rw [ih]
        rfl

theorem cappedCoordinate_eq_of_distinguished_projection
    {i cap : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (D : Finset Point)
    (q q' : TilingCappedCoordinates i cap)
    (hdist : (splitTilingCoordinatesEquiv t x r D q).1 =
      (splitTilingCoordinatesEquiv t x r D q').1)
    (k : Fin (i + 1))
    (hk : tilingBase t (rawExternalBase x r.1 k) ∈ D) :
    q k = q' k := by
  let b := tilingCoordinateDomino t x r k
  let bd : TilingDistinguishedDomino t x r D := ⟨b, hk⟩
  let kc : TilingCoordinatesAt t x r b := ⟨k, rfl⟩
  have h := congrFun (congrFun hdist bd) kc
  simpa only [TilingCappedMarginalization.splitTilingCoordinatesEquiv_distinguished_apply]
    using h

theorem eraseAwayTilingReturns_tilingInsertGapVector_eq_of_coordinates {i : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (D : Finset Point) (q q' : Fin (i + 1) → ℕ)
    (hq : ∀ k, tilingBase t (rawExternalBase x r.1 k) ∈ D →
      q k = q' k) :
    eraseAwayTilingReturns t D x
        (tilingInsertGapVector t x r (fun k ↦ (q k : ℕ))) =
      eraseAwayTilingReturns t D x
        (tilingInsertGapVector t x r (fun k ↦ (q' k : ℕ))) := by
  induction i generalizing x with
  | zero =>
      rw [tilingInsertGapVector_zero, tilingInsertGapVector_zero,
        eraseAwayTilingReturns_replicate_removable,
        eraseAwayTilingReturns_replicate_removable]
      split
      · rename_i hx
        rw [hq 0 (by rw [rawExternalBase_zero]; exact hx)]
      · rfl
  | succ i ih =>
      rw [tilingInsertGapVector_succ, tilingInsertGapVector_succ,
        eraseAwayTilingReturns_append, eraseAwayTilingReturns_append]
      rw [eraseAwayTilingReturns_append, eraseAwayTilingReturns_append]
      rw [eraseAwayTilingReturns_replicate_removable,
        eraseAwayTilingReturns_replicate_removable]
      by_cases hx : tilingBase t x ∈ D
      · rw [if_pos hx, if_pos hx]
        rw [hq 0 (by rw [rawExternalBase_zero]; exact hx)]
        rw [followBlocks_append x
          (List.replicate (q' 0) (tilingRemovableBlock t x)) [r.1 0]]
        simp_rw [
          TilingSpatialInsertionFiber.followBlocks_replicate_tilingRemovable]
        simp only [
          followBlocks, List.foldl_cons, List.foldl_nil]
        congr 1
        apply ih
        intro k hk
        exact hq k.succ (by
          simpa only [rawExternalBase_succ, tilingRetainedTail] using hk)
      · rw [if_neg hx, if_neg hx]
        simp only [List.nil_append]
        rw [followBlocks_append x
            (List.replicate (q 0) (tilingRemovableBlock t x)) [r.1 0],
          followBlocks_append x
            (List.replicate (q' 0) (tilingRemovableBlock t x)) [r.1 0]]
        simp_rw [
          TilingSpatialInsertionFiber.followBlocks_replicate_tilingRemovable]
        simp only [
          followBlocks, List.foldl_cons, List.foldl_nil]
        congr 1
        apply ih
        intro k hk
        exact hq k.succ (by
          simpa only [rawExternalBase_succ, tilingRetainedTail] using hk)

theorem eraseAwayTilingReturns_tilingInsertGapVector_eq {i cap : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (D : Finset Point) (q q' : TilingCappedCoordinates i cap)
    (hdist : (splitTilingCoordinatesEquiv t x r D q).1 =
      (splitTilingCoordinatesEquiv t x r D q').1) :
    eraseAwayTilingReturns t D x
        (tilingInsertGapVector t x r (fun k ↦ (q k : ℕ))) =
      eraseAwayTilingReturns t D x
        (tilingInsertGapVector t x r (fun k ↦ (q' k : ℕ))) := by
  apply eraseAwayTilingReturns_tilingInsertGapVector_eq_of_coordinates
  intro k hk
  exact congrArg (fun z : Fin (cap + 1) ↦ (z : ℕ))
    (cappedCoordinate_eq_of_distinguished_projection
      t x r D q q' hdist k hk)

theorem filter_blockPath_tilingInsertGapVector_eq {i cap : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (D : Finset Point) (q q' : TilingCappedCoordinates i cap)
    (hdist : (splitTilingCoordinatesEquiv t x r D q).1 =
      (splitTilingCoordinatesEquiv t x r D q').1) :
    (blockPath x
        (tilingInsertGapVector t x r (fun k ↦ (q k : ℕ)))).filter
          (pointInTilingBases t D) =
      (blockPath x
        (tilingInsertGapVector t x r (fun k ↦ (q' k : ℕ)))).filter
          (pointInTilingBases t D) := by
  calc
    _ = (blockPath x
          (eraseAwayTilingReturns t D x
            (tilingInsertGapVector t x r (fun k ↦ (q k : ℕ))))).filter
          (pointInTilingBases t D) :=
      filter_blockPath_eraseAwayTilingReturns t D x _
    _ = (blockPath x
          (eraseAwayTilingReturns t D x
            (tilingInsertGapVector t x r (fun k ↦ (q' k : ℕ))))).filter
          (pointInTilingBases t D) := by
      rw [eraseAwayTilingReturns_tilingInsertGapVector_eq t x r D q q' hdist]
    _ = _ := (filter_blockPath_eraseAwayTilingReturns t D x _).symm

theorem filter_tilingPrefixPointPath_tilingInsertGapVector_eq {i cap : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (terminal : Option Point) (D : Finset Point)
    (q q' : TilingCappedCoordinates i cap)
    (hdist : (splitTilingCoordinatesEquiv t x r D q).1 =
      (splitTilingCoordinatesEquiv t x r D q').1) :
    (tilingPrefixPointPath x
        (tilingInsertGapVector t x r (fun k ↦ (q k : ℕ))) terminal).filter
          (pointInTilingBases t D) =
      (tilingPrefixPointPath x
        (tilingInsertGapVector t x r (fun k ↦ (q' k : ℕ))) terminal).filter
          (pointInTilingBases t D) := by
  cases terminal with
  | none => exact filter_blockPath_tilingInsertGapVector_eq t x r D q q' hdist
  | some z =>
      simp only [tilingPrefixPointPath, List.filter_append]
      rw [filter_blockPath_tilingInsertGapVector_eq t x r D q q' hdist]

end
end Erdos1165.TilingDistinguishedTraceInvariant

namespace Erdos1165.TilingDistinguishedTraceInvariant

variable {α : Type*} [BEq α] [LawfulBEq α] [DecidableEq α]

def thresholdHitSequenceAux (m : ℕ) (seen : List α) : List α → List α
  | [] => []
  | x :: xs =>
      if seen.count x + 1 = m then
        x :: thresholdHitSequenceAux m (seen ++ [x]) xs
      else thresholdHitSequenceAux m (seen ++ [x]) xs

def thresholdHitSequence (m : ℕ) (p : List α) : List α :=
  thresholdHitSequenceAux m [] p

def listThresholdSites (p : List α) (m : ℕ) : Finset α :=
  p.toFinset.filter fun y ↦ m ≤ p.count y

theorem listThresholdSites_append_singleton (m : ℕ) (seen : List α)
    (x : α) (hmpos : 0 < m) :
    listThresholdSites (seen ++ [x]) m =
      if seen.count x + 1 = m then insert x (listThresholdSites seen m)
      else listThresholdSites seen m := by
  classical
  ext y
  by_cases hyx : y = x
  · subst y
    by_cases hm : seen.count x + 1 = m
    · rw [if_pos hm]
      simp [listThresholdSites, hm]
    · rw [if_neg hm]
      simp only [listThresholdSites, Finset.mem_filter, List.mem_toFinset,
        List.mem_append, List.mem_singleton, or_true, true_and,
        List.count_append, List.count_singleton, beq_self_eq_true,
        if_true]
      change (m ≤ seen.count x + 1) ↔
        (x ∈ seen ∧ m ≤ seen.count x)
      constructor
      · intro hnew
        have hle : m ≤ seen.count x := by omega
        have hxmem : x ∈ seen := by
          by_contra hnot
          have hz := List.count_eq_zero.mpr hnot
          omega
        exact ⟨hxmem, hle⟩
      · rintro ⟨_, hle⟩
        omega
  · simp only [listThresholdSites, Finset.mem_filter, List.mem_toFinset,
      List.mem_append, List.mem_singleton, hyx, Ne.symm hyx, or_false,
      Finset.mem_insert, false_or, List.count_append,
      List.count_singleton]
    simp only [show (x == y) = false by simp [Ne.symm hyx], ite_false,
      add_zero]
    by_cases hm : seen.count x + 1 = m
    · simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
      exact fun h ↦ (hyx h).elim
    · simp [hm]

theorem length_thresholdHitSequenceAux (m : ℕ) (hmpos : 0 < m)
    (seen p : List α) :
    (thresholdHitSequenceAux m seen p).length +
        (listThresholdSites seen m).card =
      (listThresholdSites (seen ++ p) m).card := by
  induction p generalizing seen with
  | nil => simp [thresholdHitSequenceAux]
  | cons x xs ih =>
      rw [show seen ++ x :: xs = (seen ++ [x]) ++ xs by simp]
      rw [← ih (seen ++ [x])]
      rw [listThresholdSites_append_singleton m seen x hmpos]
      by_cases hm : seen.count x + 1 = m
      · rw [if_pos hm]
        have hxnot : x ∉ listThresholdSites seen m := by
          simp only [listThresholdSites, Finset.mem_filter,
            List.mem_toFinset, not_and]
          intro _
          omega
        simp [thresholdHitSequenceAux, hm, hxnot]
        omega
      · rw [if_neg hm]
        simp [thresholdHitSequenceAux, hm]

theorem length_thresholdHitSequence (m : ℕ) (hmpos : 0 < m) (p : List α) :
    (thresholdHitSequence m p).length =
      (listThresholdSites p m).card := by
  have h := length_thresholdHitSequenceAux m hmpos [] p
  simpa [thresholdHitSequence, listThresholdSites] using h

theorem thresholdHitSequenceAux_append (m : ℕ) (seen p q : List α) :
    thresholdHitSequenceAux m seen (p ++ q) =
      thresholdHitSequenceAux m seen p ++
        thresholdHitSequenceAux m (seen ++ p) q := by
  induction p generalizing seen with
  | nil => simp [thresholdHitSequenceAux]
  | cons x xs ih =>
      by_cases hm : seen.count x + 1 = m
      · simp only [List.cons_append, thresholdHitSequenceAux, if_pos hm,
          List.cons_append, List.cons.injEq, true_and]
        rw [ih]
        simp only [List.append_assoc, List.singleton_append]
      · simp only [List.cons_append, thresholdHitSequenceAux, if_neg hm]
        rw [ih]
        simp only [List.append_assoc, List.singleton_append]

theorem thresholdHitSequence_append_singleton_of_count (m : ℕ)
    (p : List α) (x : α) (hcount : p.count x + 1 = m) :
    thresholdHitSequence m (p ++ [x]) =
      thresholdHitSequence m p ++ [x] := by
  unfold thresholdHitSequence
  rw [thresholdHitSequenceAux_append]
  simp [thresholdHitSequenceAux, hcount]

theorem thresholdHitSequence_prefix {m : ℕ} {p q : List α}
    (hpq : p <+: q) : thresholdHitSequence m p <+: thresholdHitSequence m q := by
  obtain ⟨tail, rfl⟩ := hpq
  unfold thresholdHitSequence
  rw [thresholdHitSequenceAux_append]
  exact List.prefix_append _ _

open HLOZPathEvents PreStoppingSpatialLaw LazyDecomposition PreStoppingFiber

theorem listThresholdSites_finitePathList (s : WalkPath) (n m : ℕ)
    (hm : 0 < m) :
    listThresholdSites (finitePathList (pathPrefix s n)) m =
      thresholdSites s n m := by
  ext y
  simp only [listThresholdSites, Finset.mem_filter, List.mem_toFinset]
  rw [mem_thresholdSites_iff s n m y hm, localTime_eq_listLocalTime]
  unfold listLocalTime
  constructor
  · exact fun h ↦ h.2
  · intro hcount
    refine ⟨?_, hcount⟩
    exact List.count_pos_iff.mp (hm.trans_le hcount)

theorem length_thresholdHitSequence_finitePathList (s : WalkPath)
    (n m : ℕ) (hm : 0 < m) :
    (thresholdHitSequence m
      (finitePathList (pathPrefix s n))).length = thresholdCount s n m := by
  rw [length_thresholdHitSequence m hm,
    listThresholdSites_finitePathList s n m hm]
  rfl

theorem finitePathList_succ (s : WalkPath) (n : ℕ) :
    finitePathList (pathPrefix s (n + 1)) =
      finitePathList (pathPrefix s n) ++ [s (n + 1)] := by
  unfold finitePathList pathPrefix
  rw [List.ofFn_succ_last]
  rfl

theorem thresholdHitSequence_at_creation {s : WalkPath} {m k n : ℕ}
    (hm : 0 < m) (hk : 0 < k) (hn : 0 < n)
    (hcreation : ThresholdCreation s m k n) :
    (thresholdHitSequence m
      (finitePathList (pathPrefix s n))).length = k ∧
      (thresholdHitSequence m
        (finitePathList (pathPrefix s n))).getLast? = some (s n) := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have hterminal :=
    (thresholdCreation_iff_terminal_count_and_new_localTime
      s m k (q + 1) hm hk (by omega)).mp hcreation
  have hcount : (finitePathList (pathPrefix s q)).count (s (q + 1)) + 1 = m := by
    change listLocalTime (finitePathList (pathPrefix s q)) (s (q + 1)) + 1 = m
    rw [← localTime_eq_listLocalTime]
    rw [← hterminal.2]
    simpa using (localTime_succ s q (s (q + 1))).symm
  rw [finitePathList_succ]
  rw [thresholdHitSequence_append_singleton_of_count m _ _ hcount]
  constructor
  · rw [List.length_append, List.length_singleton,
      length_thresholdHitSequence_finitePathList s q m hm]
    have hprev := hcreation.2 q (Nat.lt_succ_self q)
    have hstep := thresholdCount_succ_le s q m
    omega
  · simp

theorem thresholdHitSequence_at_creation_all {s : WalkPath} {m k n : ℕ}
    (hm : 0 < m) (hk : 0 < k)
    (hcreation : ThresholdCreation s m k n) :
    (thresholdHitSequence m
      (finitePathList (pathPrefix s n))).length = k ∧
      (thresholdHitSequence m
        (finitePathList (pathPrefix s n))).getLast? = some (s n) := by
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
      simp [thresholdHitSequence, thresholdHitSequenceAux,
        finitePathList, pathPrefix]
  | succ q =>
      exact thresholdHitSequence_at_creation (by omega) hk (by omega) hcreation

theorem finitePathList_prefix_of_le (s : WalkPath) {n N : ℕ} (hnN : n ≤ N) :
    finitePathList (pathPrefix s n) <+:
      finitePathList (pathPrefix s N) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnN
  clear hnN
  induction d with
  | zero => simp
  | succ d ih =>
      apply ih.trans
      rw [show n + d.succ = (n + d) + 1 by omega,
        finitePathList_succ]
      exact List.prefix_append _ _

theorem thresholdHitSequence_getElem?_of_creation_of_le
    {s : WalkPath} {m k n N : ℕ} (hm : 0 < m) (hk : 0 < k)
    (hcreation : ThresholdCreation s m k n) (hnN : n ≤ N) :
    (thresholdHitSequence m
      (finitePathList (pathPrefix s N)))[k - 1]? = some (s n) := by
  have hdata := thresholdHitSequence_at_creation_all hm hk hcreation
  have hp := thresholdHitSequence_prefix (m := m)
    (finitePathList_prefix_of_le s hnN)
  obtain ⟨tail, htail⟩ := hp
  rw [← htail, List.getElem?_append_left (by rw [hdata.1]; omega)]
  rw [← hdata.1, ← List.getLast?_eq_getElem?, hdata.2]

theorem filter_thresholdHitSequenceAux (m : ℕ) (P : α → Bool)
    (seen p : List α) :
    (thresholdHitSequenceAux m seen p).filter P =
      thresholdHitSequenceAux m (seen.filter P) (p.filter P) := by
  induction p generalizing seen with
  | nil => rfl
  | cons x xs ih =>
      by_cases hx : P x = true
      · have hc : (seen.filter P).count x = seen.count x :=
          List.count_filter hx
        by_cases hm : seen.count x + 1 = m
        · simp [thresholdHitSequenceAux, hx, hc, hm, ih, List.filter_append]
        · simp [thresholdHitSequenceAux, hx, hc, hm, ih, List.filter_append]
      · by_cases hm : seen.count x + 1 = m
        · simp [thresholdHitSequenceAux, hx, hm, ih, List.filter_append]
        · simp [thresholdHitSequenceAux, hx, hm, ih, List.filter_append]

theorem mem_thresholdHitSequenceAux_count_le (m : ℕ) (seen p : List α)
    {y : α} (hy : y ∈ thresholdHitSequenceAux m seen p) :
    m ≤ (seen ++ p).count y := by
  induction p generalizing seen with
  | nil => simp [thresholdHitSequenceAux] at hy
  | cons x xs ih =>
      by_cases hm : seen.count x + 1 = m
      · simp only [thresholdHitSequenceAux, if_pos hm, List.mem_cons] at hy
        rcases hy with rfl | hy
        · simp only [List.count_append, List.count_cons, beq_self_eq_true,
            if_true]
          omega
        · have h := ih (seen ++ [x]) hy
          simpa only [List.append_assoc, List.singleton_append] using h
      · simp only [thresholdHitSequenceAux, if_neg hm] at hy
        have h := ih (seen ++ [x]) hy
        simpa only [List.append_assoc, List.singleton_append] using h

theorem thresholdHitSequence_filter_eq_self_of_outside_lt
    (m : ℕ) (P : α → Bool) (p : List α)
    (hout : ∀ y, P y = false → p.count y < m) :
    (thresholdHitSequence m p).filter P = thresholdHitSequence m p := by
  apply List.filter_eq_self.mpr
  intro y hy
  by_contra hnot
  have hfalse : P y = false := Bool.eq_false_of_not_eq_true hnot
  have hle := mem_thresholdHitSequenceAux_count_le m [] p hy
  simp only [List.nil_append] at hle
  exact (Nat.not_le_of_gt (hout y hfalse)) hle

theorem thresholdHitSequence_eq_of_filter_eq_of_outside_lt
    (m : ℕ) (P : α → Bool) (p p' : List α)
    (hfilter : p.filter P = p'.filter P)
    (hout : ∀ y, P y = false → p.count y < m)
    (hout' : ∀ y, P y = false → p'.count y < m) :
    thresholdHitSequence m p = thresholdHitSequence m p' := by
  have hs : (thresholdHitSequenceAux m [] p).filter P =
      thresholdHitSequenceAux m [] p := by
    simpa only [thresholdHitSequence] using
      thresholdHitSequence_filter_eq_self_of_outside_lt m P p hout
  have hs' : (thresholdHitSequenceAux m [] p').filter P =
      thresholdHitSequenceAux m [] p' := by
    simpa only [thresholdHitSequence] using
      thresholdHitSequence_filter_eq_self_of_outside_lt m P p' hout'
  unfold thresholdHitSequence
  calc
    _ = (thresholdHitSequenceAux m [] p).filter P := hs.symm
    _ = thresholdHitSequenceAux m (List.filter P ([] : List α)) (p.filter P) :=
      filter_thresholdHitSequenceAux m P [] p
    _ = thresholdHitSequenceAux m (List.filter P ([] : List α)) (p'.filter P) := by
      rw [hfilter]
    _ = (thresholdHitSequenceAux m [] p').filter P :=
      (filter_thresholdHitSequenceAux m P [] p').symm
    _ = _ := hs'

theorem walkPoint_eq_of_pathPrefix_eq {s s' : WalkPath} {N n : ℕ}
    (hp : pathPrefix s N = pathPrefix s' N) (hn : n ≤ N) :
    s n = s' n := by
  exact congrFun hp ⟨n, Nat.lt_succ_of_le hn⟩

theorem thresholdCount_eq_of_pathPrefix_eq {s s' : WalkPath} {N n m : ℕ}
    (hp : pathPrefix s N = pathPrefix s' N) (hn : n ≤ N) :
    thresholdCount s n m = thresholdCount s' n m := by
  have hpn : pathPrefix s n = pathPrefix s' n := by
    funext j
    exact walkPoint_eq_of_pathPrefix_eq hp
      ((Nat.lt_succ_iff.mp j.isLt).trans hn)
  unfold thresholdCount thresholdSites visitedSites localTime
  rw [hpn]

theorem thresholdCreation_iff_of_pathPrefix_eq {s s' : WalkPath}
    {N n m rank : ℕ} (hp : pathPrefix s N = pathPrefix s' N)
    (hn : n ≤ N) :
    ThresholdCreation s m rank n ↔ ThresholdCreation s' m rank n := by
  constructor
  · rintro ⟨hnow, hprior⟩
    refine ⟨?_, ?_⟩
    · rwa [← thresholdCount_eq_of_pathPrefix_eq hp hn]
    · intro q hqn
      rw [← thresholdCount_eq_of_pathPrefix_eq hp (hqn.le.trans hn)]
      exact hprior q hqn
  · rintro ⟨hnow, hprior⟩
    refine ⟨?_, ?_⟩
    · rwa [thresholdCount_eq_of_pathPrefix_eq hp hn]
    · intro q hqn
      rw [thresholdCount_eq_of_pathPrefix_eq hp (hqn.le.trans hn)]
      exact hprior q hqn

theorem firstCreationStage_iff_of_pathPrefix_eq_of_creation
    {s s' : WalkPath} {N m : ℕ}
    (hp : pathPrefix s N = pathPrefix s' N)
    (hfinal : ThresholdCreation s m 1 N)
    (hfinal' : ThresholdCreation s' m 1 N) :
    s ∈ HLOZStoppedProductRefinement.firstCreationStage m ↔
      s' ∈ HLOZStoppedProductRefinement.firstCreationStage m := by
  simp only [HLOZStoppedProductRefinement.firstCreationStage, Set.mem_iUnion,
    thresholdCreationSet, Set.mem_setOf_eq]
  constructor
  · rintro ⟨n, hn⟩
    have hnN : n = N := HLOZSpatialAdapter.thresholdCreation_time_unique hn hfinal
    subst n
    exact ⟨N, hfinal'⟩
  · rintro ⟨n, hn⟩
    have hnN : n = N := HLOZSpatialAdapter.thresholdCreation_time_unique hn hfinal'
    subst n
    exact ⟨N, hfinal⟩

theorem firstTransitionEvent_iff_of_pathPrefix_eq_of_creation
    {s s' : WalkPath} {N m : ℕ} (t : Tilings.Tiling)
    (a : (GapScale × GapScale) × GapScale)
    (hp : pathPrefix s N = pathPrefix s' N)
    (hfinal : ThresholdCreation s m 2 N)
    (hfinal' : ThresholdCreation s' m 2 N) :
    s ∈ firstTransitionEvent t m a ↔ s' ∈ firstTransitionEvent t m a := by
  have transfer : ∀ {u u' : WalkPath}, pathPrefix u N = pathPrefix u' N →
      ThresholdCreation u m 2 N →
      u ∈ firstTransitionEvent t m a →
      u' ∈ firstTransitionEvent t m a := by
    intro u u' hprefix hlast hu
    simp only [firstTransitionEvent, Set.mem_iUnion] at hu ⊢
    rcases hu with ⟨n₁, n₂, hu⟩
    have hn₂ : n₂ = N :=
      HLOZSpatialAdapter.thresholdCreation_time_unique hu.2.1 hlast
    subst n₂
    have hn₁N : n₁ ≤ N :=
      (creation_time_lt (by omega) (by omega) (by omega) hu.1 hlast).le
    refine ⟨n₁, N, ?_⟩
    exact ⟨(thresholdCreation_iff_of_pathPrefix_eq hprefix hn₁N).mp hu.1,
      (thresholdCreation_iff_of_pathPrefix_eq hprefix (Nat.le_refl N)).mp hlast,
      (thresholdCount_eq_of_pathPrefix_eq hprefix (Nat.le_refl N)) ▸ hu.2.2.1,
      (walkPoint_eq_of_pathPrefix_eq hprefix hn₁N) ▸
        (walkPoint_eq_of_pathPrefix_eq hprefix (Nat.le_refl N)) ▸ hu.2.2.2⟩
  constructor
  · exact transfer hp hfinal
  · exact transfer hp.symm hfinal'

theorem secondTransitionEvent_iff_of_pathPrefix_eq_of_creation
    {s s' : WalkPath} {N m : ℕ} (t : Tilings.Tiling)
    (a : (GapScale × GapScale) × GapScale)
    (hp : pathPrefix s N = pathPrefix s' N)
    (hfinal : ThresholdCreation s m 3 N)
    (hfinal' : ThresholdCreation s' m 3 N) :
    s ∈ secondTransitionEvent t m a ↔ s' ∈ secondTransitionEvent t m a := by
  have transfer : ∀ {u u' : WalkPath}, pathPrefix u N = pathPrefix u' N →
      ThresholdCreation u m 3 N →
      u ∈ secondTransitionEvent t m a →
      u' ∈ secondTransitionEvent t m a := by
    intro u u' hprefix hlast hu
    simp only [secondTransitionEvent, Set.mem_iUnion] at hu ⊢
    rcases hu with ⟨n₁, n₂, n₃, hu⟩
    have hn₃ : n₃ = N :=
      HLOZSpatialAdapter.thresholdCreation_time_unique hu.2.2.1 hlast
    subst n₃
    have hn₁N : n₁ ≤ N :=
      (creation_time_lt (by omega) (by omega) (by omega) hu.1 hlast).le
    have hn₂N : n₂ ≤ N :=
      (creation_time_lt (by omega) (by omega) (by omega) hu.2.1 hlast).le
    refine ⟨n₁, n₂, N, ?_⟩
    exact ⟨(thresholdCreation_iff_of_pathPrefix_eq hprefix hn₁N).mp hu.1,
      (thresholdCreation_iff_of_pathPrefix_eq hprefix hn₂N).mp hu.2.1,
      (thresholdCreation_iff_of_pathPrefix_eq hprefix (Nat.le_refl N)).mp hlast,
      (thresholdCount_eq_of_pathPrefix_eq hprefix (Nat.le_refl N)) ▸ hu.2.2.2.1,
      (walkPoint_eq_of_pathPrefix_eq hprefix hn₁N) ▸
        (walkPoint_eq_of_pathPrefix_eq hprefix hn₂N) ▸
        (walkPoint_eq_of_pathPrefix_eq hprefix (Nat.le_refl N)) ▸ hu.2.2.2.2⟩
  constructor
  · exact transfer hp hfinal
  · exact transfer hp.symm hfinal'

noncomputable section

open TilingLazyDecomposition TilingSpatialInsertionFiber
open TilingCappedMarginalization TilingInsertedLocalTime
open TilingInsertionTerminalInvariant TilingStoppedAcceptanceFactorization
open TilingFavoriteTraceSupport
open PreStoppingFiber StoppedInsertion VariableStoppedFiber SpatialInsertionFiber

theorem pathPrefix_eq_canonical_of_mem_tilingStoppedInsertionAtom
    {τ : StepPath → ℕ} {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (q : Fin (i + 1) → ℕ)
    (tail : List Direction) (omega : StepPath)
    (homega : omega ∈ tilingStoppedInsertionAtom τ t x r q tail) :
    let v := tilingInsertionPrefixList t x r q tail
    pathPrefix (trajectory omega) v.length =
      pathPrefix
        (trajectory (extendPrefix (directionVectorOfList v))) v.length := by
  let v := tilingInsertionPrefixList t x r q tail
  change τ omega = v.length ∧ incrementPrefixList v.length omega = v at homega
  have hstep : stepPrefix v.length omega = directionVectorOfList v :=
    (incrementPrefixList_eq_iff_stepPrefix_eq_directionVector omega v).mp
      homega.2
  calc
    pathPrefix (trajectory omega) v.length =
        trajectoryPrefix (stepPrefix v.length omega) :=
      (trajectoryPrefix_stepPrefix omega v.length).symm
    _ = trajectoryPrefix (directionVectorOfList v) := by rw [hstep]
    _ = pathPrefix
        (trajectory (extendPrefix (directionVectorOfList v))) v.length :=
      by
        simpa only [stepPrefix_extendPrefix] using
          trajectoryPrefix_stepPrefix
            (extendPrefix (directionVectorOfList v)) v.length

theorem firstCreationStage_iff_canonical_of_mem_tilingStoppedInsertionAtom
    {i : ℕ} (t : DominoTiling) (m cutoff : ℕ)
    (r : TilingRetainedWord t (0, 0) i) (q : Fin (i + 1) → ℕ)
    (tail : BoundaryTail)
    (haccepted : TilingStoppingAccepted (truncatedLevelTime m 1 cutoff)
      t (0, 0) r q tail.1)
    (hlt : (tilingInsertionPrefixList t (0, 0) r q tail.1).length < cutoff)
    (omega : StepPath)
    (homega : omega ∈ tilingStoppedInsertionAtom
      (truncatedLevelTime m 1 cutoff) t (0, 0) r q tail.1) :
    trajectory omega ∈ HLOZStoppedProductRefinement.firstCreationStage m ↔
      let v := tilingInsertionPrefixList t (0, 0) r q tail.1
      trajectory (extendPrefix (directionVectorOfList v)) ∈
        HLOZStoppedProductRefinement.firstCreationStage m := by
  let v := tilingInsertionPrefixList t (0, 0) r q tail.1
  let s := trajectory (extendPrefix (directionVectorOfList v))
  have hp : pathPrefix (trajectory omega) v.length = pathPrefix s v.length :=
    pathPrefix_eq_canonical_of_mem_tilingStoppedInsertionAtom
      t (0, 0) r q tail.1 omega homega
  have hcanonical : ThresholdCreation s m 1 v.length :=
    (tilingStoppingAccepted_truncatedLevelTime_iff_thresholdCreation
      m 1 cutoff t (0, 0) r q tail hlt).mp haccepted
  have hatom : truncatedLevelTime m 1 cutoff omega = v.length := by
    exact homega.1
  have hactual : ThresholdCreation (trajectory omega) m 1 v.length :=
    (truncatedLevelTime_eq_iff_thresholdCreation_of_lt_cutoff
      m 1 cutoff v.length omega hlt).mp hatom
  exact firstCreationStage_iff_of_pathPrefix_eq_of_creation
    hp hactual hcanonical

theorem firstTransitionEvent_iff_canonical_of_mem_tilingStoppedInsertionAtom
    {i : ℕ} (t : DominoTiling) (m cutoff : ℕ)
    (a : (GapScale × GapScale) × GapScale)
    (r : TilingRetainedWord t (0, 0) i) (q : Fin (i + 1) → ℕ)
    (tail : BoundaryTail)
    (haccepted : TilingStoppingAccepted (truncatedLevelTime m 2 cutoff)
      t (0, 0) r q tail.1)
    (hlt : (tilingInsertionPrefixList t (0, 0) r q tail.1).length < cutoff)
    (omega : StepPath)
    (homega : omega ∈ tilingStoppedInsertionAtom
      (truncatedLevelTime m 2 cutoff) t (0, 0) r q tail.1) :
    trajectory omega ∈ firstTransitionEvent t m a ↔
      let v := tilingInsertionPrefixList t (0, 0) r q tail.1
      trajectory (extendPrefix (directionVectorOfList v)) ∈
        firstTransitionEvent t m a := by
  let v := tilingInsertionPrefixList t (0, 0) r q tail.1
  let s := trajectory (extendPrefix (directionVectorOfList v))
  have hp : pathPrefix (trajectory omega) v.length = pathPrefix s v.length :=
    pathPrefix_eq_canonical_of_mem_tilingStoppedInsertionAtom
      t (0, 0) r q tail.1 omega homega
  have hcanonical : ThresholdCreation s m 2 v.length :=
    (tilingStoppingAccepted_truncatedLevelTime_iff_thresholdCreation
      m 2 cutoff t (0, 0) r q tail hlt).mp haccepted
  have hactual : ThresholdCreation (trajectory omega) m 2 v.length :=
    (truncatedLevelTime_eq_iff_thresholdCreation_of_lt_cutoff
      m 2 cutoff v.length omega hlt).mp homega.1
  exact firstTransitionEvent_iff_of_pathPrefix_eq_of_creation
    t a hp hactual hcanonical

theorem secondTransitionEvent_iff_canonical_of_mem_tilingStoppedInsertionAtom
    {i : ℕ} (t : DominoTiling) (m cutoff : ℕ)
    (a : (GapScale × GapScale) × GapScale)
    (r : TilingRetainedWord t (0, 0) i) (q : Fin (i + 1) → ℕ)
    (tail : BoundaryTail)
    (haccepted : TilingStoppingAccepted (truncatedLevelTime m 3 cutoff)
      t (0, 0) r q tail.1)
    (hlt : (tilingInsertionPrefixList t (0, 0) r q tail.1).length < cutoff)
    (omega : StepPath)
    (homega : omega ∈ tilingStoppedInsertionAtom
      (truncatedLevelTime m 3 cutoff) t (0, 0) r q tail.1) :
    trajectory omega ∈ secondTransitionEvent t m a ↔
      let v := tilingInsertionPrefixList t (0, 0) r q tail.1
      trajectory (extendPrefix (directionVectorOfList v)) ∈
        secondTransitionEvent t m a := by
  let v := tilingInsertionPrefixList t (0, 0) r q tail.1
  let s := trajectory (extendPrefix (directionVectorOfList v))
  have hp : pathPrefix (trajectory omega) v.length = pathPrefix s v.length :=
    pathPrefix_eq_canonical_of_mem_tilingStoppedInsertionAtom
      t (0, 0) r q tail.1 omega homega
  have hcanonical : ThresholdCreation s m 3 v.length :=
    (tilingStoppingAccepted_truncatedLevelTime_iff_thresholdCreation
      m 3 cutoff t (0, 0) r q tail hlt).mp haccepted
  have hactual : ThresholdCreation (trajectory omega) m 3 v.length :=
    (truncatedLevelTime_eq_iff_thresholdCreation_of_lt_cutoff
      m 3 cutoff v.length omega hlt).mp homega.1
  exact secondTransitionEvent_iff_of_pathPrefix_eq_of_creation
    t a hp hactual hcanonical

theorem tilingInsertionPrefixList_pos_of_accepted_one_lt
    {i : ℕ} (t : DominoTiling) (m k cutoff : ℕ)
    (hm : 1 < m) (hk : 0 < k)
    (r : TilingRetainedWord t (0, 0) i) (q : Fin (i + 1) → ℕ)
    (tail : BoundaryTail)
    (haccepted : TilingStoppingAccepted (truncatedLevelTime m k cutoff)
      t (0, 0) r q tail.1)
    (hlt : (tilingInsertionPrefixList t (0, 0) r q tail.1).length < cutoff) :
    0 < (tilingInsertionPrefixList t (0, 0) r q tail.1).length := by
  let v := tilingInsertionPrefixList t (0, 0) r q tail.1
  have hcreation : ThresholdCreation
      (trajectory (extendPrefix (directionVectorOfList v))) m k v.length :=
    (tilingStoppingAccepted_truncatedLevelTime_iff_thresholdCreation
      m k cutoff t (0, 0) r q tail hlt).mp haccepted
  have hcount := thresholdCount_eq_of_creation hk hcreation
  by_contra hnot
  have hv : v.length = 0 := Nat.eq_zero_of_not_pos hnot
  have hvnil : v = [] := List.length_eq_zero_iff.mp hv
  change thresholdCount
      (trajectory (extendPrefix (directionVectorOfList v))) v.length m = k at hcount
  simp [hvnil, PreStoppingFiber.thresholdCount_trajectory_zero_time,
    show ¬m ≤ 1 by omega] at hcount
  omega

theorem tilingInsertionPrefixList_pos_of_distinguished_eq_of_accepted
    {i cap : ℕ} (t : DominoTiling) (m k cutoff : ℕ)
    (hm : 1 < m) (hk : 0 < k)
    (r : TilingRetainedWord t (0, 0) i) (tail : BoundaryTail)
    (D : Finset Point) (q q' : TilingCappedCoordinates i cap)
    (hbase :
      let v := tilingInsertionPrefixList t (0, 0) r
        (fun j ↦ (q j : ℕ)) tail.1
      tilingBase t
          (trajectory (extendPrefix (directionVectorOfList v)) v.length) ∈ D)
    (hdist : (splitTilingCoordinatesEquiv t (0, 0) r D q).1 =
      (splitTilingCoordinatesEquiv t (0, 0) r D q').1)
    (haccepted : TilingStoppingAccepted (truncatedLevelTime m k cutoff)
      t (0, 0) r (fun j ↦ (q j : ℕ)) tail.1)
    (hlt : (tilingInsertionPrefixList t (0, 0) r
      (fun j ↦ (q j : ℕ)) tail.1).length < cutoff) :
    0 < (tilingInsertionPrefixList t (0, 0) r
      (fun j ↦ (q' j : ℕ)) tail.1).length := by
  let qNat : Fin (i + 1) → ℕ := fun j ↦ (q j : ℕ)
  let qNat' : Fin (i + 1) → ℕ := fun j ↦ (q' j : ℕ)
  let v := tilingInsertionPrefixList t (0, 0) r qNat tail.1
  let v' := tilingInsertionPrefixList t (0, 0) r qNat' tail.1
  let s := trajectory (extendPrefix (directionVectorOfList v))
  let s' := trajectory (extendPrefix (directionVectorOfList v'))
  let terminal := tilingInsertionTerminal t r qNat tail
  have hpos := tilingInsertionPrefixList_pos_of_accepted_one_lt
    t m k cutoff hm hk r qNat tail haccepted hlt
  have hterminal :=
    (tilingStoppingAccepted_truncatedLevelTime_iff_terminal
      m k cutoff t (0, 0) r qNat tail (by omega) hk hpos hlt).mp haccepted
  have hterminal' : tilingInsertionTerminal t r qNat' tail = terminal := by
    exact (tilingInsertionTerminal_eq_of_coordinates t r qNat qNat' tail).symm
  have hpath : finitePathList (pathPrefix s v.length) =
      tilingPrefixPointPath (0, 0)
        (tilingInsertGapVector t (0, 0) r qNat) terminal := by
    exact finitePathList_tilingInsertionPrefix t r qNat tail
  have hpath' : finitePathList (pathPrefix s' v'.length) =
      tilingPrefixPointPath (0, 0)
        (tilingInsertGapVector t (0, 0) r qNat') terminal := by
    rw [← hterminal']
    exact finitePathList_tilingInsertionPrefix t r qNat' tail
  have hend : s v.length = s' v'.length :=
    canonical_tilingInsertion_endpoint_eq_of_coordinates
      t r qNat qNat' tail
  have hlocalList := tilingPrefixLocalTime_eq_of_distinguished_eq
      t (0, 0) r terminal D q q' hdist (s v.length) hbase
  have hlocal' : localTime s' v'.length (s' v'.length) = m := by
    rw [← hend]
    calc
      localTime s' v'.length (s v.length) =
          listLocalTime (finitePathList (pathPrefix s' v'.length))
            (s v.length) := localTime_eq_listLocalTime s' v'.length _
      _ = listLocalTime
          (tilingPrefixPointPath (0, 0)
            (tilingInsertGapVector t (0, 0) r qNat') terminal)
            (s v.length) := congrArg (fun p ↦ listLocalTime p (s v.length)) hpath'
      _ = listLocalTime
          (tilingPrefixPointPath (0, 0)
            (tilingInsertGapVector t (0, 0) r qNat) terminal)
            (s v.length) := hlocalList.symm
      _ = listLocalTime (finitePathList (pathPrefix s v.length))
            (s v.length) := congrArg (fun p ↦ listLocalTime p (s v.length)) hpath.symm
      _ = localTime s v.length (s v.length) :=
        (localTime_eq_listLocalTime s v.length _).symm
      _ = m := hterminal.2
  by_contra hnot
  have hv' : v'.length = 0 := Nat.eq_zero_of_not_pos hnot
  have hzero : localTime s' v'.length (s' v'.length) = 1 := by
    rw [hv']
    simp [localTime, localTimePrefix, pathPrefix]
  omega

theorem tilingStoppingAccepted_iff_of_distinguished_eq_of_truncated_one_lt
    {i cap : ℕ} (t : DominoTiling) (m k cutoff : ℕ)
    (hm : 1 < m) (hk : 0 < k)
    (r : TilingRetainedWord t (0, 0) i) (tail : BoundaryTail)
    (D : Finset Point) (q q' : TilingCappedCoordinates i cap)
    (hbase :
      let v := tilingInsertionPrefixList t (0, 0) r
        (fun j ↦ (q j : ℕ)) tail.1
      tilingBase t
          (trajectory (extendPrefix (directionVectorOfList v)) v.length) ∈ D)
    (hdist : (splitTilingCoordinatesEquiv t (0, 0) r D q).1 =
      (splitTilingCoordinatesEquiv t (0, 0) r D q').1)
    (htrunc : TilingDominoTruncation t (0, 0) r
      (tilingInsertionTerminal t r (fun j ↦ (q j : ℕ)) tail) m D
      (fun j ↦ (q j : ℕ)))
    (htrunc' : TilingDominoTruncation t (0, 0) r
      (tilingInsertionTerminal t r (fun j ↦ (q j : ℕ)) tail) m D
      (fun j ↦ (q' j : ℕ)))
    (hlt : (tilingInsertionPrefixList t (0, 0) r
      (fun j ↦ (q j : ℕ)) tail.1).length < cutoff)
    (hlt' : (tilingInsertionPrefixList t (0, 0) r
      (fun j ↦ (q' j : ℕ)) tail.1).length < cutoff) :
    TilingStoppingAccepted (truncatedLevelTime m k cutoff)
        t (0, 0) r (fun j ↦ (q j : ℕ)) tail.1 ↔
      TilingStoppingAccepted (truncatedLevelTime m k cutoff)
        t (0, 0) r (fun j ↦ (q' j : ℕ)) tail.1 := by
  constructor
  · intro haccepted
    have hpos := tilingInsertionPrefixList_pos_of_accepted_one_lt
      t m k cutoff hm hk r (fun j ↦ (q j : ℕ)) tail haccepted hlt
    have hpos' := tilingInsertionPrefixList_pos_of_distinguished_eq_of_accepted
      t m k cutoff hm hk r tail D q q' hbase hdist haccepted hlt
    exact (tilingStoppingAccepted_iff_of_distinguished_eq_of_truncated_canonical
        t m k cutoff (by omega) hk r tail D q q' hbase hdist htrunc htrunc'
        hpos hpos' hlt hlt').mp haccepted
  · intro haccepted'
    have hpos' := tilingInsertionPrefixList_pos_of_accepted_one_lt
      t m k cutoff hm hk r (fun j ↦ (q' j : ℕ)) tail haccepted' hlt'
    have hbase' :
        let v' := tilingInsertionPrefixList t (0, 0) r
          (fun j ↦ (q' j : ℕ)) tail.1
        tilingBase t
            (trajectory (extendPrefix (directionVectorOfList v')) v'.length) ∈ D := by
      dsimp only
      rw [← canonical_tilingInsertion_endpoint_eq_of_coordinates
        t r (fun j ↦ (q j : ℕ)) (fun j ↦ (q' j : ℕ)) tail]
      exact hbase
    have hpos := tilingInsertionPrefixList_pos_of_distinguished_eq_of_accepted
      t m k cutoff hm hk r tail D q' q hbase' hdist.symm haccepted' hlt'
    exact (tilingStoppingAccepted_iff_of_distinguished_eq_of_truncated_canonical
        t m k cutoff (by omega) hk r tail D q q' hbase hdist htrunc htrunc'
        hpos hpos' hlt hlt').mpr haccepted'

theorem thresholdHitSequence_tilingPrefixPointPath_eq_of_distinguished_eq
    {i cap : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (terminal : Option Point) (m : ℕ)
    (D : Finset Point) (q q' : TilingCappedCoordinates i cap)
    (hdist : (splitTilingCoordinatesEquiv t x r D q).1 =
      (splitTilingCoordinatesEquiv t x r D q').1)
    (hout : ∀ y, tilingBase t y ∉ D →
      listLocalTime
        (tilingPrefixPointPath x
          (tilingInsertGapVector t x r (fun j ↦ (q j : ℕ))) terminal) y < m)
    (hout' : ∀ y, tilingBase t y ∉ D →
      listLocalTime
        (tilingPrefixPointPath x
          (tilingInsertGapVector t x r (fun j ↦ (q' j : ℕ))) terminal) y < m) :
    thresholdHitSequence m
        (tilingPrefixPointPath x
          (tilingInsertGapVector t x r (fun j ↦ (q j : ℕ))) terminal) =
      thresholdHitSequence m
        (tilingPrefixPointPath x
          (tilingInsertGapVector t x r (fun j ↦ (q' j : ℕ))) terminal) := by
  apply thresholdHitSequence_eq_of_filter_eq_of_outside_lt
      m (pointInTilingBases t D)
  · exact filter_tilingPrefixPointPath_tilingInsertGapVector_eq
      t x r terminal D q q' hdist
  · intro y hy
    change listLocalTime _ y < m
    apply hout y
    simpa [pointInTilingBases] using hy
  · intro y hy
    change listLocalTime _ y < m
    apply hout' y
    simpa [pointInTilingBases] using hy

theorem thresholdHitSequence_canonical_tilingInsertionPrefix_eq
    {i cap : ℕ} (t : DominoTiling) (m : ℕ)
    (r : TilingRetainedWord t (0, 0) i) (tail : BoundaryTail)
    (D : Finset Point) (q q' : TilingCappedCoordinates i cap)
    (hdist : (splitTilingCoordinatesEquiv t (0, 0) r D q).1 =
      (splitTilingCoordinatesEquiv t (0, 0) r D q').1)
    (hout : ∀ y, tilingBase t y ∉ D →
      let v := tilingInsertionPrefixList t (0, 0) r
        (fun j ↦ (q j : ℕ)) tail.1
      localTime (trajectory (extendPrefix (directionVectorOfList v)))
        v.length y < m)
    (hout' : ∀ y, tilingBase t y ∉ D →
      let v' := tilingInsertionPrefixList t (0, 0) r
        (fun j ↦ (q' j : ℕ)) tail.1
      localTime (trajectory (extendPrefix (directionVectorOfList v')))
        v'.length y < m) :
    let v := tilingInsertionPrefixList t (0, 0) r
      (fun j ↦ (q j : ℕ)) tail.1
    let v' := tilingInsertionPrefixList t (0, 0) r
      (fun j ↦ (q' j : ℕ)) tail.1
    thresholdHitSequence m
        (finitePathList (pathPrefix
          (trajectory (extendPrefix (directionVectorOfList v))) v.length)) =
      thresholdHitSequence m
        (finitePathList (pathPrefix
          (trajectory (extendPrefix (directionVectorOfList v'))) v'.length)) := by
  let qNat : Fin (i + 1) → ℕ := fun j ↦ (q j : ℕ)
  let qNat' : Fin (i + 1) → ℕ := fun j ↦ (q' j : ℕ)
  let v := tilingInsertionPrefixList t (0, 0) r qNat tail.1
  let v' := tilingInsertionPrefixList t (0, 0) r qNat' tail.1
  let terminal := tilingInsertionTerminal t r qNat tail
  have hterminal' : tilingInsertionTerminal t r qNat' tail = terminal := by
    exact (tilingInsertionTerminal_eq_of_coordinates t r qNat qNat' tail).symm
  have hpath : finitePathList (pathPrefix
      (trajectory (extendPrefix (directionVectorOfList v))) v.length) =
      tilingPrefixPointPath (0, 0) (tilingInsertGapVector t (0, 0) r qNat)
        terminal := by
    exact finitePathList_tilingInsertionPrefix t r qNat tail
  have hpath' : finitePathList (pathPrefix
      (trajectory (extendPrefix (directionVectorOfList v'))) v'.length) =
      tilingPrefixPointPath (0, 0) (tilingInsertGapVector t (0, 0) r qNat')
        terminal := by
    rw [← hterminal']
    exact finitePathList_tilingInsertionPrefix t r qNat' tail
  change thresholdHitSequence m
      (finitePathList (pathPrefix
        (trajectory (extendPrefix (directionVectorOfList v))) v.length)) =
    thresholdHitSequence m
      (finitePathList (pathPrefix
        (trajectory (extendPrefix (directionVectorOfList v'))) v'.length))
  rw [hpath, hpath']
  apply thresholdHitSequence_tilingPrefixPointPath_eq_of_distinguished_eq
    t (0, 0) r terminal m D q q' hdist
  · intro y hy
    rw [← hpath, ← localTime_eq_listLocalTime]
    exact hout y hy
  · intro y hy
    rw [← hpath', ← localTime_eq_listLocalTime]
    exact hout' y hy

theorem canonical_creation_location_eq_of_distinguished_eq
    {i cap : ℕ} (t : DominoTiling) (m rank : ℕ)
    (hm : 0 < m) (hrank : 0 < rank)
    (r : TilingRetainedWord t (0, 0) i) (tail : BoundaryTail)
    (D : Finset Point) (q q' : TilingCappedCoordinates i cap)
    (hdist : (splitTilingCoordinatesEquiv t (0, 0) r D q).1 =
      (splitTilingCoordinatesEquiv t (0, 0) r D q').1)
    (hout : ∀ y, tilingBase t y ∉ D →
      let v := tilingInsertionPrefixList t (0, 0) r
        (fun j ↦ (q j : ℕ)) tail.1
      localTime (trajectory (extendPrefix (directionVectorOfList v)))
        v.length y < m)
    (hout' : ∀ y, tilingBase t y ∉ D →
      let v' := tilingInsertionPrefixList t (0, 0) r
        (fun j ↦ (q' j : ℕ)) tail.1
      localTime (trajectory (extendPrefix (directionVectorOfList v')))
        v'.length y < m)
    {n n' : ℕ}
    (hcreation :
      let v := tilingInsertionPrefixList t (0, 0) r
        (fun j ↦ (q j : ℕ)) tail.1
      ThresholdCreation (trajectory (extendPrefix (directionVectorOfList v)))
        m rank n)
    (hcreation' :
      let v' := tilingInsertionPrefixList t (0, 0) r
        (fun j ↦ (q' j : ℕ)) tail.1
      ThresholdCreation (trajectory (extendPrefix (directionVectorOfList v')))
        m rank n')
    (hn : n ≤ (tilingInsertionPrefixList t (0, 0) r
      (fun j ↦ (q j : ℕ)) tail.1).length)
    (hn' : n' ≤ (tilingInsertionPrefixList t (0, 0) r
      (fun j ↦ (q' j : ℕ)) tail.1).length) :
    let v := tilingInsertionPrefixList t (0, 0) r
      (fun j ↦ (q j : ℕ)) tail.1
    let v' := tilingInsertionPrefixList t (0, 0) r
      (fun j ↦ (q' j : ℕ)) tail.1
    trajectory (extendPrefix (directionVectorOfList v)) n =
      trajectory (extendPrefix (directionVectorOfList v')) n' := by
  let v := tilingInsertionPrefixList t (0, 0) r
    (fun j ↦ (q j : ℕ)) tail.1
  let v' := tilingInsertionPrefixList t (0, 0) r
    (fun j ↦ (q' j : ℕ)) tail.1
  let s := trajectory (extendPrefix (directionVectorOfList v))
  let s' := trajectory (extendPrefix (directionVectorOfList v'))
  have hseq := thresholdHitSequence_canonical_tilingInsertionPrefix_eq
    t m r tail D q q' hdist hout hout'
  have hloc := thresholdHitSequence_getElem?_of_creation_of_le
    hm hrank hcreation hn
  have hloc' := thresholdHitSequence_getElem?_of_creation_of_le
    hm hrank hcreation' hn'
  rw [hseq] at hloc
  exact Option.some.inj (hloc.symm.trans hloc')

end

end Erdos1165.TilingDistinguishedTraceInvariant
