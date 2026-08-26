import ErdosProblems.Erdos118.Reused591.GameInvariant
import ErdosProblems.Erdos118.Reused591.LegalMetadata

namespace Erdos118.Reused591

/-!
# Actual cursor continuations along game replies

Both response commands yield legal atomic runs on the selected word.
Every new coordinate belongs to the response input. Lifting this fact
to history paths preserves the original labels and places every new
coordinate strictly above the earlier history's freshness bound.
-/

namespace Erdos591.Positive.Game

namespace LabeledWord

theorem zero_run_legal (D : ResponseParser LabeledWord)
    (hstep : ∀ w n, D.step w n = w.read ∅ n)
    {w v : LabeledWord} {xs : List ℕ} (h : D.run w xs = some v) :
    LegalRun w (xs.map fun n => (∅, n)) v := by
  induction xs generalizing w with
  | nil =>
      cases hs : D.stopped w with
      | false => simp [ResponseParser.run, hs] at h
      | true =>
          have heq : w = v := by simpa [ResponseParser.run, hs] using h
          exact heq ▸ LegalRun.nil w
  | cons n xs ih =>
      cases hs : D.stopped w with
      | true => simp [ResponseParser.run, hs] at h
      | false =>
          cases hr : w.read ∅ n with
          | none => simp [ResponseParser.run, hs, hstep, hr] at h
          | some u =>
              have ht : D.run u xs = some v := by
                simpa [ResponseParser.run, hs, hstep, hr] using h
              exact .cons w ∅ n u _ v (allowed_empty (read_nonterminal hr) n) hr (ih ht)

theorem LegalRun.terminal_eq {w v : LabeledWord} {xs : List (Finset ℕ × ℕ)}
    (h : LegalRun w xs v) (hw : w.terminal = true) : v = w := by
  cases h with
  | nil => rfl
  | cons w D n u xs v _ hr _ =>
      have hfalse := read_nonterminal hr
      simp [hw] at hfalse

theorem LegalRun.coordinates_prefix {w v : LabeledWord} {xs : List (Finset ℕ × ℕ)}
    (h : LegalRun w xs v) : List.IsPrefix w.coordinates v.coordinates :=
  ⟨xs.map Prod.snd, (runAtoms_coordinates h.run).symm⟩

theorem LegalRun.relaxed_coordinates_pos {w : LabeledWord} {xs : List (Finset ℕ × ℕ)}
    (h : LegalRun initial xs w) (hr : w.relaxed = true) : 0 < w.coordinates.length := by
  cases xs with
  | nil =>
      have heq := (legalRun_nil_iff initial w).mp h
      simp [← heq, relaxed, initial] at hr
  | cons a xs => simp [runAtoms_coordinates h.run, initial]

theorem LegalRun.marker_coordinates_pos {w : LabeledWord} {xs : List (Finset ℕ × ℕ)}
    (h : LegalRun initial xs w) (hr : w.markerEvent = true) : 0 < w.coordinates.length := by
  cases xs with
  | nil =>
      have heq := (legalRun_nil_iff initial w).mp h
      simp [← heq, markerEvent, initial] at hr
  | cons a xs => simp [runAtoms_coordinates h.run, initial]

theorem marker_not_terminal {w : LabeledWord} (hm : w.markerEvent = true) :
    w.terminal = false := by
  cases hp : w.parser with
  | start => simp [markerEvent, hp] at hm
  | leaves r k => simp [markerEvent, hp] at hm
  | blocks r =>
      cases r with
      | zero => simp [markerEvent, hp] at hm
      | succ r => simp [terminal, hp]

end LabeledWord

namespace Advance

theorem run_legal (w : Unfinished) (d : ℕ) (xs : List ℕ) (v : LabeledWord)
    (hd : w.val.AllowedSize d) (hinc : xs.Pairwise (· < ·))
    (hpos : ∀ x ∈ xs, 0 < x)
    (h : parser.run (.prelude w d []) xs = some (.remainder v)) :
    ∃ as : List (Finset ℕ × ℕ), LabeledWord.LegalRun w.val as v ∧
      ∀ a ∈ as, a.2 ∈ xs := by
  obtain ⟨labels, n, rest, first, last, hxs, hlen, hf, hl, hlast⟩ :=
    run_prelude w d [] xs (.remainder v) h
  have heq : v = last := State.remainder.inj hlast
  subst last
  have hp : (labels ++ n :: rest).Pairwise (· < ·) := hxs ▸ hinc
  have hcard : labels.toFinset.card = d :=
    (List.toFinset_card_of_nodup (List.pairwise_append.mp hp).1.nodup).trans hlen
  have hbound : ∀ i ∈ labels.toFinset, 0 < i ∧ i < n := by
    intro i hi
    have hil : i ∈ labels := List.mem_toFinset.mp hi
    refine ⟨hpos i (hxs ▸ List.mem_append_left _ hil),
      (List.pairwise_append.mp hp).2.2 i hil n (by simp)⟩
  have hr : w.val.read labels.toFinset n = some first := by simpa using hf
  refine ⟨(labels.toFinset, n) :: rest.map (fun x => (∅, x)),
    .cons w.val labels.toFinset n first _ v
      (LabeledWord.allowedLabel_of_size hd hcard hbound) hr
      (LabeledWord.zero_run_legal _ (fun _ _ => rfl) hl), ?_⟩
  intro a ha
  rw [hxs]
  rcases List.mem_cons.mp ha with rfl | ha
  · simp
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
    exact List.mem_append_right _ (List.mem_cons_of_mem n hx)

end Advance

theorem Reply.legal_run {b b' : Board} {r : Request} {u : Finset ℕ}
    (h : Reply b r u b') (hpos : ∀ x ∈ u, 0 < x) (side : Bool) :
    ∃ as : List (Finset ℕ × ℕ),
      LabeledWord.LegalRun (b.get side) as (b'.get side) ∧
      ∀ a ∈ as, a.2 ∈ u := by
  have unchanged (w : LabeledWord) (s : Bool) (hne : side ≠ s) :
      ∃ as : List (Finset ℕ × ℕ),
        LabeledWord.LegalRun (b.get side) as ((b.update s w).get side) ∧
        ∀ a ∈ as, a.2 ∈ u := by
    have heq : (b.update s w).get side = b.get side := by
      cases side <;> cases s <;> simp_all [Board.get, Board.update]
    exact ⟨[], heq ▸ .nil _, by simp⟩
  cases h with
  | finish s u w _ hrun =>
      by_cases heq : side = s
      · subst side
        refine ⟨(u.sort (· ≤ ·)).map (fun n => (∅, n)), ?_, ?_⟩
        · simpa using LabeledWord.zero_run_legal _ (fun _ _ => rfl) hrun
        · intro a ha
          obtain ⟨n, hn, rfl⟩ := List.mem_map.mp ha
          simpa using hn
      · exact unchanged w s heq
  | advance s d u w hlegal hrun =>
      by_cases heq : side = s
      · subst side
        obtain ⟨as, has, hmem⟩ := Advance.run_legal ⟨b.get s, hlegal.1⟩ d
          (u.sort (· ≤ ·)) w hlegal (Finset.sortedLT_sort u).pairwise
          (fun x hx => hpos x (by simpa using hx)) hrun
        exact ⟨as, by simpa using has, fun a ha => by simpa using hmem a ha⟩
      · exact unchanged w s heq

theorem Reply.first_read {b b' : Board} {r : Request} {u : Finset ℕ}
    (h : Reply b r u b') : ∃ D n v as,
      D.card = r.size ∧ (b.get r.side).read D n = some v ∧
      LabeledWord.LegalRun v as (b'.get r.side) := by
  cases h with
  | finish side u w hlegal hrun =>
      have hl := LabeledWord.zero_run_legal _ (fun _ _ => rfl) hrun
      cases hs : u.sort (· ≤ ·) with
      | nil => simp [hs, ResponseParser.run, LabeledWord.finishParser, hlegal] at hrun
      | cons n xs =>
          rw [hs] at hl
          cases hl with
          | cons _ _ _ v _ _ _ hr ht =>
              exact ⟨∅, n, v, _, by simp [Request.size], hr, by simpa using ht⟩
  | advance side d u w hlegal hrun =>
      obtain ⟨labels, n, rest, first, last, hxs, hlen, hf, hl, hlast⟩ :=
        Advance.run_prelude ⟨b.get side, hlegal.1⟩ d [] (u.sort (· ≤ ·)) (.remainder w) hrun
      have heq : w = last := Advance.State.remainder.inj hlast
      subst last
      have hp : (labels ++ n :: rest).Pairwise (· < ·) :=
        hxs ▸ (Finset.sortedLT_sort u).pairwise
      have hcard : labels.toFinset.card = d :=
        (List.toFinset_card_of_nodup (List.pairwise_append.mp hp).1.nodup).trans hlen
      exact ⟨labels.toFinset, n, first, _, hcard, by simpa using hf,
        by simpa using LabeledWord.zero_run_legal _ (fun _ _ => rfl) hl⟩

theorem Reply.coordinates_extend {b b' : Board} {r : Request} {u : Finset ℕ}
    (h : Reply b r u b') :
    ∃ n xs, (b'.get r.side).coordinates = (b.get r.side).coordinates ++ n :: xs := by
  obtain ⟨D, n, v, as, _, hr, ht⟩ := h.first_read
  refine ⟨n, as.map Prod.snd, ?_⟩
  rw [LabeledWord.runAtoms_coordinates ht.run, (LabeledWord.read_spec hr).2]
  simp only [List.append_assoc, List.singleton_append]

theorem Reply.coordinates_extend_input {b b' : Board} {r : Request} {u : Finset ℕ}
    (h : Reply b r u b') (hpos : ∀ x ∈ u, 0 < x) :
    ∃ n ∈ u, ∃ xs,
      (b'.get r.side).coordinates = (b.get r.side).coordinates ++ n :: xs := by
  obtain ⟨n, xs, hc⟩ := h.coordinates_extend
  obtain ⟨as, has, hmem⟩ := h.legal_run hpos r.side
  have hmap : as.map Prod.snd = n :: xs :=
    List.append_cancel_left ((LabeledWord.runAtoms_coordinates has.run).symm.trans hc)
  have hn : n ∈ as.map Prod.snd := by simp [hmap]
  obtain ⟨a, ha, heq⟩ := List.mem_map.mp hn
  exact ⟨n, heq ▸ hmem a ha, xs, hc⟩

theorem Reply.other_eq {b b' : Board} {r : Request} {u : Finset ℕ}
    (h : Reply b r u b') : b'.get (!r.side) = b.get (!r.side) := by
  obtain ⟨w, rfl, _⟩ := h.word_support
  cases r.side <;> rfl

namespace Position

theorem history_last_bound {N : Set ℕ} (p : Concrete.Hist N) (side : Bool) :
    (p.position.board.get side).coordinates.getLastD 0 ≤ p.position.bound := by
  rcases List.mem_cons.mp (List.getLastD_mem_cons
    (l := (p.position.board.get side).coordinates) (a := 0)) with hz | hmem
  · rw [hz]
    exact Nat.zero_le _
  · exact ((history_dataInvariant p).1 _
      (p.position.board.get_support_subset side (LabeledWord.coordinate_mem_support hmem))).2.2

theorem Next.word_extension {N : Set ℕ} {p q : Position} (h : Next N q p)
    (side : Bool) : ∃ as : List (Finset ℕ × ℕ),
      LabeledWord.LegalRun (p.board.get side) as (q.board.get side) ∧
      ∀ a ∈ as, p.bound < a.2 := by
  cases h with
  | request p mode r _ _ _ _ => exact ⟨[], .nil _, by simp⟩
  | reply p r u b _ hr _ hfresh =>
      obtain ⟨as, has, hmem⟩ := hr.legal_run
        (fun x hx => (Nat.zero_le p.bound).trans_lt (hfresh x hx)) side
      exact ⟨as, has, fun a ha => hfresh a.2 (hmem a ha)⟩

end Position

namespace History

theorem Next.position_next {N : Set ℕ} {p q : Concrete.Hist N} (h : Next q p) :
    Position.Next N q.position p.position := by
  obtain ⟨q, hq, rfl⟩ := h
  simpa using hq

theorem reachable_word_extension {N : Set ℕ} {p q : Concrete.Hist N}
    (h : Relation.ReflTransGen (fun p q => Next q p) p q) :
    p.position.bound ≤ q.position.bound ∧ ∀ side,
      ∃ as : List (Finset ℕ × ℕ),
        LabeledWord.LegalRun (p.position.board.get side) as (q.position.board.get side) ∧
        ∀ a ∈ as, p.position.bound < a.2 := by
  induction h with
  | refl => exact ⟨le_refl _, fun _ => ⟨[], .nil _, by simp⟩⟩
  | @tail q r _ hstep ih =>
      have hn := hstep.position_next
      refine ⟨ih.1.trans hn.bound_le, ?_⟩
      intro side
      obtain ⟨as, ha, haf⟩ := ih.2 side
      obtain ⟨bs, hb, hbf⟩ := hn.word_extension side
      refine ⟨as ++ bs, ha.append hb, ?_⟩
      intro a hmem
      rcases List.mem_append.mp hmem with hmem | hmem
      · exact haf a hmem
      · exact ih.1.trans_lt (hbf a hmem)

theorem word_run {N : Set ℕ} (p : Concrete.Hist N) (side : Bool) :
    ∃ as, LabeledWord.LegalRun LabeledWord.initial as (p.position.board.get side) := by
  induction p using History.induction with
  | hinit =>
      have heq : ((History.initial (Position.Next N) Position.initial).position.board.get side) =
          LabeledWord.initial := by cases side <;> rfl
      exact ⟨[], heq ▸ .nil _⟩
  | hstep p q hq ih =>
      obtain ⟨as, has⟩ := ih
      obtain ⟨bs, hbs, _⟩ := hq.word_extension side
      exact ⟨as ++ bs, by simpa using has.append hbs⟩

end History

#print axioms Reply.legal_run
#print axioms Reply.first_read
#print axioms Position.Next.word_extension
#print axioms History.reachable_word_extension
#print axioms History.word_run

end Erdos591.Positive.Game

end Erdos118.Reused591
