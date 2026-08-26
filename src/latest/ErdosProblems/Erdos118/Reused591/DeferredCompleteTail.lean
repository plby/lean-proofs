import ErdosProblems.Erdos118.Reused591.SharedTailHistory

namespace Erdos118.Reused591

/-!
# Submit an exhausted pending response after a retained prefix

Keep the entire recorded prefix, erase only its newly read labels,
and choose a complete new tail after the newly known bound. The
old command accepts the concatenation because its selected part is
exhausted. The returned suffix, not the old prefix, obeys the new bound.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem deferred_complete_tail_from_prefix {N H : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} (σ : (exactGame N blue).ArchitectStrategy)
    (p : Concrete.Hist N) {r : Request} (hp : p.position.pending = some r)
    (hstart : (p.position.board.get r.side).parser ≠ .start)
    (hno : ¬ Macro.Pending (p.position.board.get r.side))
    {f v : LabeledWord} {front : List (Finset ℕ × ℕ)}
    (hsame : LabeledWord.SameStructure (p.position.board.get r.side) f)
    (hfront : LabeledWord.LegalRun f front v) (hvinc : v.coordinates.Pairwise (· < ·))
    (hfrontPool : ∀ a ∈ front, a.2 ∈ H ∧ max p.position.bound (b p) < a.2)
    (C : ℕ) :
    ∃ q, (exactGame N blue).FollowStep σ H b p q ∧ q.position.pending = none ∧
      (q.position.board.get r.side).terminal = true ∧
      q.position.board.get (!r.side) = p.position.board.get (!r.side) ∧
      ∃ anchor, LabeledWord.SameStructure v anchor ∧
        ∃ as, LabeledWord.LegalRun anchor as (q.position.board.get r.side) ∧
          ∀ a ∈ as, a.2 ∈ H ∧ C < a.2 := by
  let D := max (max C (max p.position.bound (b p))) (v.coordinates.toFinset.sup id)
  let J := H \ Set.Iic D
  have hJ : J.Infinite := hH.sdiff (Set.finite_Iic D)
  obtain ⟨u, ⟨endFine, hfinish⟩, huJ⟩ := LabeledWord.finish_exists v hJ
  let ys := u.sort (· ≤ ·)
  have hys : ∀ y ∈ ys, y ∈ H ∧ D < y := by
    intro y hy
    have hh := huJ ((Finset.mem_sort (· ≤ ·)).mp hy)
    exact ⟨hh.1, lt_of_not_ge hh.2⟩
  have hnew := LabeledWord.zero_run_legal LabeledWord.finishParser (fun _ _ => rfl) hfinish
  have hterm : endFine.terminal = true := LabeledWord.finishParser.run_stopped hfinish
  obtain ⟨z, hz, hshapeZ⟩ := hsame.erase_run hfront.run
  obtain ⟨last, hlastRun, hlastShape⟩ := hshapeZ.erase_run hnew.run
  have htail : LabeledWord.LegalRun z (ys.map fun y => (∅, y)) last := by
    apply LabeledWord.legal_of_zero_atoms
    simpa only [ys, List.map_map, Function.comp_def, List.map_id] using hlastRun
  have hwhole : (p.position.board.get r.side).runAtoms
      ((front.map Prod.snd ++ ys).map fun x => (∅, x)) = some last := by
    simp only [List.map_append, LabeledWord.runAtoms_append, hz, Option.bind_some, htail.run]
  have hterminal : last.terminal = true := by
    simpa only [LabeledWord.terminal, hlastShape.parser_eq] using hterm
  have hfrontInc : (front.map Prod.snd).Pairwise (· < ·) := by
    rw [LabeledWord.runAtoms_coordinates hfront.run] at hvinc
    exact (List.pairwise_append.mp hvinc).2.1
  have hinc : (front.map Prod.snd ++ ys).Pairwise (· < ·) := by
    apply List.pairwise_append.mpr
    refine ⟨hfrontInc, (Finset.sortedLT_sort u).pairwise, ?_⟩
    intro x hx y hy
    have hxv : x ∈ v.coordinates := by
      rw [LabeledWord.runAtoms_coordinates hfront.run]
      exact List.mem_append_right _ hx
    exact ((Finset.le_sup (f := id) (List.mem_toFinset.mpr hxv)).trans
      (le_max_right _ _)).trans_lt (hys y hy).2
  have hlegal := (Position.history_controlInvariant p).2 r hp
  have hlive : (p.position.board.get r.side).terminal = false := by
    cases hc : r.command with
    | finish => simpa [Request.Legal, hc] using hlegal
    | advance d => exact (show (p.position.board.get r.side).AllowedSize d by
        simpa [Request.Legal, hc] using hlegal).1
  have hfinishLast := LabeledWord.finish_of_zero_atoms hwhole hterminal
  have hreplyFinish : Reply p.position.board ⟨r.side, .finish⟩
      (front.map Prod.snd ++ ys).toFinset (p.position.board.update r.side last) :=
    Reply.finish r.side _ last hlive (by
      simpa only [Erdos590.Larson.sort_toFinset_eq_self_of_pairwise hinc] using hfinishLast)
  have hreply := (Reply.not_pending_iff_finish p.position.board r _ _ hlegal hstart hno).mpr
    hreplyFinish
  have hpool : ∀ x ∈ (front.map Prod.snd ++ ys).toFinset,
      x ∈ H ∧ p.position.bound < x ∧ b p < x := by
    intro x hx
    have hf : x ∈ H ∧ max p.position.bound (b p) < x := by
      rcases List.mem_append.mp (List.mem_toFinset.mp hx) with hx | hx
      · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
        exact hfrontPool a ha
      · exact ⟨(hys x hx).1, ((le_max_right _ _).trans (le_max_left _ _)).trans_lt (hys x hx).2⟩
    exact ⟨hf.1, (le_max_left _ _).trans_lt hf.2, (le_max_right _ _).trans_lt hf.2⟩
  obtain ⟨q, hstep, hboard, hn⟩ := Concrete.follow_reply hHN (payoff blue) σ p hp hreply
    (fun x hx => (hpool x hx).1) (fun x hx => (hpool x hx).2)
  refine ⟨q, hstep, hn, by simpa [hboard] using hterminal,
    by simpa [hboard] using hreply.other_eq, z, hshapeZ.symm,
    ys.map (fun y => (∅, y)), by simpa [hboard] using htail, ?_⟩
  intro a ha
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp ha
  exact ⟨(hys y hy).1, ((le_max_left _ _).trans (le_max_left _ _)).trans_lt (hys y hy).2⟩

#print axioms deferred_complete_tail_from_prefix

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
