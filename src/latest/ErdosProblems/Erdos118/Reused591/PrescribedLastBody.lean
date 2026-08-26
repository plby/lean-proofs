import ErdosProblems.Erdos118.Reused591.BodyGluingHistory

namespace Erdos118.Reused591

/-!
# A prescribed root prefix through the last selected-body request

The lower root label and marker are fixed before playing. Continue from
the first selected body to the last selected body's pending request.
The retained coordinate execution starts just after the common root and
is ready for the upper root-label response, with all input bounds intact.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem winning_prescribed_last_body {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} {p : Concrete.Hist N}
    (hwin : (exactGame N blue).ArchitectWins H b σ p) (side : Bool)
    {B a c : ℕ} (L : LastFirstLabels H B a c)
    (hp : p.position.pending = some ⟨side, .advance a⟩)
    (hinit : p.position.board.get side = LabeledWord.initial)
    (hB : max p.position.bound (b p) ≤ B) :
    ∃ q d as, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q ∧
      q.position.pending = some ⟨side, .advance d⟩ ∧ 0 < d ∧
      (q.position.board.get side).markerEvent = true ∧
      (q.position.board.get side).bodyLabels.length + 1 = L.pivot ∧
      (LabeledCode.rootCursor L.lower L.marker).runAtoms as = some (q.position.board.get side) ∧
      (L.marker :: as.map Prod.snd).Pairwise (· < ·) ∧
      (∀ x ∈ L.marker :: as.map Prod.snd, x ∈ H ∧ B < x) ∧
      (q.position.board.get side).rootLabel = L.lower := by
  let b' : Concrete.Hist N → ℕ := fun t => max (b t) B
  have hwin' : (exactGame N blue).ArchitectWins H b' σ p :=
    hwin.mono (exactGame N blue) (Set.Subset.refl H) (fun t => le_max_left (b t) B)
  have hlegal : (p.position.board.get side).AllowedSize L.lower.card := by
    simp [hinit, LabeledWord.AllowedSize, LabeledWord.terminal, LabeledWord.initial]
  obtain ⟨u, last, tail, hreply, hsort, hpool, hfresh, first, hread, hrest⟩ :=
    Reply.prescribed_advance_exists_run hH p.position.board side L.lower L.marker B
      hlegal L.lower_fresh L.marker_fresh
  rw [L.lower_card] at hreply
  have hbp : b' p ≤ B := max_le ((le_max_right _ _).trans hB) le_rfl
  obtain ⟨q₀, hstep, hboard, hnone⟩ := Concrete.follow_reply hHN (payoff blue) (b := b') σ p
    hp hreply hpool (fun x hx => ⟨((le_max_left _ _).trans hB).trans_lt (hfresh x hx),
      hbp.trans_lt (hfresh x hx)⟩)
  have hword₀ : q₀.position.board.get side = last := by simp [hboard]
  have hwin₀ := hwin'.of_reachable (exactGame N blue) (Relation.ReflTransGen.single hstep)
  have hfirstEq : first = LabeledCode.rootCursor L.lower L.marker := by
    rw [hinit] at hread
    exact Option.some.inj (hread.symm.trans (LabeledCode.read_root _ _))
  have hrootRun := LabeledWord.zero_run_legal _ (fun _ _ => rfl) hrest
  have hstart := LabeledWord.read_parser_ne_start hread
  have hlastRoot : last.rootLabel = L.lower := by
    simpa [hfirstEq, LabeledCode.rootCursor] using hrootRun.rootLabel_eq hstart
  have hno : first.NoRootPassed := by
    intro i hi
    have himem : i ∈ L.lower := by simpa [hfirstEq, LabeledCode.rootCursor] using hi
    simpa [hfirstEq, LabeledCode.rootCursor] using (L.label_bounds.1 i himem).1
  have hlastNo := hno.remainder hstart hrest
  have hbefore : LabeledWord.BeforeBody L.pivot (q₀.position.board.get side) := by
    rw [hword₀]
    have hi : L.pivot ∈ last.rootLabel := hlastRoot ▸ L.pivot_lower
    exact ⟨hi, hlastNo L.pivot hi⟩
  have hlastStart : (q₀.position.board.get side).parser ≠ .start := by
    rw [hword₀]
    exact hrootRun.parser_ne_start hstart
  obtain ⟨q, d, hpath, hpending, hd, hm, hindex⟩ :=
    winning_reach_body_marker hHN hH blue hwin₀ side L.pivot hlastStart hbefore
  obtain ⟨as, has, hinputs⟩ := follow_word_inputs hpath B (fun t => le_max_right (b t) B) side
  have has' : LabeledWord.LegalRun last as (q.position.board.get side) := by
    simpa only [hword₀] using has
  have hrun := hrootRun.append has'
  let atoms := tail.map (fun x => (∅, x)) ++ as
  have hraw : (LabeledCode.rootCursor L.lower L.marker).runAtoms atoms =
      some (q.position.board.get side) := by simpa only [hfirstEq] using hrun.run
  have hcoords : (q.position.board.get side).coordinates = L.marker :: atoms.map Prod.snd := by
    simpa [LabeledCode.rootCursor] using LabeledWord.runAtoms_coordinates hraw
  have hinc : (L.marker :: atoms.map Prod.snd).Pairwise (· < ·) := by
    simpa only [hcoords] using ((Position.history_dataInvariant q).2.1 side).2
  have htail : ∀ x ∈ tail, x ∈ H ∧ B < x := by
    intro x hx
    have hu : x ∈ u := (Finset.mem_sort (· ≤ ·)).mp (by
      rw [hsort]
      exact List.mem_append_right _ (List.mem_cons_of_mem L.marker hx))
    exact ⟨hpool hu, hfresh x hu⟩
  have hnewPool : ∀ x ∈ atoms.map Prod.snd, x ∈ H ∧ B < x := by
    intro x hx
    obtain ⟨a, ha, hax⟩ := List.mem_map.mp hx
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨y, hy, hay⟩ := List.mem_map.mp ha
      have heq : y = x := by simpa [← hay] using hax
      exact heq ▸ htail y hy
    · exact hax ▸ hinputs a ha
  have hfull : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b') p q :=
    hpath.head hstep
  have horiginal : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q :=
    Relation.ReflTransGen.mono (fun _ _ hs =>
      FiniteResponseGame.FollowStep.mono (exactGame N blue) (Set.Subset.refl H)
        (fun t => le_max_left (b t) B) hs) _ _ hfull
  refine ⟨q, d, atoms, horiginal, hpending, hd, hm, hindex, hraw, hinc, ?_, ?_⟩
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact L.marker_fresh
    · exact hnewPool x hx
  · simpa [hfirstEq, LabeledCode.rootCursor] using hrun.rootLabel_eq hstart

#print axioms winning_prescribed_last_body

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
