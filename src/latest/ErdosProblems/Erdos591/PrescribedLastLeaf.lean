import ErdosProblems.Erdos591.SharedTailHistory
import ErdosProblems.Erdos591.ReachSelectedLeaf
import ErdosProblems.Erdos591.SameBodyRun
import ErdosProblems.Erdos591.PrescribedResponse

/-!
# A winning lower play through a prescribed last selected leaf

At a pending selected-body request, fix the lower label and its common
marker before continuing. A genuine response reaches its first selected
leaf, and a conservative continuation reaches the last one. The exact
coordinate prefix, its length and its pool bounds are retained for the
upper play's delayed response.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem winning_prescribed_last_leaf_fresh {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} {p : Concrete.Hist N}
    (hwin : (exactGame N blue).ArchitectWins H b σ p) (side : Bool)
    {B a c : ℕ} (L : LastFirstLabels H B a c)
    (hp : p.position.pending = some ⟨side, .advance a⟩)
    (hm : (p.position.board.get side).markerEvent = true)
    (hB : max p.position.bound (b p) ≤ B) :
    ∃ q xs, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q ∧
      q.position.pending = none ∧ (q.position.board.get side).relaxed = true ∧
      (q.position.board.get side).coordinates =
        (p.position.board.get side).coordinates ++ L.marker :: xs ∧
      xs.length = L.pivot ∧ (L.marker :: xs).Pairwise (· < ·) ∧
      (∀ x ∈ L.marker :: xs, x ∈ H ∧ B < x) ∧
      (q.position.board.get side).bodyLabels =
        (p.position.board.get side).bodyLabels ++ [L.lower] ∧
      (q.position.board.get side).bodyMarker = L.marker ∧
      (q.position.board.get side).leafIndex = L.pivot ∧
      ∀ y ∈ (q.position.board.get (!side)).coordinates,
        y ≤ (q.position.board.get side).coordinates.getLastD 0 := by
  let b' : Concrete.Hist N → ℕ := fun t => max (b t) B
  have hwin' : (exactGame N blue).ArchitectWins H b' σ p :=
    hwin.mono (exactGame N blue) (Set.Subset.refl H) (fun t => le_max_left (b t) B)
  have hlegal : (p.position.board.get side).AllowedSize L.lower.card :=
    ⟨LabeledWord.marker_not_terminal hm, Or.inr (Or.inr hm)⟩
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
  have hw := ((Position.history_dataInvariant p).2.1 side).1
  have hlabel := LabeledWord.allowedLabel_of_size hlegal rfl L.label_bounds.1
  have hfirstCorrect := hw.read hlabel hread
  have hfirstState := LabeledWord.FirstLeafState.of_marker_read hm ⟨L.pivot, L.pivot_lower⟩ hread
  have hlastState := hfirstState.remainder hfirstCorrect hrest
  have hlastMin := hfirstState.remainder_minimum hfirstCorrect hrest
  have hlastLabels := hfirstState.remainder_bodyLabels hfirstCorrect hrest
  have hlastMarker := hfirstState.remainder_bodyMarker hfirstCorrect hrest
  obtain ⟨r, hparse⟩ := LabeledWord.marker_blocks hm
  have hfirstEq : (p.position.board.get side).record L.lower L.marker
      (Parser.normalize r L.marker) = first := by
    simpa [LabeledWord.read, hparse, Parser.step] using hread
  have hfirstLabels : first.bodyLabels = (p.position.board.get side).bodyLabels ++ [L.lower] := by
    simp [← hfirstEq, LabeledWord.record, hparse]
  have hfirstMarker : first.bodyMarker = L.marker := by
    simp [← hfirstEq, LabeledWord.record, hparse]
  have hfirstLeaf : first.leafIndex = 0 := by simp [← hfirstEq, LabeledWord.record, hparse]
  have hcurrent : last.currentLabel = L.lower := by
    simp [LabeledWord.currentLabel, hlastLabels, hfirstLabels]
  have htarget : LabeledWord.UpToLeaf L.pivot (q₀.position.board.get side) := by
    rw [hword₀]
    exact ⟨hlastState.selected, hcurrent ▸ L.pivot_lower,
      hlastMin.2.2 L.pivot (hcurrent ▸ L.pivot_lower)⟩
  obtain ⟨q, hpath, hqnone, hrel, hleaf, hlabels, hmarker, hsep⟩ :=
    winning_reach_selected_leaf_le_fresh hHN hH blue hwin₀ side L.pivot hnone htarget
      ((FiniteResponseGame.FollowStep.next (exactGame N blue) hstep).reply_separation hp)
  obtain ⟨as, has, hinputs⟩ := follow_word_inputs hpath B (fun t => le_max_right (b t) B) side
  have has' : LabeledWord.LegalRun last as (q.position.board.get side) := by
    simpa only [hword₀] using has
  have hrun := (LabeledWord.zero_run_legal _ (fun _ _ => rfl) hrest).append has'
  have hqLabels : (q.position.board.get side).bodyLabels = first.bodyLabels := by
    simpa only [hword₀] using hlabels.trans (by simpa only [hword₀] using hlastLabels)
  obtain ⟨xs, hcoords, hlength, hmem⟩ := hrun.same_body_coordinates
    (LabeledWord.read_parser_ne_start hread) (congrArg List.length hqLabels)
  have hxs : xs.length = L.pivot := by rw [hfirstLeaf, Nat.zero_add, hleaf] at hlength; omega
  have hcoords' : (q.position.board.get side).coordinates =
      (p.position.board.get side).coordinates ++ L.marker :: xs := by
    rw [hcoords, (LabeledWord.read_spec hread).2]
    simp [List.append_assoc]
  have hinc : (L.marker :: xs).Pairwise (· < ·) := by
    have hi := ((Position.history_dataInvariant q).2.1 side).2
    rw [hcoords'] at hi
    exact (List.pairwise_append.mp hi).2.1
  have htail : ∀ x ∈ tail, x ∈ H ∧ B < x := by
    intro x hx
    have hu : x ∈ u := (Finset.mem_sort (· ≤ ·)).mp (by
      rw [hsort]
      exact List.mem_append_right _ (List.mem_cons_of_mem L.marker hx))
    exact ⟨hpool hu, hfresh x hu⟩
  have hxsPool : ∀ x ∈ xs, x ∈ H ∧ B < x := by
    intro x hx
    obtain ⟨a, ha, hax⟩ := hmem x hx
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
  refine ⟨q, xs, horiginal, hqnone, hrel, hcoords', hxs, hinc, ?_,
    hqLabels.trans hfirstLabels, ?_, hleaf, hsep⟩
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact L.marker_fresh
    · exact hxsPool x hx
  · exact hmarker.trans (by simpa only [hword₀] using hlastMarker.trans hfirstMarker)

theorem winning_prescribed_last_leaf {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} {p : Concrete.Hist N}
    (hwin : (exactGame N blue).ArchitectWins H b σ p) (side : Bool)
    {B a c : ℕ} (L : LastFirstLabels H B a c)
    (hp : p.position.pending = some ⟨side, .advance a⟩)
    (hm : (p.position.board.get side).markerEvent = true)
    (hB : max p.position.bound (b p) ≤ B) :
    ∃ q xs, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q ∧
      q.position.pending = none ∧ (q.position.board.get side).relaxed = true ∧
      (q.position.board.get side).coordinates =
        (p.position.board.get side).coordinates ++ L.marker :: xs ∧
      xs.length = L.pivot ∧ (L.marker :: xs).Pairwise (· < ·) ∧
      (∀ x ∈ L.marker :: xs, x ∈ H ∧ B < x) ∧
      (q.position.board.get side).bodyLabels =
        (p.position.board.get side).bodyLabels ++ [L.lower] ∧
      (q.position.board.get side).bodyMarker = L.marker ∧
      (q.position.board.get side).leafIndex = L.pivot := by
  obtain ⟨q, xs, hpath, hn, hr, hc, hl, hi, hf, hb, hm, he, _⟩ :=
    winning_prescribed_last_leaf_fresh hHN hH blue hwin side L hp hm hB
  exact ⟨q, xs, hpath, hn, hr, hc, hl, hi, hf, hb, hm, he⟩

#print axioms winning_prescribed_last_leaf_fresh
#print axioms winning_prescribed_last_leaf

end Erdos591.Positive.Game.Payoff
