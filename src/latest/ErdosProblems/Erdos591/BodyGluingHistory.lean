import ErdosProblems.Erdos591.PrescribedLastLeaf

/-!
# Last--first body gluing in two actual strategy histories

Both body requests are pending before the common marker is chosen.
The lower play proceeds to its prescribed last leaf; the upper play then
submits the shared coordinate prefix as its first-leaf response. Both
follow the original strategy conservatively, and the upper other word
is unchanged. The two labelings are never identified or overwritten.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem winning_body_gluing_fresh {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} {lower upper : Concrete.Hist N}
    (hwin : (exactGame N blue).ArchitectWins H b σ lower) (s t : Bool)
    {B a c : ℕ} (L : LastFirstLabels H B a c)
    (hlower : lower.position.pending = some ⟨s, .advance a⟩)
    (hupper : upper.position.pending = some ⟨t, .advance c⟩)
    (hml : (lower.position.board.get s).markerEvent = true)
    (hmu : (upper.position.board.get t).markerEvent = true)
    (hsame : LabeledWord.SameStructure (lower.position.board.get s) (upper.position.board.get t))
    (hBl : max lower.position.bound (b lower) ≤ B)
    (hBu : max upper.position.bound (b upper) ≤ B) :
    ∃ q v, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) lower q ∧
      (exactGame N blue).FollowStep σ H b upper v ∧
      q.position.pending = none ∧ v.position.pending = none ∧
      LabeledWord.SameStructure (q.position.board.get s) (v.position.board.get t) ∧
      (q.position.board.get s).relaxed = true ∧ (v.position.board.get t).relaxed = true ∧
      (q.position.board.get s).leafIndex = L.pivot ∧
      (q.position.board.get s).bodyLabels = (lower.position.board.get s).bodyLabels ++ [L.lower] ∧
      (v.position.board.get t).bodyLabels = (upper.position.board.get t).bodyLabels ++ [L.upper] ∧
      v.position.board.get (!t) = upper.position.board.get (!t) ∧
      ∀ y ∈ (q.position.board.get (!s)).coordinates,
        y ≤ (q.position.board.get s).coordinates.getLastD 0 := by
  obtain ⟨q, xs, hpath, hnone, hrel, hcoords, hlen, hinc, hpool, hlabels, _, hleaf, hsep⟩ :=
    winning_prescribed_last_leaf_fresh hHN hH blue hwin s L hlower hml hBl
  obtain ⟨r, hparse⟩ := LabeledWord.marker_blocks hmu
  have hw := ((Position.history_dataInvariant upper).2.1 t).1
  obtain ⟨u, hreply, _hsort, huH, huB⟩ := L.leaf_reply upper.position.board t r xs
    hw hparse hmu hlen hinc (fun x hx => (hpool x (List.mem_cons_of_mem _ hx)).1)
  obtain ⟨v, hstep, hboard, hvnone⟩ := Concrete.follow_reply hHN (payoff blue) σ upper
    hupper hreply huH (fun x hx => ⟨((le_max_left _ _).trans hBu).trans_lt (huB x hx),
      ((le_max_right _ _).trans hBu).trans_lt (huB x hx)⟩)
  have hword : v.position.board.get t =
      LabeledWord.bodyLeafCursor (upper.position.board.get t) L.upper L.marker r xs := by
    simp [hboard]
  have hcoords' : (q.position.board.get s).coordinates = (v.position.board.get t).coordinates := by
    rw [hcoords, hword]
    simp [LabeledWord.bodyLeafCursor, hsame.coordinates_eq]
  obtain ⟨as, has⟩ := History.word_run q s
  obtain ⟨bs, hbs⟩ := History.word_run v t
  have hshape := LabeledWord.sameStructure_of_initial_runs has.run hbs.run hcoords'
  have hrel' : (v.position.board.get t).relaxed = true := by
    rw [hword]
    simpa [LabeledWord.relaxed, LabeledWord.bodyLeafCursor, LabeledWord.currentLabel, hlen] using
      (show 0 < L.pivot ∧ (upper.position.board.get t).bodyLabels.length + 1 ∈
          (upper.position.board.get t).rootLabel ∧ L.pivot ∈ L.upper from
        ⟨(L.label_bounds.2 L.pivot L.pivot_upper).1,
          LabeledWord.marker_body_mem hmu, L.pivot_upper⟩)
  exact ⟨q, v, hpath, hstep, hnone, hvnone, hshape, hrel, hrel', hleaf, hlabels,
    by simp [hword, LabeledWord.bodyLeafCursor], by simpa [hboard] using hreply.other_eq, hsep⟩

theorem winning_body_gluing {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} {lower upper : Concrete.Hist N}
    (hwin : (exactGame N blue).ArchitectWins H b σ lower) (s t : Bool)
    {B a c : ℕ} (L : LastFirstLabels H B a c)
    (hlower : lower.position.pending = some ⟨s, .advance a⟩)
    (hupper : upper.position.pending = some ⟨t, .advance c⟩)
    (hml : (lower.position.board.get s).markerEvent = true)
    (hmu : (upper.position.board.get t).markerEvent = true)
    (hsame : LabeledWord.SameStructure (lower.position.board.get s) (upper.position.board.get t))
    (hBl : max lower.position.bound (b lower) ≤ B)
    (hBu : max upper.position.bound (b upper) ≤ B) :
    ∃ q v, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) lower q ∧
      (exactGame N blue).FollowStep σ H b upper v ∧
      q.position.pending = none ∧ v.position.pending = none ∧
      LabeledWord.SameStructure (q.position.board.get s) (v.position.board.get t) ∧
      (q.position.board.get s).relaxed = true ∧ (v.position.board.get t).relaxed = true ∧
      (q.position.board.get s).leafIndex = L.pivot ∧
      (q.position.board.get s).bodyLabels = (lower.position.board.get s).bodyLabels ++ [L.lower] ∧
      (v.position.board.get t).bodyLabels = (upper.position.board.get t).bodyLabels ++ [L.upper] ∧
      v.position.board.get (!t) = upper.position.board.get (!t) := by
  obtain ⟨q, v, hq, hv, hnq, hnv, he, hrq, hrv, hi, hlq, hlv, ho, _⟩ :=
    winning_body_gluing_fresh hHN hH blue hwin s t L hlower hupper hml hmu hsame hBl hBu
  exact ⟨q, v, hq, hv, hnq, hnv, he, hrq, hrv, hi, hlq, hlv, ho⟩

/-- The last leaf of the last selected body has no pending selected
index, regardless of the later coordinate choices in an upper play. -/
theorem last_selected_leaf_not_pending {H : Set ℕ} {B a c : ℕ}
    (L : LastFirstLabels H B a c) {w : LabeledWord}
    (hroot : ∀ i ∈ w.rootLabel, i ≤ w.bodyLabels.length)
    (hcurrent : w.currentLabel = L.lower) (hleaf : w.leafIndex = L.pivot) :
    ¬ Macro.Pending w := by
  rintro (⟨i, hi, hlt⟩ | ⟨_, j, hj, hlt⟩)
  · exact (Nat.not_lt_of_ge (hroot i hi)) hlt
  · have hle := L.lower_le j (hcurrent ▸ hj)
    rw [hleaf] at hlt
    exact (Nat.not_lt_of_ge hle) hlt

#print axioms winning_body_gluing
#print axioms winning_body_gluing_fresh
#print axioms last_selected_leaf_not_pending

end Erdos591.Positive.Game.Payoff
