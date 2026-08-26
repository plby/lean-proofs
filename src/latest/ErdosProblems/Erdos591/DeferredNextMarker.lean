import ErdosProblems.Erdos591.FreshMarkerRemainder
import ErdosProblems.Erdos591.NextMarkerReplay
import ErdosProblems.Erdos591.SameBodyRun

/-!
# Submit a pending next-body response after its retained same-body prefix

The old upper label has no remaining current-body leaf. Erase the
nonempty recorded lower prefix, extend its virtual upper endpoint with
fresh coordinates to the least future selected marker, and submit the
whole old response. Retain only the new tail for the lower completion.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem deferred_next_marker_from_prefix {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    (σ : (exactGame N blue).ArchitectStrategy) (p : Concrete.Hist N) (side : Bool)
    (hp : p.position.pending = some ⟨side, .advance 0⟩)
    (hrel : (p.position.board.get side).relaxed = true)
    (hno : (p.position.board.get side).NoLeafPending) {i : ℕ}
    (hi : LabeledWord.BeforeBody i (p.position.board.get side))
    (hnext : ∀ k ∈ (p.position.board.get side).rootLabel,
      (p.position.board.get side).bodyLabels.length < k → i ≤ k)
    {f v : LabeledWord} {frontAtoms : List (Finset ℕ × ℕ)}
    (hsame : LabeledWord.SameStructure (p.position.board.get side) f)
    (hfront : LabeledWord.LegalRun f frontAtoms v)
    (hcount : v.bodyLabels.length = f.bodyLabels.length)
    (hstrict : f.leafIndex < v.leafIndex) (hvinc : v.coordinates.Pairwise (· < ·))
    (hfrontPool : ∀ a ∈ frontAtoms, a.2 ∈ H ∧ max p.position.bound (b p) < a.2)
    (C : ℕ) :
    ∃ q, (exactGame N blue).FollowStep σ H b p q ∧ q.position.pending = none ∧
      (q.position.board.get side).markerEvent = true ∧
      (q.position.board.get side).bodyLabels.length + 1 = i ∧
      q.position.board.get (!side) = p.position.board.get (!side) ∧
      ∃ anchor, LabeledWord.SameStructure v anchor ∧
        ∃ as, LabeledWord.LegalRun anchor as (q.position.board.get side) ∧
          ∀ a ∈ as, a.2 ∈ H ∧ C < a.2 := by
  have hw := ((Position.history_dataInvariant p).2.1 side).1
  have hstart := LabeledWord.relaxed_ne_start hw hrel
  obtain ⟨z, hz, hshapeZ⟩ := hsame.erase_run hfront.run
  have hzero := LabeledWord.legal_of_zero_atoms hz
  have hlenZ : z.bodyLabels.length = (p.position.board.get side).bodyLabels.length :=
    hshapeZ.body_length.trans (hcount.trans hsame.body_length.symm)
  have hrootZ := hzero.rootLabel_eq hstart
  have hne : frontAtoms.map Prod.snd ≠ [] := by
    intro he
    have heq : p.position.board.get side = z := Option.some.inj (by simpa [he] using hz)
    have hleaf : f.leafIndex = v.leafIndex :=
      hsame.leaf_eq.symm.trans ((congrArg LabeledWord.leafIndex heq).trans hshapeZ.leaf_eq)
    exact (lt_irrefl _ (hleaf ▸ hstrict))
  have hzNo := hno.nonempty_zero_run hstart hne hz
  have hzBefore : LabeledWord.BeforeBody i z := ⟨hrootZ ▸ hi.1, by simpa [hlenZ] using hi.2⟩
  have hzNext : ∀ k ∈ z.rootLabel, z.bodyLabels.length < k → i ≤ k := by
    simpa only [hrootZ, hlenZ] using hnext
  let D := max C (max p.position.bound (b p))
  obtain ⟨ys, last, htail, hm, hidx, hysInc, hysPool, hysAfter⟩ :=
    LabeledWord.fresh_next_marker_remainder hH z (hzero.cursorInvariant hw)
      (hzero.parser_ne_start hstart) hzNo.1 hzNo.2 hzBefore hzNext D
  have hwhole : (p.position.board.get side).runAtoms
      (((frontAtoms.map Prod.snd) ++ ys).map fun x => (∅, x)) = some last := by
    simp only [List.map_append, LabeledWord.runAtoms_append, hz, Option.bind_some, htail.run]
  have hfrontInc : (frontAtoms.map Prod.snd).Pairwise (· < ·) := by
    rw [LabeledWord.runAtoms_coordinates hfront.run] at hvinc
    exact (List.pairwise_append.mp hvinc).2.1
  have hwholeInc : (frontAtoms.map Prod.snd ++ ys).Pairwise (· < ·) := by
    apply List.pairwise_append.mpr
    refine ⟨hfrontInc, hysInc, ?_⟩
    intro x hx y hy
    apply hysAfter x ?_ y hy
    rw [LabeledWord.runAtoms_coordinates hz]
    simpa only [List.map_map, Function.comp_def, List.map_id] using
      List.mem_append_right (p.position.board.get side).coordinates hx
  have hpool : ∀ x ∈ frontAtoms.map Prod.snd ++ ys,
      x ∈ H ∧ p.position.bound < x ∧ b p < x := by
    intro x hx
    have hf : x ∈ H ∧ max p.position.bound (b p) < x := by
      rcases List.mem_append.mp hx with hx | hx
      · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
        exact hfrontPool a ha
      · exact ⟨(hysPool x hx).1, (le_max_right _ _).trans_lt (hysPool x hx).2⟩
    exact ⟨hf.1, (le_max_left _ _).trans_lt hf.2, (le_max_right _ _).trans_lt hf.2⟩
  have hr := Reply.next_marker_of_list p.position.board side hw hrel hno hi hnext
    hwhole hm hidx hwholeInc
  obtain ⟨q, hstep, hboard, hn⟩ := Concrete.follow_reply hHN (payoff blue) σ p hp hr
    (fun x hx => (hpool x (List.mem_toFinset.mp hx)).1)
    (fun x hx => (hpool x (List.mem_toFinset.mp hx)).2)
  refine ⟨q, hstep, hn, by simpa [hboard] using hm, by simpa [hboard] using hidx,
    by simpa [hboard] using hr.other_eq, z, hshapeZ.symm,
    ys.map (fun y => (∅, y)), by simpa [hboard] using htail, ?_⟩
  intro a ha
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp ha
  exact ⟨(hysPool y hy).1, (le_max_left _ _).trans_lt (hysPool y hy).2⟩

#print axioms deferred_next_marker_from_prefix

end Erdos591.Positive.Game.Payoff
