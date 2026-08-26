import ErdosProblems.Erdos591.FreshLeafExtension
import ErdosProblems.Erdos591.NextLeafReplay
import ErdosProblems.Erdos591.ReplySeparation

/-!
# Resume a pending next-leaf reply after a retained virtual prefix

Erase only the new labels in the retained prefix, preserving every old
label. Extend the resulting same-body cursor to the next selected leaf
with fresh coordinates. Submit the whole prefix as one actual response,
and retain the newly added tail for a different waiting reply.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem deferred_next_leaf_from_prefix {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    (σ : (exactGame N blue).ArchitectStrategy) (p : Concrete.Hist N) (side : Bool)
    (hp : p.position.pending = some ⟨side, .advance 0⟩) {j : ℕ}
    (hup : LabeledWord.UpToLeaf j (p.position.board.get side))
    (hstrict : (p.position.board.get side).leafIndex < j)
    (hnext : ∀ k ∈ (p.position.board.get side).currentLabel,
      (p.position.board.get side).leafIndex < k → j ≤ k)
    {f v : LabeledWord} {front : List (Finset ℕ × ℕ)}
    (hsame : LabeledWord.SameStructure (p.position.board.get side) f)
    (hfront : LabeledWord.LegalRun f front v)
    (hcount : v.bodyLabels.length = f.bodyLabels.length)
    (hmarker : v.bodyMarker = f.bodyMarker)
    (hbefore : v.leafIndex < j) (hvinc : v.coordinates.Pairwise (· < ·))
    (hfrontPool : ∀ atom ∈ front, atom.2 ∈ H ∧ max p.position.bound (b p) < atom.2)
    (C : ℕ) :
    ∃ q, (exactGame N blue).FollowStep σ H b p q ∧ q.position.pending = none ∧
      (q.position.board.get side).relaxed = true ∧ (q.position.board.get side).leafIndex = j ∧
      (q.position.board.get side).bodyLabels = (p.position.board.get side).bodyLabels ∧
      (q.position.board.get side).bodyMarker = (p.position.board.get side).bodyMarker ∧
      q.position.board.get (!side) = p.position.board.get (!side) ∧
      (∀ y ∈ (q.position.board.get (!side)).coordinates,
        y ≤ (q.position.board.get side).coordinates.getLastD 0) ∧
      ∃ anchor, LabeledWord.SameStructure v anchor ∧ ∃ as,
        LabeledWord.LegalRun anchor as (q.position.board.get side) ∧
        ∀ atom ∈ as, atom.2 ∈ H ∧ C < atom.2 := by
  have hw := ((Position.history_dataInvariant p).2.1 side).1
  obtain ⟨r, k, hparse⟩ := hup.parser_leaves hw
  have hstart : (p.position.board.get side).parser ≠ .start := by simp [hparse]
  obtain ⟨z, hz, hshape⟩ := hsame.erase_run hfront.run
  have hzero := LabeledWord.legal_of_zero_atoms hz
  have hlenZ : z.bodyLabels.length = (p.position.board.get side).bodyLabels.length :=
    hshape.body_length.trans (hcount.trans hsame.body_length.symm)
  have hlabelsZ : z.bodyLabels = (p.position.board.get side).bodyLabels := by
    obtain ⟨rest, heq⟩ := hzero.bodyLabels_prefix hstart
    have hrest : rest.length = 0 := by
      have hlen := congrArg List.length heq
      simp only [List.length_append] at hlen
      omega
    simpa only [List.length_eq_zero_iff.mp hrest, List.append_nil] using heq.symm
  have hmarkerZ : z.bodyMarker = (p.position.board.get side).bodyMarker :=
    hshape.bodyMarker_eq.trans (hmarker.trans hsame.bodyMarker_eq.symm)
  have hrootZ := hzero.rootLabel_eq hstart
  have hbeforeZ : z.leafIndex < j := by simpa only [hshape.leaf_eq] using hbefore
  have hupZ : LabeledWord.UpToLeaf j z :=
    ⟨by simpa only [hlabelsZ, hrootZ] using hup.selected,
      by simpa only [LabeledWord.currentLabel, hlabelsZ] using hup.mem, hbeforeZ.le⟩
  have hincZ : z.coordinates.Pairwise (· < ·) := hshape.coordinates_eq.symm ▸ hvinc
  let D := max C (max p.position.bound (b p))
  obtain ⟨ys, last, htail, hrelLast, hiLast, hlabelsLast, hmarkerLast, _hrootLast,
      _hyslen, _hcoordsLast, _hincLast, hysPool, hysAfter⟩ :=
    LabeledWord.fresh_leaf_extension hH z (hzero.cursorInvariant hw) hincZ hupZ hbeforeZ D
  have hwhole : (p.position.board.get side).runAtoms
      ((front.map Prod.snd ++ ys).map fun y => (∅, y)) = some last := by
    simp only [List.map_append, LabeledWord.runAtoms_append, hz, Option.bind_some, htail.run]
  have hfrontInc : (front.map Prod.snd).Pairwise (· < ·) := by
    rw [LabeledWord.runAtoms_coordinates hfront.run] at hvinc
    exact (List.pairwise_append.mp hvinc).2.1
  have hysInc : ys.Pairwise (· < ·) := by
    have hi := _hincLast
    rw [_hcoordsLast] at hi
    exact (List.pairwise_append.mp hi).2.1
  have hwholeInc : (front.map Prod.snd ++ ys).Pairwise (· < ·) := by
    refine List.pairwise_append.mpr ⟨hfrontInc, hysInc, ?_⟩
    intro x hx y hy
    apply hysAfter x ?_ y hy
    rw [LabeledWord.runAtoms_coordinates hz]
    simpa only [List.map_map, Function.comp_def, List.map_id] using
      List.mem_append_right (p.position.board.get side).coordinates hx
  have hlastUp : LabeledWord.UpToLeaf j last :=
    ⟨(of_decide_eq_true hrelLast).2.1, hiLast ▸ (of_decide_eq_true hrelLast).2.2, hiLast.le⟩
  have hreply := Reply.next_leaf_of_list p.position.board side hw hup hstrict hnext hwhole
    hlastUp hiLast (hlabelsLast.trans hlabelsZ) (hmarkerLast.trans hmarkerZ) hwholeInc
  have hpool : ∀ x ∈ front.map Prod.snd ++ ys,
      x ∈ H ∧ p.position.bound < x ∧ b p < x := by
    intro x hx
    have hf : x ∈ H ∧ max p.position.bound (b p) < x := by
      rcases List.mem_append.mp hx with hx | hx
      · obtain ⟨atom, hatom, rfl⟩ := List.mem_map.mp hx
        exact hfrontPool atom hatom
      · exact ⟨(hysPool x hx).1, (le_max_right _ _).trans_lt (hysPool x hx).2⟩
    exact ⟨hf.1, (le_max_left _ _).trans_lt hf.2, (le_max_right _ _).trans_lt hf.2⟩
  obtain ⟨q, hstep, hboard, hn⟩ := Concrete.follow_reply hHN (payoff blue) σ p hp hreply
    (fun x hx => (hpool x (List.mem_toFinset.mp hx)).1)
    (fun x hx => (hpool x (List.mem_toFinset.mp hx)).2)
  have hword : q.position.board.get side = last := by simp [hboard]
  refine ⟨q, hstep, hn, hword ▸ hrelLast, hword ▸ hiLast,
    hword ▸ hlabelsLast.trans hlabelsZ, hword ▸ hmarkerLast.trans hmarkerZ,
    by simpa [hboard] using hreply.other_eq,
    (FiniteResponseGame.FollowStep.next (exactGame N blue) hstep).reply_separation hp,
    z, hshape.symm, ys.map (fun y => (∅, y)), by simpa only [hword] using htail, ?_⟩
  intro atom hatom
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hatom
  exact ⟨(hysPool y hy).1, (le_max_left _ _).trans_lt (hysPool y hy).2⟩

#print axioms deferred_next_leaf_from_prefix

end Erdos591.Positive.Game.Payoff
