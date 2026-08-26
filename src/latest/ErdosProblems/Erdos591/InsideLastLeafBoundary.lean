import ErdosProblems.Erdos591.NextLeafEndpoint
import ErdosProblems.Erdos591.OutsideBoundary

/-!
# Before the sole remaining first-word leaf, the opposite word is exhausted

One test next-leaf response exhausts the first word's selected indices.
The inside boundary theorem then exhausts the unchanged second word.
This identifies middle-phase endpoints without committing the common
last leaf and without introducing a separate cut-count assumption.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem winning_before_last_leaf_other_exhausted {N H : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    {p : Concrete.Hist N} (hwin : (exactGame N blue).ArchitectWins H b σ p)
    (hmode : p.position.mode = some true)
    (hp : p.position.pending = some ⟨false, .advance 0⟩) {j : ℕ}
    (htarget : LabeledWord.UpToLeaf j p.position.board.left)
    (hstrict : p.position.board.left.leafIndex < j)
    (hnext : ∀ k ∈ p.position.board.left.currentLabel,
      p.position.board.left.leafIndex < k → j ≤ k)
    (hrootLast : ∀ k ∈ p.position.board.left.rootLabel,
      k ≤ p.position.board.left.bodyLabels.length)
    (hleafLast : ∀ k ∈ p.position.board.left.currentLabel, k ≤ j)
    (hstartT : p.position.board.right.parser ≠ .start) :
    ¬ Macro.Pending p.position.board.right := by
  have hk : (exactGame N blue).kind p = .builder :=
    (Concrete.kind_builder_iff (payoff blue) p).mpr ⟨_, hp⟩
  obtain ⟨u, hu, huH, hub⟩ := (exactGame N blue).response_exists_above hHN hH p hk (b p)
  let q := Concrete.response p u
  have hs : (exactGame N blue).FollowStep σ H b p q :=
    FiniteResponseGame.FollowStep.builder (exactGame N blue) σ p u hk hu huH hub
  have hr := (Concrete.response_spec hu).reply_spec hp
  have hw := ((Position.history_dataInvariant p).2.1 false).1
  obtain ⟨hrel, hidx, hlabels, _hmarker⟩ := hr.next_leaf_endpoint hw
    ((Position.history_dataInvariant q).2.1 false).1
    (fun x hx => (Nat.zero_le _).trans_lt (hub x hx)) htarget hstrict hnext
  change q.position.board.left.leafIndex = j at hidx
  change q.position.board.left.bodyLabels = p.position.board.left.bodyLabels at hlabels
  obtain ⟨r, k, hparse⟩ := htarget.parser_leaves hw
  have hstartS : p.position.board.left.parser ≠ .start := by simp [hparse]
  have hpath := Relation.ReflTransGen.single hs
  obtain ⟨as, has, _⟩ := follow_word_inputs hpath 0 (fun _ => Nat.zero_le _) false
  have hroot : q.position.board.left.rootLabel = p.position.board.left.rootLabel :=
    has.rootLabel_eq hstartS
  have hcurrent : q.position.board.left.currentLabel = p.position.board.left.currentLabel := by
    simp [LabeledWord.currentLabel, hlabels]
  have hlast : ¬ Macro.Pending q.position.board.left := by
    rintro (⟨i, hi, hlt⟩ | ⟨_hsel, i, hi, hlt⟩)
    · have hi' := hrootLast i (hroot ▸ hi)
      rw [hlabels] at hlt
      omega
    · have hi' := hleafLast i (hcurrent ▸ hi)
      rw [hidx] at hlt
      omega
  have hother : q.position.board.right = p.position.board.right := hr.other_eq
  have hlastT := winning_no_pending_smaller hHN hH blue
    (hwin.of_reachable (exactGame N blue) hpath) (follow_mode_some hpath hmode)
    (by simpa [Board.get, hother] using hstartT)
    (by simpa [Board.get] using has.parser_ne_start hstartS) hlast
  simpa [Board.get, hother] using hlastT

#print axioms winning_before_last_leaf_other_exhausted

end Erdos591.Positive.Game.Payoff
