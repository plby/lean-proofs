import ErdosProblems.Erdos591.InsideSingletonBridge
import ErdosProblems.Erdos591.ReservedInsidePreparation

/-!
# Insert the second lower play between the penultimate and last shared body

The first lower history is waiting for its next S marker, and TU has
issued its U-root request. Finish the reserved SU opening, install a
managed U root on a fresh subpool, and apply the actual singleton bridge.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact
open Relay

theorem inside_singleton_insertion_triangle {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) (htri : blue.CliqueFree 3) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy}
    (hroot : (exactGame N blue).ArchitectWins H b σ
      (History.initial (Position.Next N) Position.initial))
    (origin old upperOrigin : Concrete.Hist N) {B a c : ℕ} (L : LastLastLabels H B a)
    (hwinOrigin : (exactGame N blue).ArchitectWins H b σ origin)
    (hopening : origin.position.pending = some ⟨false, .advance a⟩)
    (hboardOrigin : origin.position.board = Board.initial)
    (hmodeOrigin : origin.position.mode = some true)
    (hB : max origin.position.bound (b origin) ≤ B)
    (hfromOld : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin old)
    (hfromUpper : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin upperOrigin)
    (hall : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin z →
      (exactGame N blue).kind z = .terminal w → lastBodySingletonColor false z = true)
    (hpOld : old.position.pending = some ⟨false, .advance 0⟩)
    (hOldRoot : old.position.board.left.rootLabel = L.lower)
    (hOldBody : old.position.board.left.bodyLabels.length = L.penultimate)
    (hOldRel : old.position.board.left.relaxed = true)
    (hOldNo : old.position.board.left.NoLeafPending)
    (hTRel : old.position.board.right.relaxed = true)
    (hTLast : ¬ Macro.Pending old.position.board.right)
    (hpUpper : upperOrigin.position.pending = some ⟨true, .advance c⟩) (hc : 0 < c)
    (hUpperInit : upperOrigin.position.board.right = LabeledWord.initial)
    (hUpperMode : upperOrigin.position.mode = some true)
    (hT : LabeledWord.SameStructure old.position.board.right upperOrigin.position.board.left)
    {as : List (Finset ℕ × ℕ)}
    (hraw : (LabeledCode.rootCursor L.lower L.marker).runAtoms as = some old.position.board.left)
    (hinc : (L.marker :: as.map Prod.snd).Pairwise (· < ·))
    (hpool : ∀ x ∈ as.map Prod.snd, x ∈ H) : ¬ blue.CliqueFree 3 := by
  obtain ⟨J, hJH, hJ, hJfresh, fine, hfromFine, hwinFine, _hnFine, _hrFine,
      hFineRoot, hFineBody, _hFineStrict, frontAtoms, hfullRun, hfullPool, M, hMfrom⟩ :=
    reserved_inside_preparation hHN hH blue htri hroot origin old upperOrigin L hwinOrigin
      hopening hboardOrigin hB hfromUpper hOldBody hpUpper hc hUpperInit hUpperMode hraw hinc hpool
  have hbeforeOld : LabeledWord.BeforeBody L.pivot old.position.board.left :=
    ⟨hOldRoot ▸ L.pivot_lower, by simpa only [hOldBody] using L.penultimate_lt_pivot⟩
  have hnext : ∀ k ∈ old.position.board.left.rootLabel,
      old.position.board.left.bodyLabels.length < k → L.pivot ≤ k := by
    intro k hk hlt
    rcases L.lower_bounds k (hOldRoot ▸ hk) with heq | hle
    · exact heq.ge
    · rw [hOldBody] at hlt
      exact (not_lt_of_ge hle hlt).elim
  have hbeforeFine : LabeledWord.BeforeBody L.pivot fine.position.board.left :=
    ⟨hFineRoot ▸ L.pivot_upper, by simpa only [hFineBody] using L.firstUpper_lt_pivot⟩
  exact inside_singleton_bridge_triangle hHN hJH hJ blue origin old fine upperOrigin
    (hwinOrigin.of_reachable (exactGame N blue) hfromOld) hwinFine hfromOld hfromFine hall
    (follow_mode_some hfromOld hmodeOrigin) (follow_mode_some hfromFine hmodeOrigin) hpOld
    (LabeledWord.rootRelabel_sameStructure L.upper old.position.board.left).symm
    hfullRun hfullPool hJfresh hOldRel hOldNo hbeforeOld hnext hbeforeFine
    (fun k hk => L.lower_le_pivot k (hOldRoot ▸ hk))
    (fun k hk => (L.upper_bounds k (hFineRoot ▸ hk)).2) hTRel hTLast hT ⟨M, hMfrom⟩

#print axioms inside_singleton_insertion_triangle

end Erdos591.Positive.Game.Payoff
