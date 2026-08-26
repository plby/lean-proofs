import ErdosProblems.Erdos591.RootPlanTransport
import ErdosProblems.Erdos591.EndpointOrder
import ErdosProblems.Erdos591.ReplySeparation

/-!
# A managed word and its delayed upper play

Before the last selected body keep a root plan; inside that body keep
a prepared reply. The target side and its unchanged other word are
retained in both cases. Exhausted selected indices can occur only in
the prepared case, where firing produces the shared upper first leaf.
-/

namespace Erdos591.Positive.Game.Relay

open Erdos591.Negative.Exact
open Payoff

inductive Managed (N H : Set ℕ) (blue : SimpleGraph G) (b : Concrete.Hist N → ℕ)
    (σ : (exactGame N blue).ArchitectStrategy) (targetSide mode : Bool)
    (other w : LabeledWord) : Type
  | root (R : RootPlan N H blue b σ w) (side : R.side = targetSide)
      (other_eq : R.target.position.board.get (!R.side) = other)
      (targetMode : R.target.position.mode = some mode)
  | prepared (P : PreparedBody N H blue b σ w) (side : P.side = targetSide)
      (other_eq : P.target.position.board.get (!P.side) = other)
      (targetMode : P.target.position.mode = some mode)
      (targetFirst : (P.target.position.board.get P.side).NoRootPassed)

def BothLast (board : Board) : Prop := ∀ s, ¬ Macro.Pending (board.get s)

namespace Managed

variable {N H : Set ℕ} {blue : SimpleGraph G} {b : Concrete.Hist N → ℕ}
  {σ : (exactGame N blue).ArchitectStrategy} {t mode : Bool} {other w : LabeledWord}

/-- The saved actual upper history, before its pending response. -/
def target : Managed N H blue b σ t mode other w → Concrete.Hist N
  | .root R _ _ _ => R.target
  | .prepared P _ _ _ _ => P.target

theorem unfinished (M : Managed N H blue b σ t mode other w) (hw : w.CursorInvariant) :
    w.terminal = false := by
  cases M with
  | root R _ _ _ => exact R.before_body.not_terminal hw
  | prepared P _ _ _ _ =>
      obtain ⟨r, k, hp⟩ := P.upto.parser_leaves hw
      simp [LabeledWord.terminal, hp]

theorem not_start (M : Managed N H blue b σ t mode other w) (hw : w.CursorInvariant) :
    w.parser ≠ .start := by
  cases M with
  | root R _ _ _ => exact R.not_start
  | prepared P _ _ _ _ =>
      obtain ⟨r, k, hp⟩ := P.upto.parser_leaves hw
      simp [hp]

theorem relaxed_of_last (M : Managed N H blue b σ t mode other w)
    (hw : w.CursorInvariant) (hlast : ¬ Macro.Pending w) : w.relaxed = true := by
  cases M with
  | root R _ _ _ => exact (hlast R.pending).elim
  | prepared P _ _ _ _ => exact P.upto.relaxed_of_eq hw (P.last_of_not_pending hlast)

theorem fire_fresh (M : Managed N H blue b σ t mode other w) (hHN : H ⊆ N)
    (hinc : w.coordinates.Pairwise (· < ·)) (hlast : ¬ Macro.Pending w) :
    ∃ q : Concrete.Hist N, (exactGame N blue).ArchitectWins H b σ q ∧
      q.position.pending = none ∧ (q.position.board.get t).coordinates = w.coordinates ∧
      (q.position.board.get t).relaxed = true ∧ q.position.board.get (!t) = other ∧
      q.position.mode = some mode ∧
      ∀ y ∈ (q.position.board.get (!t)).coordinates,
        y ≤ (q.position.board.get t).coordinates.getLastD 0 := by
  cases M with
  | root R _ _ _ => exact (hlast R.pending).elim
  | prepared P hside hother hmode _hfirst =>
      obtain ⟨q, hstep, hnone, hcoords, hrel, heq⟩ :=
        P.fire hHN hinc (P.last_of_not_pending hlast)
      refine ⟨q, P.targetWinning.of_reachable (exactGame N blue)
        (Relation.ReflTransGen.single hstep), hnone, by simpa [← hside] using hcoords,
        by simpa [← hside] using hrel, by simpa [← hside] using heq.trans hother,
        follow_mode_some (Relation.ReflTransGen.single hstep) hmode, ?_⟩
      have hsep := (FiniteResponseGame.FollowStep.next (exactGame N blue) hstep).reply_separation
        P.targetPending
      simpa [← hside] using hsep

theorem fire (M : Managed N H blue b σ t mode other w) (hHN : H ⊆ N)
    (hinc : w.coordinates.Pairwise (· < ·)) (hlast : ¬ Macro.Pending w) :
    ∃ q : Concrete.Hist N, (exactGame N blue).ArchitectWins H b σ q ∧
      q.position.pending = none ∧ (q.position.board.get t).coordinates = w.coordinates ∧
      (q.position.board.get t).relaxed = true ∧ q.position.board.get (!t) = other ∧
      q.position.mode = some mode := by
  obtain ⟨q, hw, hn, hc, hr, ho, hm, _⟩ := M.fire_fresh hHN hinc hlast
  exact ⟨q, hw, hn, hc, hr, ho, hm⟩

/-- Retain the actual upper path from an earlier reference history.
This permits globally uniform terminal properties to be transported
to a delayed play, not merely its original blue-pair winning property. -/
theorem fire_from (M : Managed N H blue b σ t mode other w) (hHN : H ⊆ N)
    (hinc : w.coordinates.Pairwise (· < ·)) (hlast : ¬ Macro.Pending w)
    (origin : Concrete.Hist N)
    (hfrom : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin M.target) :
    ∃ q : Concrete.Hist N,
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin q ∧
      (exactGame N blue).ArchitectWins H b σ q ∧ q.position.pending = none ∧
      (q.position.board.get t).coordinates = w.coordinates ∧
      (q.position.board.get t).relaxed = true ∧ q.position.board.get (!t) = other ∧
      q.position.mode = some mode ∧ ∀ y ∈ (q.position.board.get (!t)).coordinates,
        y ≤ (q.position.board.get t).coordinates.getLastD 0 := by
  cases M with
  | root R _ _ _ => exact (hlast R.pending).elim
  | prepared P hside hother hmode _hfirst =>
      obtain ⟨q, hstep, hnone, hcoords, hrel, heq⟩ :=
        P.fire hHN hinc (P.last_of_not_pending hlast)
      refine ⟨q, hfrom.tail hstep, P.targetWinning.of_reachable (exactGame N blue)
        (Relation.ReflTransGen.single hstep), hnone, by simpa [← hside] using hcoords,
        by simpa [← hside] using hrel, by simpa [← hside] using heq.trans hother,
        follow_mode_some (Relation.ReflTransGen.single hstep) hmode, ?_⟩
      have hsep := (FiniteResponseGame.FollowStep.next (exactGame N blue) hstep).reply_separation
        P.targetPending
      simpa [← hside] using hsep

end Managed

#print axioms Managed.fire
#print axioms Managed.fire_fresh
#print axioms Managed.fire_from

end Erdos591.Positive.Game.Relay
