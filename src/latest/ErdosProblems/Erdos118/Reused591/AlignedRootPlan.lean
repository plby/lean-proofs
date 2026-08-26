import ErdosProblems.Erdos118.Reused591.AlignedRootReplay
import ErdosProblems.Erdos118.Reused591.RootPlanTransport

namespace Erdos118.Reused591

/-!
# An aligned root reservation up to the penultimate lower body

The saved upper initial response is fired at the shared index, not at
the lower maximum. The lower last selected body stays in the future.
All transported atoms come from actual conservative history moves.
-/

namespace Erdos591.Positive.Game.Relay

open Erdos591.Negative.Exact
open Payoff

structure AlignedRootPlan (N H : Set ℕ) (blue : SimpleGraph G)
    (b : Concrete.Hist N → ℕ) (σ : (exactGame N blue).ArchitectStrategy) (w : LabeledWord) where
  target : Concrete.Hist N
  side : Bool
  budget : ℕ
  lowerSize : ℕ
  upperSize : ℕ
  labels : AlignedRootLabels H budget lowerSize upperSize
  targetPending : target.position.pending = some ⟨side, .advance upperSize⟩
  targetInitial : target.position.board.get side = LabeledWord.initial
  targetBound : max target.position.bound (b target) ≤ budget
  targetWinning : (exactGame N blue).ArchitectWins H b σ target
  atoms : List (Finset ℕ × ℕ)
  run : LabeledWord.LegalRun (LabeledCode.rootCursor labels.lower labels.marker) atoms w
  pool : ∀ a ∈ atoms, a.2 ∈ H ∧ budget < a.2
  before : w.bodyLabels.length < labels.shared

namespace AlignedRootPlan

variable {N H : Set ℕ} {blue : SimpleGraph G} {b : Concrete.Hist N → ℕ}
  {σ : (exactGame N blue).ArchitectStrategy} {w v : LabeledWord}

theorem not_start (R : AlignedRootPlan N H blue b σ w) : w.parser ≠ .start :=
  R.run.parser_ne_start (by simp [LabeledCode.rootCursor])

theorem rootLabel (R : AlignedRootPlan N H blue b σ w) : w.rootLabel = R.labels.lower := by
  simpa [LabeledCode.rootCursor] using
    R.run.rootLabel_eq (by simp [LabeledCode.rootCursor])

theorem before_body (R : AlignedRootPlan N H blue b σ w) :
    LabeledWord.BeforeBody R.labels.shared w := ⟨R.rootLabel ▸ R.labels.shared_lower, R.before⟩

theorem pending (R : AlignedRootPlan N H blue b σ w) : Macro.Pending w :=
  Or.inl ⟨R.labels.shared, R.before_body⟩

theorem coordinates (R : AlignedRootPlan N H blue b σ w) :
    w.coordinates = R.labels.marker :: R.atoms.map Prod.snd := by
  simpa [LabeledCode.rootCursor] using LabeledWord.runAtoms_coordinates R.run.run

theorem budget_lt_bound {p : Concrete.Hist N} {s : Bool}
    (R : AlignedRootPlan N H blue b σ (p.position.board.get s)) :
    R.budget < p.position.bound := by
  have hm : R.labels.marker ∈ (p.position.board.get s).coordinates := by
    rw [R.coordinates]
    simp
  exact R.labels.marker_fresh.2.trans_le ((Position.history_dataInvariant p).1 _
    (p.position.board.get_support_subset s (LabeledWord.coordinate_mem_support hm))).2.2

def move (R : AlignedRootPlan N H blue b σ w) {ys : List (Finset ℕ × ℕ)}
    (h : LabeledWord.LegalRun w ys v)
    (hpool : ∀ a ∈ ys, a.2 ∈ H ∧ R.budget < a.2)
    (hbefore : v.bodyLabels.length < R.labels.shared) : AlignedRootPlan N H blue b σ v where
  target := R.target
  side := R.side
  budget := R.budget
  lowerSize := R.lowerSize
  upperSize := R.upperSize
  labels := R.labels
  targetPending := R.targetPending
  targetInitial := R.targetInitial
  targetBound := R.targetBound
  targetWinning := R.targetWinning
  atoms := R.atoms ++ ys
  run := R.run.append h
  pool := by
    intro a ha
    exact (List.mem_append.mp ha).elim (R.pool a) (hpool a)
  before := hbefore

theorem follow {p q : Concrete.Hist N} (s : Bool)
    (R : AlignedRootPlan N H blue b σ (p.position.board.get s))
    (hHN : H ⊆ N) (hH : H.Infinite)
    (hwin : (exactGame N blue).ArchitectWins H b σ p)
    (hstep : (exactGame N blue).FollowStep σ H b p q)
    (haway : p.position.board.get s ≠ q.position.board.get s →
      ¬ ((p.position.board.get s).markerEvent = true ∧
        (p.position.board.get s).bodyLabels.length + 1 = R.labels.shared)) :
    ∃ Q : AlignedRootPlan N H blue b σ (q.position.board.get s),
      Q.target = R.target ∧ Q.side = R.side ∧ HEq Q.labels R.labels := by
  by_cases heq : p.position.board.get s = q.position.board.get s
  · rw [← heq]
    exact ⟨R, rfl, rfl, HEq.rfl⟩
  have hnext := History.Next.position_next
    (FiniteResponseGame.FollowStep.next (exactGame N blue) hstep)
  have hbefore : (q.position.board.get s).bodyLabels.length < R.labels.shared := by
    cases hp : p.position.pending with
    | none => exact (heq (by rw [hnext.board_eq_of_no_pending hp])).elim
    | some r =>
        obtain ⟨u, hr⟩ := hnext.reply_of_pending hp
        have hside : s = r.side := by
          by_contra hn
          have hs : s = !r.side := Bool.eq_not_of_ne hn
          exact heq (by simpa [hs] using hr.other_eq.symm)
        cases r with
        | mk t command =>
            have hst : s = t := hside
            subst t
            cases command with
            | finish =>
                exact ((winning_pending_finish_not_pending hHN hH blue hwin hp rfl) R.pending).elim
            | advance d =>
                exact (hr.advance_before_body_or_marker R.before_body R.not_start).resolve_right
                  (haway heq) |>.2
  obtain ⟨as, has, hpool⟩ := follow_step_word_inputs_fresh hstep s
  have hfresh : ∀ a ∈ as, a.2 ∈ H ∧ R.budget < a.2 := by
    intro a ha
    exact ⟨(hpool a ha).1, R.budget_lt_bound.trans
      ((le_max_left _ _).trans_lt (hpool a ha).2)⟩
  exact ⟨R.move has hfresh hbefore, rfl, rfl, HEq.rfl⟩

theorem fire_first (R : AlignedRootPlan N H blue b σ w) (hHN : H ⊆ N) (hH : H.Infinite)
    (hm : w.markerEvent = true) (hindex : w.bodyLabels.length + 1 = R.labels.shared)
    (hinc : w.coordinates.Pairwise (· < ·)) :
    ∃ q d, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) R.target q ∧
      q.position.pending = some ⟨R.side, .advance d⟩ ∧ 0 < d ∧
      q.position.board.get R.side = LabeledWord.rootRelabel R.labels.upper w ∧
      (q.position.board.get R.side).markerEvent = true ∧
      (q.position.board.get R.side).NoRootPassed ∧
      q.position.board.get (!R.side) = R.target.position.board.get (!R.side) := by
  apply winning_aligned_root_request hHN hH blue R.target R.targetWinning R.side R.labels
    R.targetPending R.targetInitial R.targetBound R.run.run hm hindex
    (by simpa only [R.coordinates] using hinc)
  intro x hx
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
  exact (R.pool a ha).1

#print axioms follow
#print axioms fire_first

end AlignedRootPlan

end Erdos591.Positive.Game.Relay

end Erdos118.Reused591
