import ErdosProblems.Erdos591.ForcedMoves
import ErdosProblems.Erdos591.ZeroResponse

/-!
# A finish request cannot swallow an unread selected body

After the root is fixed, a completion response appends only empty body
labels. Every unread selected body's persistent slot would therefore be
empty, contradicting the exact root-label/body-label equality of any
clear terminal pair.
-/

namespace Erdos591.Positive.Game

namespace LabeledWord

theorem read_empty_bodyLabels {w v : LabeledWord} {n : ℕ} (hw : w.parser ≠ .start)
    (hr : w.read ∅ n = some v) : ∃ k, v.bodyLabels = w.bodyLabels ++ List.replicate k ∅ := by
  cases hp : w.parser with
  | start => exact (hw hp).elim
  | blocks r =>
      cases r with
      | zero => simp [LabeledWord.read, hp, Parser.step] at hr
      | succ r =>
          have heq : w.record ∅ n (Parser.normalize r n) = v := by
            simpa [LabeledWord.read, hp, Parser.step] using hr
          exact ⟨1, by simp [← heq, record, hp]⟩
  | leaves r k =>
      have heq : w.record ∅ n (Parser.normalize r k) = v := by
        simpa [LabeledWord.read, hp, Parser.step] using hr
      exact ⟨0, by simp [← heq, record, hp]⟩

theorem zero_run_bodyLabels (D : ResponseParser LabeledWord)
    (hstep : ∀ w n, D.step w n = w.read ∅ n)
    {w v : LabeledWord} {xs : List ℕ} (hw : w.parser ≠ .start)
    (hrun : D.run w xs = some v) :
    ∃ k, v.bodyLabels = w.bodyLabels ++ List.replicate k ∅ := by
  induction xs generalizing w with
  | nil =>
      cases he : D.stopped w with
      | false => simp [ResponseParser.run, he] at hrun
      | true =>
          have heq : w = v := by simpa [ResponseParser.run, he] using hrun
          exact ⟨0, by simp [heq]⟩
  | cons n xs ih =>
      cases he : D.stopped w with
      | true => simp [ResponseParser.run, he] at hrun
      | false =>
          cases hr : w.read ∅ n with
          | none => simp [ResponseParser.run, he, hstep, hr] at hrun
          | some u =>
              have ht : D.run u xs = some v := by
                simpa [ResponseParser.run, he, hstep, hr] using hrun
              obtain ⟨a, ha⟩ := read_empty_bodyLabels hw hr
              obtain ⟨c, hc⟩ := ih (read_parser_ne_start hr) ht
              exact ⟨a + c, by rw [hc, ha, List.append_assoc, List.replicate_add]⟩

theorem finish_new_body_empty {w v : LabeledWord} {xs : List ℕ}
    (hw : w.parser ≠ .start) (hrun : finishParser.run w xs = some v) {i : ℕ}
    (hi : w.bodyLabels.length ≤ i) : v.bodyLabels.getD i ∅ = ∅ := by
  obtain ⟨k, hk⟩ := zero_run_bodyLabels finishParser (fun _ _ => rfl) hw hrun
  rw [hk, List.getD_append_right _ _ _ _ hi]
  simp

end LabeledWord

theorem Reply.finish_run {board last : Board} {side : Bool} {u : Finset ℕ}
    (h : Reply board ⟨side, .finish⟩ u last) :
    LabeledWord.finishParser.run (board.get side) (u.sort (· ≤ ·)) = some (last.get side) := by
  cases h with
  | finish side u w _ hr => simpa using hr

namespace Payoff

open Erdos591.Negative.Exact

theorem ClearSide.finish_no_future_body {w v : LabeledWord} {xs : List ℕ} {s t : G}
    (hc : ClearSide v s t) (hw : w.parser ≠ .start)
    (hrun : LabeledWord.finishParser.run w xs = some v) :
    ∀ i ∈ w.rootLabel, i ≤ w.bodyLabels.length := by
  have hlegal := LabeledWord.zero_run_legal _ (fun _ _ => rfl) hrun
  have hroot := hlegal.rootLabel_eq hw
  intro i hi
  by_contra hle
  have hlt : w.bodyLabels.length < i := by omega
  have himem : i ∈ v.rootLabel := by rw [hroot]; exact hi
  have hibound := (hc.root_bounds i himem).2
  have hnon : (v.bodyLabels.getD (i - 1) ∅).Nonempty := by
    apply (hc.root_mem_iff_body_nonempty (i := i - 1) (by omega)).mp
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ i)] using himem
  have hempty := LabeledWord.finish_new_body_empty hw hrun (i := i - 1) (by omega)
  rw [hempty] at hnon
  simp at hnon

theorem winning_finish_no_future_body {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} {q : Concrete.Hist N}
    (hwin : (exactGame N blue).ArchitectWins H b σ q)
    {board : Board} {side : Bool} {u : Finset ℕ}
    (hreply : Reply board ⟨side, .finish⟩ u q.position.board)
    (hw : (board.get side).parser ≠ .start) :
    ∀ i ∈ (board.get side).rootLabel, i ≤ (board.get side).bodyLabels.length := by
  obtain ⟨z, hqz, _, _, hz⟩ := winning_continuation hHN hH blue hwin
  obtain ⟨s, t, hc, _⟩ := hz.side_clear side
  obtain ⟨as, has, _⟩ :=
    (History.reachable_word_extension (follow_history_path hqz)).2 side
  have hsame := has.terminal_eq hreply.finish_terminal
  rw [hsame] at hc
  exact hc.finish_no_future_body hw hreply.finish_run

theorem winning_pending_finish_no_future_body {N H : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    {p : Concrete.Hist N} (hwin : (exactGame N blue).ArchitectWins H b σ p)
    {r : Request} (hp : p.position.pending = some r) (hcommand : r.command = .finish)
    (hw : (p.position.board.get r.side).parser ≠ .start) :
    ∀ i ∈ (p.position.board.get r.side).rootLabel,
      i ≤ (p.position.board.get r.side).bodyLabels.length := by
  have hk : (exactGame N blue).kind p = .builder :=
    (Concrete.kind_builder_iff (payoff blue) p).mpr ⟨r, hp⟩
  obtain ⟨u, hu, huH, hub⟩ := (exactGame N blue).response_exists_above hHN hH p hk (b p)
  have hf := FiniteResponseGame.FollowStep.builder (exactGame N blue) σ p u hk hu huH hub
  have hqwin := hwin.of_reachable (exactGame N blue) (Relation.ReflTransGen.single hf)
  have hreply := (Concrete.response_spec hu).reply_spec hp
  have hfinish : Reply p.position.board ⟨r.side, .finish⟩ u
      (Concrete.response p u).position.board := by
    cases r with
    | mk side command =>
        cases hcommand
        exact hreply
  exact winning_finish_no_future_body hHN hH blue hqwin hfinish hw

#print axioms winning_finish_no_future_body
#print axioms winning_pending_finish_no_future_body

end Payoff

end Erdos591.Positive.Game
