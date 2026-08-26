import ErdosProblems.Erdos591.FinishLeafPrefix
import ErdosProblems.Erdos591.MacroPending

/-!
# A winning architect cannot finish with a selected position pending

A pending selected leaf occurs strictly inside the actual completion
response. Clarity would require a cut there, but the fixed other-word
prefix lies below every new response coordinate; later coordinates lie
above the whole response. Permanent cut status gives the contradiction.
Together with the empty unread-body-label obstruction, this proves the
full finish restriction for the concrete conservative game.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem winning_reply_cannot_finish_leaf {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} {p q : Concrete.Hist N}
    (hwin : (exactGame N blue).ArchitectWins H b σ q) {side : Bool} {u : Finset ℕ}
    (hreply : Reply p.position.board ⟨side, .finish⟩ u q.position.board)
    (hfresh : ∀ x ∈ u, p.position.bound < x)
    (hsel : (p.position.board.get side).bodyLabels.length ∈
      (p.position.board.get side).rootLabel) {j : ℕ}
    (hj : j ∈ (p.position.board.get side).currentLabel)
    (hfuture : (p.position.board.get side).leafIndex < j) : False := by
  have hw := ((Position.history_dataInvariant p).2.1 side).1
  have hfinish := hreply.finish_run
  obtain ⟨k, cur, hkpos, hklen, hpre, htail, hrel⟩ :=
    LabeledWord.finish_pending_leaf_prefix hw hfinish hsel hj hfuture
  have hcur : cur.coordinates =
      (p.position.board.get side).coordinates ++ (u.sort (· ≤ ·)).take k := by
    simpa [List.map_map] using LabeledWord.runAtoms_coordinates hpre.run
  have hcoords : (q.position.board.get side).coordinates =
      (p.position.board.get side).coordinates ++ u.sort (· ≤ ·) :=
    (LabeledWord.finish_spec hw.1 hfinish).2.1
  let K := (p.position.board.get side).coordinates.length + k - 1
  have hcurLen : cur.coordinates.length = K + 1 := by
    rw [hcur, List.length_append, List.length_take, Nat.min_eq_left hklen.le]
    dsimp only [K]
    omega
  have hK : K + 1 < (q.position.board.get side).coordinates.length := by
    rw [hcoords, List.length_append]
    dsimp only [K]
    omega
  obtain ⟨z, hqz, _, _, hz⟩ := winning_continuation hHN hH blue hwin
  obtain ⟨s, t, hc, hother⟩ := hz.side_clear side
  obtain ⟨as, has⟩ := History.word_run p side
  obtain ⟨bs, hbs, _⟩ :=
    (History.reachable_word_extension (follow_history_path hqz)).2 side
  have hcut := hc.cut_of_relaxed_prefix (has.append hpre) (htail.append hbs) hcurLen hrel
  have hcut' : Cut (q.position.board.get side).coordinates
      (q.position.board.get (!side)).coordinates K := by
    apply (history_cut_iff (follow_history_path hqz) side hK).mp
    simpa only [hc.coordinates, hother] using hcut
  obtain ⟨_, y, hy, hlo, _⟩ := hcut'
  rw [hreply.other_eq] at hy
  have hybound := ((Position.history_dataInvariant p).1 y
    (p.position.board.get_support_subset (!side) (LabeledWord.coordinate_mem_support hy))).2.2
  have hKge : (p.position.board.get side).coordinates.length ≤ K := by dsimp only [K]; omega
  have hKsub : K - (p.position.board.get side).coordinates.length = k - 1 := by
    dsimp only [K]
    omega
  rw [hcoords, List.getD_append_right _ _ _ _ hKge, hKsub] at hlo
  have hn : (u.sort (· ≤ ·)).getD (k - 1) 0 ∈ u := by
    rw [List.getD_eq_getElem _ _ (by omega)]
    have hm := List.getElem_mem (l := u.sort (· ≤ ·)) (n := k - 1) (by omega)
    exact (Finset.mem_sort (· ≤ ·)).mp hm
  exact not_lt_of_ge hybound ((hfresh _ hn).trans hlo)

theorem winning_pending_finish_not_pending {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} {p : Concrete.Hist N}
    (hwin : (exactGame N blue).ArchitectWins H b σ p) {r : Request}
    (hp : p.position.pending = some r) (hcommand : r.command = .finish) :
    ¬ Macro.Pending (p.position.board.get r.side) := by
  intro hpending
  have hw := ((Position.history_dataInvariant p).2.1 r.side).1
  have hstart : (p.position.board.get r.side).parser ≠ .start := by
    intro heq
    exact Macro.not_pending_of_no_outstanding hw
      (by simp [heq, LabeledWord.outstandingBodies])
      (by simp [heq, LabeledWord.outstandingLeaves]) hpending
  rcases hpending with ⟨i, hi, hfuture⟩ | ⟨hsel, j, hj, hfuture⟩
  · have hle := winning_pending_finish_no_future_body hHN hH blue hwin hp hcommand hstart i hi
    omega
  · have hk : (exactGame N blue).kind p = .builder :=
      (Concrete.kind_builder_iff (payoff blue) p).mpr ⟨r, hp⟩
    obtain ⟨u, hu, huH, hub⟩ := (exactGame N blue).response_exists_above hHN hH p hk (b p)
    have hf := FiniteResponseGame.FollowStep.builder (exactGame N blue) σ p u hk hu huH hub
    have hqwin := hwin.of_reachable (exactGame N blue) (Relation.ReflTransGen.single hf)
    have hrep := Concrete.response_spec hu
    have hreply := hrep.reply_spec hp
    have hfinish : Reply p.position.board ⟨r.side, .finish⟩ u
        (Concrete.response p u).position.board := by
      cases r with
      | mk side command =>
          cases hcommand
          exact hreply
    exact winning_reply_cannot_finish_leaf hHN hH blue hqwin hfinish hrep.fresh hsel hj hfuture

#print axioms winning_pending_finish_not_pending

end Erdos591.Positive.Game.Payoff
