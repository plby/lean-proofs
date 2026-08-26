import ErdosProblems.Erdos118.Reused591.BodyMarkerOnPath
import ErdosProblems.Erdos118.Reused591.ReachCriticalCheckpoint
import ErdosProblems.Erdos118.Reused591.LocalizedNonlastCheckpoint

namespace Erdos118.Reused591

/-!
# Reach the shared nonlast U anchor before T enters its last body

An auxiliary critical continuation identifies the selected U body by
its fixed rank. Extract its earlier positive marker request, retaining
the suffix to that checkpoint to prove that T is still pre-last.
The auxiliary reply at the anchor is not retained or prescribed.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem winning_spliced_anchor_marker {N H HU : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    {p : Concrete.Hist N} {B e g j k : ℕ} (U : SplicedRootLabels HU B e g j k)
    (hwin : (exactGame N blue).ArchitectWins H b σ p)
    (hn : p.position.pending = none)
    (hl : p.position.board.left.relaxed = true)
    (hr : p.position.board.right.relaxed = true)
    (hbeforeT : p.position.board.left.bodyLabels.length < p.position.board.left.lastSelectedBody)
    (hbeforeU : p.position.board.right.bodyLabels.length < U.anchor)
    (hUroot : p.position.board.right.rootLabel = U.upper)
    (hsep : ∀ x ∈ p.position.board.left.coordinates,
      x ≤ p.position.board.right.coordinates.getLastD 0)
    (hmode : p.position.mode = some true)
    (hfixed : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p z →
      (exactGame N blue).kind z = .terminal w →
        z.position.board.right.criticalBodyRank z.position.board.left.lastSelectedLabel.card = k)
    (hlast : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p z →
      (exactGame N blue).kind z = .terminal w → criticalLastColor z = false) :
    ∃ q d, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q ∧
      q.position.pending = some ⟨true, .advance d⟩ ∧ 0 < d ∧
      q.position.board.right.markerEvent = true ∧
      q.position.board.right.bodyLabels.length + 1 = U.anchor ∧
      q.position.board.right.rootLabel = U.upper ∧
      q.position.board.left.rootLabel = p.position.board.left.rootLabel ∧
      q.position.board.left.bodyLabels.length < q.position.board.left.lastSelectedBody := by
  obtain ⟨z, hpz, _hzn, hz⟩ :=
    winning_reach_critical_checkpoint hHN hH blue hwin hn hl hr hbeforeT hsep
  have hwinZ := hwin.of_reachable (exactGame N blue) hpz
  obtain ⟨hrank, _hnot⟩ := hz.localized_body_nonlast hHN hH blue hwinZ
    (follow_mode_some hpz hmode)
    (fun v w hzv hv => hfixed v w (hpz.trans hzv) hv)
    (fun v w hzv hv => hlast v w (hpz.trans hzv) hv)
  have hstartU := LabeledWord.relaxed_ne_start
    ((Position.history_dataInvariant p).2.1 true).1 hr
  have hstartT := LabeledWord.relaxed_ne_start
    ((Position.history_dataInvariant p).2.1 false).1 hl
  obtain ⟨us, hus, _⟩ :=
    (History.reachable_word_extension (follow_history_path hpz)).2 true
  have hrootZ : z.position.board.right.rootLabel = U.upper :=
    (hus.rootLabel_eq hstartU).trans hUroot
  have hbodyZ : z.position.board.right.bodyLabels.length = U.anchor :=
    finite_rank_injective z.position.board.right.rootLabel
      (of_decide_eq_true hz.right_relaxed).2.1 (hrootZ ▸ U.anchor_upper)
      (hrank.trans (by rw [hrootZ, U.anchor_upper_rank]))
  obtain ⟨q, d, hpq, hqz, hp, hd, hm, hi⟩ :=
    winning_body_marker_on_path hHN hH blue hwin true U.anchor hpz hstartU
      ⟨hUroot ▸ U.anchor_upper, hbeforeU⟩ (by
        intro hb
        simpa only [Board.get, hbodyZ, lt_self_iff_false] using hb.2)
  simp only [Board.get] at hm hi
  obtain ⟨ts, hts, _⟩ :=
    (History.reachable_word_extension (follow_history_path hpq)).2 false
  obtain ⟨vs, hvs, _⟩ :=
    (History.reachable_word_extension (follow_history_path hqz)).2 false
  obtain ⟨ws, hws, _⟩ :=
    (History.reachable_word_extension (follow_history_path hpq)).2 true
  have hstartQT := hts.parser_ne_start hstartT
  have hrootT : q.position.board.left.rootLabel = p.position.board.left.rootLabel :=
    hts.rootLabel_eq hstartT
  have hlastT : z.position.board.left.lastSelectedBody =
      q.position.board.left.lastSelectedBody :=
    congrArg (fun C : Finset ℕ => C.sup id) (hvs.rootLabel_eq hstartQT)
  have hbodyT : q.position.board.left.bodyLabels.length ≤
      z.position.board.left.bodyLabels.length := (hvs.bodyLabels_prefix hstartQT).length_le
  refine ⟨q, d, hpq, hp, hd, hm, hi,
    (hws.rootLabel_eq hstartU).trans hUroot, hrootT, ?_⟩
  exact hbodyT.trans_lt (by simpa only [hlastT] using hz.left_before)

#print axioms winning_spliced_anchor_marker

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
