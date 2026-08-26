import ErdosProblems.Erdos118.Reused591.ReachCriticalCheckpoint
import ErdosProblems.Erdos118.Reused591.LocalizedNonlastCheckpoint
import ErdosProblems.Erdos118.Reused591.PrepareSelectionHistory
import ErdosProblems.Erdos118.Reused591.PreparedSelectionTransport
import ErdosProblems.Erdos118.Reused591.LastCriticalLabels

namespace Erdos118.Reused591

/-!
# Preserve the chosen U anchor and its delayed lower reply to the critical checkpoint

The anchor label is chosen at actual requests. Fixed critical body
rank keeps the subsequent checkpoint in that same body, and the
nonlast color keeps its pivot (the last upper selection) unread.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact
open Relay

theorem nonlast_prepared_anchor_checkpoint {N H HU : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (p oldU : Concrete.Hist N) {B d c BU e g j k : ℕ}
    (U : SplicedRootLabels HU BU e g j k) (E : LastFirstLabels H B d c)
    (hwin : (exactGame N blue).ArchitectWins H b σ p)
    (hwinU : (exactGame N blue).ArchitectWins H b σ oldU)
    (hp : p.position.pending = some ⟨true, .advance d⟩)
    (hpU : oldU.position.pending = some ⟨true, .advance c⟩)
    (hm : p.position.board.right.markerEvent = true)
    (hmU : oldU.position.board.right.markerEvent = true)
    (hshape : LabeledWord.SameStructure p.position.board.right oldU.position.board.right)
    (hBp : max p.position.bound (b p) ≤ B)
    (hBU : max oldU.position.bound (b oldU) ≤ B)
    (hbeforeT : p.position.board.left.bodyLabels.length < p.position.board.left.lastSelectedBody)
    (hposT : 0 < p.position.board.left.coordinates.length)
    (hrootU : p.position.board.right.rootLabel = U.upper)
    (hbodyU : p.position.board.right.bodyLabels.length + 1 = U.anchor)
    (hmode : p.position.mode = some true)
    (hfixed : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p z →
      (exactGame N blue).kind z = .terminal w →
        z.position.board.right.criticalBodyRank z.position.board.left.lastSelectedLabel.card = k)
    (hlast : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p z →
      (exactGame N blue).kind z = .terminal w → criticalLastColor z = false) :
    ∃ q, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q ∧
      q.position.pending = none ∧ CriticalCheckpoint q ∧
      q.position.board.right.rootLabel = U.upper ∧
      q.position.board.right.bodyLabels.length = U.anchor ∧
      q.position.board.right.currentLabel = E.lower ∧
      q.position.board.right.leafIndex < E.pivot ∧
      ∃ P : PreparedSelection N H blue b σ q.position.board.right,
        P.target = oldU ∧ P.side = true ∧ P.stem = p.position.board.right ∧
        P.lowerLabel = E.lower ∧ P.labels.pivot = E.pivot ∧ P.labels.upper = E.upper := by
  obtain ⟨first, hpf, hfn, hfr, hfo, P, hPt, hPs, _hPv, hPstem, hPlower,
      hPpivot, hPupper⟩ :=
    prepare_selection hHN hH blue hwinU true true E.lower E.lower_card E.upper_first_view
      E.pivot_lower E.lower_fresh hp hpU hm hmU hshape hBp hBU
  simp only [Board.get, Bool.not_true] at hfr hfo hPstem
  have hwinF := hwin.of_reachable (exactGame N blue) (.single hpf)
  have hfsep : ∀ x ∈ first.position.board.left.coordinates,
      x ≤ first.position.board.right.coordinates.getLastD 0 := by
    simpa only [Board.get, Bool.not_true] using
      (FiniteResponseGame.FollowStep.next (exactGame N blue) hpf).reply_separation hp
  have hfpos : 0 < first.position.board.left.coordinates.length := by
    simpa only [hfo] using hposT
  obtain ⟨hfl, _hforder⟩ := winning_overtaken_other_relaxed hHN hH blue hwinF true hfr hfpos hfsep
  have hfroot : first.position.board.right.rootLabel = U.upper := by
    have he := P.rootLabel
    simp only [Board.get, hPstem] at he
    exact he.trans hrootU
  have hfbody : first.position.board.right.bodyLabels.length = U.anchor := by
    have he := P.body_length
    simp only [Board.get, hPstem] at he
    exact he.trans hbodyU
  obtain ⟨q, hfq, hqn, hq⟩ := winning_reach_critical_checkpoint hHN hH blue hwinF hfn
    hfl hfr (by simpa only [hfo] using hbeforeT) hfsep
  have hpq := (Relation.ReflTransGen.single hpf).trans hfq
  obtain ⟨hqrank, hqnot⟩ := hq.localized_body_nonlast hHN hH blue
    (hwin.of_reachable (exactGame N blue) hpq) (follow_mode_some hpq hmode)
    (fun z w hqz hz => hfixed z w (hpq.trans hqz) hz)
    (fun z w hqz hz => hlast z w (hpq.trans hqz) hz)
  obtain ⟨as, has, hpool⟩ := follow_word_inputs_above_bound hfq true
  have hstart := LabeledWord.relaxed_ne_start
    ((Position.history_dataInvariant first).2.1 true).1 hfr
  have hqroot : q.position.board.right.rootLabel = U.upper :=
    (has.rootLabel_eq hstart).trans hfroot
  have hqbody : q.position.board.right.bodyLabels.length = U.anchor :=
    finite_rank_injective q.position.board.right.rootLabel
      (of_decide_eq_true hq.right_relaxed).2.1 (hqroot ▸ U.anchor_upper)
      (hqrank.trans (by rw [hqroot, U.anchor_upper_rank]))
  have hlabels : q.position.board.right.bodyLabels = first.position.board.right.bodyLabels :=
    ((has.bodyLabels_prefix hstart).eq_of_length_le
      (by simp only [Board.get, hqbody, hfbody, le_refl])).symm
  have hcurrent : q.position.board.right.currentLabel = E.lower := by
    simpa only [LabeledWord.currentLabel, hlabels, Board.get] using P.currentLabel.trans hPlower
  have hbefore : q.position.board.right.leafIndex < E.pivot := by
    by_contra hn
    apply hqnot
    intro x hx
    exact (E.lower_le x (hcurrent ▸ hx)).trans (le_of_not_gt hn)
  have hup : LabeledWord.UpToLeaf P.labels.pivot q.position.board.right :=
    ⟨(of_decide_eq_true hq.right_relaxed).2.1, by
      rw [hPpivot, hcurrent]
      exact E.pivot_lower, by rw [hPpivot]; exact hbefore.le⟩
  have hfresh : ∀ a ∈ as, a.2 ∈ H ∧ P.budget < a.2 := by
    intro a ha
    exact ⟨(hpool a ha).1, P.budget_lt_bound.trans (hpool a ha).2⟩
  exact ⟨q, hpq, hqn, hq, hqroot, hqbody, hcurrent, hbefore,
    P.move has hlabels hfresh hup, hPt, hPs, hPstem, hPlower, hPpivot, hPupper⟩

#print axioms nonlast_prepared_anchor_checkpoint

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
