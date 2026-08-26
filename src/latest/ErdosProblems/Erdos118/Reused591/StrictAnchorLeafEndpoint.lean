import ErdosProblems.Erdos118.Reused591.AnchorEndpointRank
import ErdosProblems.Erdos118.Reused591.PreparedSelectionLastBody
import ErdosProblems.Erdos118.Reused591.PreparedSelectionReach
import ErdosProblems.Erdos118.Reused591.PrepareSelectionHistory
import ErdosProblems.Erdos118.Reused591.LastCriticalLabels
import ErdosProblems.Erdos118.Reused591.OvertakenOtherRelaxed

namespace Erdos118.Reused591

/-!
# Reach the upper U anchor's last leaf with both lower first leaves still saved

The lower U first leaf is its upper anchor's last leaf. At that endpoint
the exact suffix count puts T at rank K, before its saved rank K+1.
Both saved replies are retained with their original labels and targets.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact
open Relay

theorem strict_anchor_leaf_endpoint {N H HU : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (p oldU : Concrete.Hist N) {B K c BU e g j k : ℕ}
    (U : SplicedRootLabels HU BU e g j (k + 1)) (E : LastFirstLabels H B K c)
    (P : PreparedSelection N H blue b σ p.position.board.left)
    (hwin : (exactGame N blue).ArchitectWins H b σ p)
    (hwinU : (exactGame N blue).ArchitectWins H b σ oldU)
    (hp : p.position.pending = some ⟨true, .advance K⟩)
    (hpU : oldU.position.pending = some ⟨true, .advance c⟩)
    (hm : p.position.board.right.markerEvent = true)
    (hmU : oldU.position.board.right.markerEvent = true)
    (hshape : LabeledWord.SameStructure p.position.board.right oldU.position.board.right)
    (hBp : max p.position.bound (b p) ≤ B)
    (hBU : max oldU.position.bound (b oldU) ≤ B)
    (hTrel : p.position.board.left.relaxed = true)
    (hTroot : ∀ i ∈ p.position.board.left.rootLabel, i ≤ p.position.board.left.bodyLabels.length)
    (hPrank : (P.lowerLabel.filter (fun x => x ≤ P.labels.pivot)).card = K + 1)
    (hUroot : p.position.board.right.rootLabel = U.upper)
    (hUbody : p.position.board.right.bodyLabels.length + 1 = U.anchor)
    (hmode : p.position.mode = some true)
    (hvalid : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p z →
      (exactGame N blue).kind z = .terminal w →
        z.position.board.right.CriticalPairSpec z.position.board.left.lastSelectedLabel.card
          (z.position.board.right.criticalPair z.position.board.left.lastSelectedLabel.card) ∧
        z.position.board.right.criticalBodyRank z.position.board.left.lastSelectedLabel.card = k ∧
        criticalLastColor z = true) :
    ∃ q, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q ∧
      q.position.pending = none ∧ q.position.board.left.relaxed = true ∧
      q.position.board.right.relaxed = true ∧ q.position.board.right.NoLeafPending ∧
      (∀ x ∈ q.position.board.left.coordinates, x ≤ q.position.board.right.coordinates.getLastD 0) ∧
      (q.position.board.left.currentLabel.filter
        (fun x => x ≤ q.position.board.left.leafIndex)).card = K ∧
      q.position.board.left.leafIndex < P.labels.pivot ∧
      ∃ PT : PreparedSelection N H blue b σ q.position.board.left,
        PT.target = P.target ∧ PT.side = P.side ∧ PT.stem = P.stem ∧
        PT.lowerLabel = P.lowerLabel ∧ PT.labels.pivot = P.labels.pivot ∧
        PT.labels.upper = P.labels.upper ∧
      ∃ PU : PreparedSelection N H blue b σ q.position.board.right,
        PU.target = oldU ∧ PU.side = true ∧ PU.stem = p.position.board.right ∧
        PU.lowerLabel = E.lower ∧ PU.labels.pivot = E.pivot ∧ PU.labels.upper = E.upper ∧
        q.position.board.right.leafIndex = PU.labels.pivot := by
  obtain ⟨first, hpFirst, hFirstNone, hFirstRel, _hFirstOther, Q, hQtarget, hQside,
      _hQview, hQstem, hQlower, hQpivot, hQupper⟩ :=
    prepare_selection hHN hH blue hwinU true true E.lower E.lower_card E.upper_first_view
      E.pivot_lower E.lower_fresh hp hpU hm hmU hshape hBp hBU
  have hFirstSep :=
    (FiniteResponseGame.FollowStep.next (exactGame N blue) hpFirst).reply_separation hp
  obtain ⟨q, hFirstQ, hqn, hqr, hqsep, QU, hQUtarget, hQUside, _hQUview, hQUstem,
      hQUindex, hQUlower, hQUpivot, hQUupper⟩ := Q.reach_target hHN hH blue true
    (hwin.of_reachable (exactGame N blue) (.single hpFirst)) hFirstNone hFirstSep
  have hpq := (Relation.ReflTransGen.single hpFirst).trans hFirstQ
  have hwinQ := hwin.of_reachable (exactGame N blue) hpq
  have hQUlabel : QU.lowerLabel = E.lower := hQUlower.trans hQlower
  have hQUfirst : QU.stem = p.position.board.right := hQUstem.trans hQstem
  have hQUpiv : QU.labels.pivot = E.pivot := hQUpivot.trans hQpivot
  have hcurrentU : q.position.board.right.currentLabel = E.lower :=
    QU.currentLabel.trans hQUlabel
  have hqUno : q.position.board.right.NoLeafPending := by
    intro x hx
    change q.position.board.right.leafIndex = QU.labels.pivot at hQUindex
    rw [hQUindex, hQUpiv]
    exact E.lower_le x (hcurrentU ▸ hx)
  obtain ⟨as, has, _⟩ := follow_word_inputs hpq 0 (fun _ => Nat.zero_le _) false
  obtain ⟨initialAtoms, hinit⟩ := History.word_run p false
  have hpos : 0 < q.position.board.left.coordinates.length :=
    (hinit.relaxed_coordinates_pos hTrel).trans_le has.coordinates_prefix.length_le
  obtain ⟨hql, horder⟩ := winning_overtaken_other_relaxed hHN hH blue hwinQ true hqr hpos hqsep
  have hstart := LabeledWord.relaxed_ne_start ((Position.history_dataInvariant p).2.1 false).1 hTrel
  have hlabels := (has.last_body_relaxed_labels hstart hTroot hql).1
  change q.position.board.left.bodyLabels = p.position.board.left.bodyLabels at hlabels
  have hcurrentT : q.position.board.left.currentLabel = P.lowerLabel := by
    simpa only [LabeledWord.currentLabel, hlabels] using P.currentLabel
  have hlastT : q.position.board.left.bodyLabels.length =
      q.position.board.left.lastSelectedBody := by
    apply le_antisymm (Finset.le_sup (f := id) (of_decide_eq_true hql).2.1)
    apply Finset.sup_le
    intro i hi
    have hrootEq := has.rootLabel_eq hstart
    change i ≤ q.position.board.left.bodyLabels.length
    rw [hlabels]
    exact hTroot i (hrootEq ▸ hi)
  have hbodyU : q.position.board.right.bodyLabels.length = U.anchor := by
    have he := QU.body_length
    simp only [Board.get, hQUfirst] at he
    exact he.trans hUbody
  obtain ⟨z, hqz, hz⟩ := hwinQ.exists_terminal (exactGame N blue) hHN hH
  obtain ⟨_hn, _hd, hpay⟩ := (Concrete.kind_terminal_iff (payoff blue) z true).mp hz
  have hmodeZ := follow_mode_some (hpq.trans hqz) hmode
  have hwinning : Winning blue true z.position.board := by
    apply (payoff_true_iff blue true _).mp
    simpa only [hmodeZ, Option.getD_some] using hpay
  obtain ⟨s, t, hc, _hblue, hmax⟩ := hwinning
  obtain ⟨rightAtoms, hrightRun, _⟩ := follow_word_inputs hqz 0 (fun _ => Nat.zero_le _) true
  have hrootZ : z.position.board.right.rootLabel = U.upper := by
    have he := QU.rootLabel
    simp only [Board.get, hQUfirst] at he
    exact (hrightRun.rootLabel_eq (LabeledWord.relaxed_ne_start
      ((Position.history_dataInvariant q).2.1 true).1 hqr)).trans (he.trans hUroot)
  have hdata := hvalid z true (hpq.trans hqz) hz
  have hrank := history_anchor_last_rank U (follow_history_path hqz) hc hmax hql hqr horder
    hlastT hbodyU hqUno hrootZ hdata.1 hdata.2.1 hdata.2.2
  rw [hcurrentU, E.lower_card] at hrank
  have hbefore : q.position.board.left.leafIndex < P.labels.pivot := by
    by_contra hn
    have hle := finite_rank_mono P.lowerLabel (le_of_not_gt hn)
    rw [hPrank, ← hcurrentT, hrank] at hle
    omega
  obtain ⟨PT, hPTtarget, hPTside, hPTstem, hPTlower, hPTpivot, hPTupper⟩ :=
    P.move_of_last_body false hpq hTroot hql hbefore.le
  exact ⟨q, hpq, hqn, hql, hqr, hqUno, hqsep, hrank, hbefore,
    PT, hPTtarget, hPTside, hPTstem, hPTlower, hPTpivot, hPTupper,
    QU, hQUtarget.trans hQtarget, hQUside.trans hQside, hQUfirst, hQUlabel, hQUpiv,
    hQUupper.trans hQupper, hQUindex⟩

#print axioms strict_anchor_leaf_endpoint

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
