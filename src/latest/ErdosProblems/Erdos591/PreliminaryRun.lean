import ErdosProblems.Erdos591.WinningPreliminaryEndpoint
import ErdosProblems.Erdos591.PreliminaryPivotRanks
import ErdosProblems.Erdos591.OvertakenOtherRelaxed
import ErdosProblems.Erdos591.LastBodyEndpoint
import ErdosProblems.Erdos591.ReachSelectedLeaf
import ErdosProblems.Erdos591.FollowFreshInputs

/-!
# The actual preliminary run for either full S label

Starting in the issued last S body, follow the old opposite critical
body to its largest selected leaf. The actual endpoint has S rank r,
so beta is its next selection. Both full body labels and the literal
input runs are retained; every new input lies in the chosen future
pool and exceeds its externally recorded bound.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem preliminary_run {N H K : Set ℕ}
    (hHN : H ⊆ N) (hKH : K ⊆ H) (hK : K.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (origin old p : Concrete.Hist N) {a beta r F : ℕ}
    (D : Finset ℕ) (hmemBeta : beta ∈ D)
    (hbetaRank : (D.filter (fun x => x ≤ beta)).card = r + 1) (ha : 2 ≤ a)
    (hop : origin.position.pending = some ⟨false, .advance a⟩)
    (hboard : origin.position.board = Board.initial) (hmode : origin.position.mode = some true)
    (hwin : (exactGame N blue).ArchitectWins H b σ origin)
    (hfrom : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin old)
    (holdp : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) old p)
    (hOld : CriticalCheckpoint old)
    (hl : p.position.board.left.relaxed = true) (hr : p.position.board.right.relaxed = true)
    (hSroot : ∀ i ∈ p.position.board.left.rootLabel, i ≤ p.position.board.left.bodyLabels.length)
    (hSlabel : p.position.board.left.currentLabel = D)
    (hTbody : p.position.board.right.bodyLabels = old.position.board.right.bodyLabels)
    (hTlt : p.position.board.right.leafIndex < p.position.board.right.currentLabel.sup id)
    (hrank : old.position.board.right.currentLabel.card -
      (old.position.board.right.currentLabel.filter
        (fun x => x ≤ old.position.board.right.leafIndex)).card = r)
    (hfresh : ∀ x ∈ K, F < x)
    (hall : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin z →
      (exactGame N blue).kind z = .terminal w →
        z.position.board.left.beforeLastLeafCount < z.position.board.right.beforeLastLeafCount) :
    ∃ q, Relation.ReflTransGen ((exactGame N blue).FollowStep σ K b) p q ∧
      q.position.pending = none ∧ q.position.board.left.relaxed = true ∧
      q.position.board.right.relaxed = true ∧ q.position.board.right.NoLeafPending ∧
      q.position.board.left.bodyLabels = p.position.board.left.bodyLabels ∧
      q.position.board.left.bodyMarker = p.position.board.left.bodyMarker ∧
      q.position.board.left.currentLabel = D ∧
      q.position.board.right.bodyLabels = old.position.board.right.bodyLabels ∧
      q.position.board.right.bodyMarker = p.position.board.right.bodyMarker ∧
      q.position.board.right.leafIndex = p.position.board.right.currentLabel.sup id ∧
      (q.position.board.left.currentLabel.filter
        (fun x => x ≤ q.position.board.left.leafIndex)).card = r ∧
      q.position.board.left.leafIndex < beta ∧
      (∀ x ∈ D, q.position.board.left.leafIndex < x → beta ≤ x) ∧
      (∀ x ∈ q.position.board.left.coordinates,
        x ≤ q.position.board.right.coordinates.getLastD 0) ∧
      ∃ as bs, LabeledWord.LegalRun p.position.board.left as q.position.board.left ∧
        LabeledWord.LegalRun p.position.board.right bs q.position.board.right ∧
        (∀ atom ∈ as, atom.2 ∈ K ∧ F < atom.2) ∧
        (∀ atom ∈ bs, atom.2 ∈ K ∧ F < atom.2) := by
  have hwinP := (hwin.of_reachable (exactGame N blue) (hfrom.trans holdp)).mono
    (exactGame N blue) hKH (fun _ => le_rfl)
  have hmaxmem : p.position.board.right.currentLabel.sup id ∈
      p.position.board.right.currentLabel := by
    simpa using Finset.sup_mem_of_nonempty (f := id)
      ⟨_, (of_decide_eq_true hr).2.2⟩
  obtain ⟨q, hpq, hqn, hqr, hqi, hqb, hqm, hqsep⟩ :=
    winning_reach_selected_leaf_fresh (hKH.trans hHN) hK blue hwinP true
      (p.position.board.right.currentLabel.sup id)
      ⟨(of_decide_eq_true hr).2.1, hmaxmem, hTlt.le⟩ hTlt
  simp only [Board.get, Bool.not_true] at hqr hqi hqb hqm hqsep
  obtain ⟨as, has, hpoolS⟩ := follow_word_inputs_above_bound hpq false
  obtain ⟨bs, hbs, hpoolT⟩ := follow_word_inputs_above_bound hpq true
  change LabeledWord.LegalRun p.position.board.left as q.position.board.left at has
  change LabeledWord.LegalRun p.position.board.right bs q.position.board.right at hbs
  obtain ⟨initialAtoms, hinit⟩ := History.word_run p false
  have hpos : 0 < q.position.board.left.coordinates.length :=
    (hinit.relaxed_coordinates_pos hl).trans_le has.coordinates_prefix.length_le
  have hwinQ := hwinP.of_reachable (exactGame N blue) hpq
  obtain ⟨hql, horder⟩ := winning_overtaken_other_relaxed (hKH.trans hHN) hK blue
    hwinQ true hqr hpos hqsep
  simp only [Board.get, Bool.not_true] at hql horder
  have hstart := LabeledWord.relaxed_ne_start ((Position.history_dataInvariant p).2.1 false).1 hl
  have hlabels := has.last_body_relaxed_labels hstart hSroot hql
  have hcurrentS : q.position.board.left.currentLabel = D := by
    simpa only [LabeledWord.currentLabel, hlabels.1] using hSlabel
  have hrootEq := has.rootLabel_eq hstart
  have hlastS : q.position.board.left.bodyLabels.length =
      q.position.board.left.lastSelectedBody := by
    apply le_antisymm (Finset.le_sup (f := id) (of_decide_eq_true hql).2.1)
    apply Finset.sup_le
    intro i hi
    change i ≤ q.position.board.left.bodyLabels.length
    rw [hlabels.1]
    exact hSroot i (hrootEq ▸ hi)
  have hcurrentT : q.position.board.right.currentLabel = p.position.board.right.currentLabel := by
    simp only [LabeledWord.currentLabel, hqb]
  have hTno : q.position.board.right.NoLeafPending := by
    intro x hx
    rw [hqi]
    exact Finset.le_sup (f := id) (hcurrentT ▸ hx)
  have hpqH : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q :=
    Relation.ReflTransGen.mono (fun _ _ hs => FiniteResponseGame.FollowStep.mono
      (exactGame N blue) hKH (fun _ => le_rfl) hs) _ _ hpq
  have hqrank := winning_preliminary_last_rank hHN hKH hK blue origin old q ha hop
    hboard hmode hwin hfrom (holdp.trans hpqH) hOld hql hqr horder hlastS
      (hqb.trans hTbody) hTno hall
  rw [hrank] at hqrank
  have hqrankD : (D.filter (fun x => x ≤ q.position.board.left.leafIndex)).card = r := by
    simpa only [hcurrentS] using hqrank
  have hbeta := finite_rank_successor D hmemBeta (x := q.position.board.left.leafIndex)
    (by rw [hbetaRank, hqrankD])
  exact ⟨q, hpq, hqn, hql, hqr, hTno, hlabels.1, hlabels.2, hcurrentS,
    hqb.trans hTbody, hqm, hqi, hqrank, hbeta.1, hbeta.2, hqsep,
    as, bs, has, hbs, (fun atom ha => ⟨(hpoolS atom ha).1, hfresh _ (hpoolS atom ha).1⟩),
    (fun atom hb => ⟨(hpoolT atom hb).1, hfresh _ (hpoolT atom hb).1⟩)⟩

#print axioms preliminary_run

end Erdos591.Positive.Game.Payoff
