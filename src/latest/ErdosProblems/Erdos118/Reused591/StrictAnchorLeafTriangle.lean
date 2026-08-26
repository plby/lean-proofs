import ErdosProblems.Erdos118.Reused591.StrictAnchorLeafEndpoint
import ErdosProblems.Erdos118.Reused591.StrictAnchorHandoffTriangle

namespace Erdos118.Reused591

/-!
# Both U anchor-label requests through the complete strict triangle

The terminal critical profile supplies the exact rank-K endpoint.
Transport its saved replies without changing their original targets,
then submit them and invoke the complete ranked finishing argument.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact
open Relay

theorem strict_anchor_leaf_triangle {N H HT HU : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (p oldU : Concrete.Hist N) {B K c BT R D BU e g j k : ℕ}
    (T : RankedFirstLeafLabels HT BT R D (K + 1))
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
    (hPside : P.side = true) (hPsource : P.lowerLabel = T.source)
    (hPpivot : P.labels.pivot = T.targetView.pivot)
    (hPupper : P.labels.upper = T.targetView.upper)
    (hUroot : p.position.board.right.rootLabel = U.upper)
    (hUbody : p.position.board.right.bodyLabels.length + 1 = U.anchor)
    (hLowerUroot : oldU.position.board.right.rootLabel = U.lower)
    (hAfterU : k + 1 < g)
    (hmode : p.position.mode = some true) (hModeSU : oldU.position.mode = some true)
    (hvalid : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p z →
      (exactGame N blue).kind z = .terminal w →
        z.position.board.right.CriticalPairSpec z.position.board.left.lastSelectedLabel.card
          (z.position.board.right.criticalPair z.position.board.left.lastSelectedLabel.card) ∧
        z.position.board.right.criticalBodyRank z.position.board.left.lastSelectedLabel.card = k ∧
        criticalLastColor z = true)
    (hSrel : oldU.position.board.left.relaxed = true)
    (hS : LabeledWord.SameStructure P.target.position.board.left oldU.position.board.left)
    {gamma : ℕ} (hSUp : LabeledWord.UpToLeaf gamma P.target.position.board.left)
    (hSstrict : P.target.position.board.left.leafIndex < gamma)
    (hSnext : ∀ i ∈ P.target.position.board.left.currentLabel,
      P.target.position.board.left.leafIndex < i → gamma ≤ i)
    (hSroot : ∀ i ∈ oldU.position.board.left.rootLabel,
      i ≤ oldU.position.board.left.bodyLabels.length)
    (hgamma : gamma ∈ oldU.position.board.left.currentLabel)
    (hSlast : ∀ i ∈ oldU.position.board.left.currentLabel, i ≤ gamma) :
    ¬ blue.CliqueFree 3 := by
  have hPrank : (P.lowerLabel.filter (fun x => x ≤ P.labels.pivot)).card = K + 1 := by
    simpa only [hPsource, hPpivot] using T.pivot_rank
  obtain ⟨q, hpq, _hqn, hql, hqr, hqno, hqsep, hqrank, _hbefore,
      PT, hPTtarget, hPTside, _hPTstem, hPTlower, hPTpivot, hPTupper,
      PU, hPUtarget, hPUside, hPUstem, _hPUlower, _hPUpivot, _hPUupper, hPUindex⟩ :=
    strict_anchor_leaf_endpoint hHN hH blue p oldU U E P hwin hwinU hp hpU hm hmU hshape
      hBp hBU hTrel hTroot hPrank hUroot hUbody hmode hvalid
  have hnextRank : (q.position.board.left.currentLabel.filter
        (fun x => x ≤ PT.labels.pivot)).card =
      (q.position.board.left.currentLabel.filter
        (fun x => x ≤ q.position.board.left.leafIndex)).card + 1 := by
    rw [hqrank, PT.currentLabel, hPTlower, hPTpivot]
    exact hPrank
  have hqUroot : q.position.board.right.rootLabel = U.upper := by
    rw [PU.rootLabel, hPUstem]
    exact hUroot
  have hqUbody : q.position.board.right.bodyLabels.length = U.anchor := by
    rw [PU.body_length, hPUstem]
    exact hUbody
  obtain ⟨ts, hts, _⟩ := follow_word_inputs hpq 0 (fun _ => Nat.zero_le _) false
  have hstart := LabeledWord.relaxed_ne_start ((Position.history_dataInvariant p).2.1 false).1 hTrel
  have hlabels := (hts.last_body_relaxed_labels hstart hTroot hql).1
  have hrootEq := hts.rootLabel_eq hstart
  have hqTroot : ∀ i ∈ q.position.board.left.rootLabel,
      i ≤ q.position.board.left.bodyLabels.length := by
    intro i hi
    change q.position.board.left.bodyLabels = p.position.board.left.bodyLabels at hlabels
    rw [hlabels]
    exact hTroot i (hrootEq ▸ hi)
  exact strict_anchor_handoff_triangle hHN hH blue q T U PT PU
    (hwin.of_reachable (exactGame N blue) hpq) (follow_mode_some hpq hmode)
    (by simpa only [hPUtarget] using hModeSU) (hPTside.trans hPside) hPUside
    (hPTlower.trans hPsource) (hPTpivot.trans hPpivot) (hPTupper.trans hPupper)
    hqr hPUindex hqno hqUroot hqUbody
    (by simpa only [hPUtarget] using hLowerUroot) hAfterU hqsep hnextRank hqTroot
    (by simpa only [hPUtarget] using hSrel)
    (by simpa only [hPTtarget, hPUtarget] using hS)
    (by simpa only [hPTtarget] using hSUp) (by simpa only [hPTtarget] using hSstrict)
    (by simpa only [hPTtarget] using hSnext) (by simpa only [hPUtarget] using hSroot)
    (by simpa only [hPUtarget] using hgamma) (by simpa only [hPUtarget] using hSlast)

#print axioms strict_anchor_leaf_triangle

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
