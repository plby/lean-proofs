import ErdosProblems.Erdos118.Reused591.PreparedNextLeafHandoff
import ErdosProblems.Erdos118.Reused591.NextLeafReplay
import ErdosProblems.Erdos118.Reused591.RankedStrictFinishing
import ErdosProblems.Erdos118.Reused591.SeparatedNextRoot
import ErdosProblems.Erdos118.Reused591.LastBodyEndpoint

namespace Erdos118.Reused591

/-!
# A saved lower U next-leaf reply and a saved lower T first-leaf reply

Submit the whole U prefix without relabeling its old body. Then
take the next upper T selection and fire its saved first-leaf reply.
The separated next U root supplies the checked strict ending.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact
open Relay

theorem next_leaf_anchor_triangle {N H J HT HU : Set ℕ}
    (hHN : H ⊆ N) (hJH : J ⊆ H) (hJ : J.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (p oldU : Concrete.Hist N) {BT R D rank BU e g j leaf : ℕ}
    (T : RankedFirstLeafLabels HT BT R D rank) (U : SeparatedRootLabels HU BU e g j)
    (PT : PreparedSelection N J blue b σ p.position.board.left)
    (hwin : (exactGame N blue).ArchitectWins J b σ p)
    (hwinU : (exactGame N blue).ArchitectWins H b σ oldU)
    (hmode : p.position.mode = some true) (hModeSU : oldU.position.mode = some true)
    (hPTside : PT.side = true) (hPTsource : PT.lowerLabel = T.source)
    (hPTpivot : PT.labels.pivot = T.targetView.pivot)
    (hPTupper : PT.labels.upper = T.targetView.upper)
    (hpU : oldU.position.pending = some ⟨true, .advance 0⟩)
    (hOldUrel : oldU.position.board.right.relaxed = true)
    (hUpTo : LabeledWord.UpToLeaf leaf oldU.position.board.right)
    (hStrict : oldU.position.board.right.leafIndex < leaf)
    (hNext : ∀ x ∈ oldU.position.board.right.currentLabel,
      oldU.position.board.right.leafIndex < x → leaf ≤ x)
    {anchor : LabeledWord} {front : List (Finset ℕ × ℕ)}
    (hUshape : LabeledWord.SameStructure oldU.position.board.right anchor)
    (hfront : LabeledWord.LegalRun anchor front p.position.board.right)
    (hpool : ∀ atom ∈ front, atom.2 ∈ H ∧ max oldU.position.bound (b oldU) < atom.2)
    (hcount : p.position.board.right.bodyLabels.length = anchor.bodyLabels.length)
    (hmarker : p.position.board.right.bodyMarker = anchor.bodyMarker)
    (hUat : p.position.board.right.leafIndex = leaf)
    (hUrel : p.position.board.right.relaxed = true)
    (hUno : p.position.board.right.NoLeafPending)
    (hUroot : p.position.board.right.rootLabel = U.upper)
    (hUbody : p.position.board.right.bodyLabels.length = U.first)
    (hLowerRoot : oldU.position.board.right.rootLabel = U.lower) (hg : 2 ≤ g)
    (hsep : ∀ x ∈ p.position.board.left.coordinates,
      x ≤ p.position.board.right.coordinates.getLastD 0)
    (hnextRank : (p.position.board.left.currentLabel.filter
        (fun x => x ≤ PT.labels.pivot)).card =
      (p.position.board.left.currentLabel.filter
        (fun x => x ≤ p.position.board.left.leafIndex)).card + 1)
    (hTroot : ∀ i ∈ p.position.board.left.rootLabel, i ≤ p.position.board.left.bodyLabels.length)
    (hSrel : oldU.position.board.left.relaxed = true)
    (hS : LabeledWord.SameStructure PT.target.position.board.left oldU.position.board.left)
    {gamma : ℕ} (hSUp : LabeledWord.UpToLeaf gamma PT.target.position.board.left)
    (hSstrict : PT.target.position.board.left.leafIndex < gamma)
    (hSnext : ∀ i ∈ PT.target.position.board.left.currentLabel,
      PT.target.position.board.left.leafIndex < i → gamma ≤ i)
    (hSroot : ∀ i ∈ oldU.position.board.left.rootLabel,
      i ≤ oldU.position.board.left.bodyLabels.length)
    (hgamma : gamma ∈ oldU.position.board.left.currentLabel)
    (hSlast : ∀ i ∈ oldU.position.board.left.currentLabel, i ≤ gamma) :
    ¬ blue.CliqueFree 3 := by
  have hJN := hJH.trans hHN
  have hinc : (front.map Prod.snd).Pairwise (· < ·) := by
    have hi := ((Position.history_dataInvariant p).2.1 true).2
    change p.position.board.right.coordinates.Pairwise (· < ·) at hi
    rw [LabeledWord.runAtoms_coordinates hfront.run] at hi
    exact (List.pairwise_append.mp hi).2.1
  obtain ⟨su, hSUstep, _hSUnone, hSUshape, hSUrel, _hSUlabels, hSUother⟩ :=
    Concrete.follow_next_leaf hHN (payoff blue) σ oldU true hpU hUshape hUpTo hStrict hNext
      hfront.run hUat hcount hmarker hinc (by
        intro atom ha
        exact ⟨(hpool atom ha).1, (le_max_left _ _).trans_lt (hpool atom ha).2,
          (le_max_right _ _).trans_lt (hpool atom ha).2⟩)
  simp only [Board.get, Bool.not_true] at hSUshape hSUrel hSUother
  have hSUsep :=
    (FiniteResponseGame.FollowStep.next (exactGame N blue) hSUstep).reply_separation hpU
  have hnext := finite_rank_successor p.position.board.left.currentLabel PT.upto.mem hnextRank
  obtain ⟨tu, st, hpTU, hSTstep, _hTUnone, _hSTnone, hTUrel, hTUindex, hTUlabel,
      hTUother, hTUsep, hTshape, hSTrel, _hSTroot, hSTlabel, _hSTindex, hSTother⟩ :=
    PT.fire_at_next_leaf hJN hJ blue false hwin hnext.1 hnext.2 hUrel hsep
  simp only [Board.get, Bool.not_false] at hTUrel hTUindex hTUlabel hTUother hTUsep
  simp only [hPTside, Board.get, Bool.not_true] at hTshape hSTrel hSTlabel hSTother
  have hSTsep := (FiniteResponseGame.FollowStep.next (exactGame N blue) hSTstep).reply_separation
    PT.targetPending
  obtain ⟨as, has, _⟩ := follow_word_inputs_above_bound hpTU false
  obtain ⟨r, k, hparse⟩ := PT.upto.parser_leaves ((Position.history_dataInvariant p).2.1 false).1
  have hstart : p.position.board.left.parser ≠ .start := by simp [hparse]
  have hTbody := (has.last_body_relaxed_labels hstart hTroot hTUrel).1
  have hTRootEq := has.rootLabel_eq hstart
  have hTrootFinal : ∀ i ∈ tu.position.board.left.rootLabel,
      i ≤ tu.position.board.left.bodyLabels.length := by
    intro i hi
    change tu.position.board.left.bodyLabels = p.position.board.left.bodyLabels at hTbody
    rw [hTbody]
    exact hTroot i (hTRootEq ▸ hi)
  obtain ⟨bs, hbs, _⟩ := follow_word_inputs_above_bound (Relation.ReflTransGen.single hSUstep) true
  have hSUroot : su.position.board.right.rootLabel = U.lower :=
    (hbs.rootLabel_eq (LabeledWord.relaxed_ne_start
      ((Position.history_dataInvariant oldU).2.1 true).1 hOldUrel)).trans hLowerRoot
  obtain ⟨nextU, hnextMem, hFirstLt, hnextLeast, hLowerLt⟩ := U.next_after_first hg
  have hBeforeU : LabeledWord.BeforeBody nextU tu.position.board.right :=
    ⟨by simpa only [hTUother, hUroot] using hnextMem,
      by simpa only [hTUother, hUbody] using hFirstLt⟩
  have hNextU : ∀ i ∈ tu.position.board.right.rootLabel,
      tu.position.board.right.bodyLabels.length < i → nextU ≤ i := by
    simpa only [hTUother, hUroot, hUbody] using hnextLeast
  have hLowerBeforeU : ∀ i ∈ su.position.board.right.rootLabel, i < nextU := by
    simpa only [hSUroot] using hLowerLt
  exact ranked_strict_finishing hJN hJ blue st su tu T
    (PT.targetWinning.of_reachable (exactGame N blue) (.single hSTstep))
    ((hwinU.of_reachable (exactGame N blue) (.single hSUstep)).mono
      (exactGame N blue) hJH (fun _ => le_rfl))
    (hwin.of_reachable (exactGame N blue) hpTU)
    (follow_mode_some (.single hSUstep) hModeSU) (follow_mode_some hpTU hmode)
    hSTrel (by simpa only [hSUother] using hSrel) hSUrel hTUrel
    (by simpa only [hTUother] using hUrel)
    (by simpa only [hPTside, Board.get, Bool.not_true] using hSTsep)
    (by simpa only [Board.get, Bool.not_true] using hSUsep) hTUsep
    (by simpa only [hSTother, hSUother] using hS) hTshape.symm
    (by simpa only [hTUother] using hSUshape.symm)
    (by simpa only [hSTother] using hSUp) (by simpa only [hSTother] using hSstrict)
    (by simpa only [hSTother] using hSnext) (by simpa only [hSUother] using hSroot)
    (by simpa only [hSUother] using hgamma) (by simpa only [hSUother] using hSlast)
    (hSTlabel.trans hPTupper)
    (hTUlabel.trans hPTsource) (hTUindex.trans hPTpivot) hTrootFinal
    (by simpa only [hTUother] using hUno) hBeforeU hNextU hLowerBeforeU

#print axioms next_leaf_anchor_triangle

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
