import ErdosProblems.Erdos118.Reused591.ReservedNonlastSeparatedPreparation
import ErdosProblems.Erdos118.Reused591.StrictNonlastAnchorOpening
import ErdosProblems.Erdos118.Reused591.LastLastUpper

namespace Erdos118.Reused591

/-!
# The inserted rank-one nonlast SU checkpoint and the upper pair's two first leaves

The lower first-word prefix reaches its actual penultimate selected
body. The upper U root rank remains localized because the exact path
from its saved root request stays in the original restricted future
pool. All new S coordinates retain the old pending ST bound.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact
open Relay

theorem reserved_nonlast_separated_checkpoint {N H M : Set ℕ}
    (hHN : H ⊆ N) (hMH : M ⊆ H) (hM : M.Infinite)
    (blue : SimpleGraph G) (htri : blue.CliqueFree 3) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy}
    (hroot : (exactGame N blue).ArchitectWins H b σ
      (History.initial (Position.Next N) Position.initial))
    (origin old upperOrigin : Concrete.Hist N) {B a g : ℕ}
    (S : LastLastLabels H B a) (ha : 2 ≤ a) (hg : 2 ≤ g)
    (hwin : (exactGame N blue).ArchitectWins H b σ origin)
    (hop : origin.position.pending = some ⟨false, .advance a⟩)
    (hboard : origin.position.board = Board.initial) (hmode : origin.position.mode = some true)
    (hB : max origin.position.bound (b origin) ≤ B)
    (hfromUpper : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin upperOrigin)
    (hOldBody : old.position.board.left.bodyLabels.length = S.penultimate)
    (hpUpper : upperOrigin.position.pending = some ⟨true, .advance g⟩)
    (hUpperInit : upperOrigin.position.board.right = LabeledWord.initial)
    (hall : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin z →
      (exactGame N blue).kind z = .terminal w →
        z.position.board.left.beforeLastLeafCount < z.position.board.right.beforeLastLeafCount)
    (hlast : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin z →
      (exactGame N blue).kind z = .terminal w → criticalLastColor z = false)
    (hfixedUpper : ∀ z w,
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ M b) upperOrigin z →
      (exactGame N blue).kind z = .terminal w →
        z.position.board.right.criticalBodyRank z.position.board.left.lastSelectedLabel.card = 1)
    {as : List (Finset ℕ × ℕ)}
    (hraw : (LabeledCode.rootCursor S.lower S.marker).runAtoms as = some old.position.board.left)
    (hinc : (S.marker :: as.map Prod.snd).Pairwise (· < ·))
    (hpool : ∀ x ∈ as.map Prod.snd, x ∈ H) :
    ∃ K, K ⊆ M ∧ K.Infinite ∧ ∃ C e j, ∃ U : SeparatedRootLabels K C e g j,
      0 < j ∧ j < e ∧ ∃ L, L ⊆ K ∧ L.Infinite ∧
        (∀ x ∈ L, max old.position.bound (b old) < x) ∧
        ∃ Dbound d c s, ∃ D : CriticalRootLabels L Dbound d c s,
          2 ≤ c ∧ 0 < s ∧ s < d ∧ ∃ su tu,
          Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin su ∧
          Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin tu ∧
          Relation.ReflTransGen ((exactGame N blue).FollowStep σ M b) upperOrigin tu ∧
          (exactGame N blue).ArchitectWins L b σ su ∧
          su.position.pending = some ⟨false, .advance 0⟩ ∧ CriticalCheckpoint su ∧
          su.position.board.left.rootLabel = S.upper ∧
          su.position.board.left.bodyLabels.length = S.upperPenultimate ∧
          su.position.board.right.rootLabel = U.lower ∧
          su.position.board.right.bodyLabels.length = U.first ∧
          su.position.board.right.currentLabel = D.lower ∧
          su.position.board.right.leafIndex = D.shared ∧ tu.position.pending = none ∧
          tu.position.board.left = upperOrigin.position.board.left ∧
          LabeledWord.SameStructure su.position.board.right tu.position.board.right ∧
          tu.position.board.right.relaxed = true ∧ tu.position.board.right.rootLabel = U.upper ∧
          tu.position.board.right.bodyLabels.length = U.first ∧
          tu.position.board.right.currentLabel = D.upper ∧
          tu.position.board.right.leafIndex = D.shared ∧ tu.position.mode = some true ∧
          (∀ x ∈ tu.position.board.left.coordinates,
            x ≤ tu.position.board.right.coordinates.getLastD 0) ∧
          (∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ L b) tu z →
            (exactGame N blue).kind z = .terminal w →
              z.position.board.right.criticalBodyRank z.position.board.left.lastSelectedLabel.card =
                1) ∧
          ∃ frontAtoms, LabeledWord.LegalRun
            (LabeledWord.rootRelabel S.upper old.position.board.left) frontAtoms
              su.position.board.left ∧
            ∀ atom ∈ frontAtoms, atom.2 ∈ H ∧ max old.position.bound (b old) < atom.2 := by
  obtain ⟨K, hKM, hK, hKfresh, C, e, j, U, hj, hje, fine, hfromFine, _hwinFine,
      _hnFine, hrFine, hrootFine, _hbodyFine, frontAtoms, hfront, hfrontPool,
      R, hRt, hRs, hRlower, hRupper, hRshared, _hRrank, hfixed⟩ :=
    reserved_nonlast_separated_preparation hHN hMH hM blue htri hroot
      origin old upperOrigin S ha hg
      hwin hop hboard hmode hB hfromUpper hOldBody hpUpper hUpperInit hall hraw hinc hpool
  have hKH := hKM.trans hMH
  have pathM {p q : Concrete.Hist N}
      (hpath : Relation.ReflTransGen ((exactGame N blue).FollowStep σ K b) p q) :
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ M b) p q :=
    Relation.ReflTransGen.mono (fun _ _ hs =>
      FiniteResponseGame.FollowStep.mono (exactGame N blue) hKM (fun _ => le_rfl) hs) _ _ hpath
  have pathH {p q : Concrete.Hist N}
      (hpath : Relation.ReflTransGen ((exactGame N blue).FollowStep σ K b) p q) :
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q :=
    Relation.ReflTransGen.mono (fun _ _ hs =>
      FiniteResponseGame.FollowStep.mono (exactGame N blue) hKH (fun _ => le_rfl) hs) _ _ hpath
  have hRfrom : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin R.target := by
    simpa only [hRt] using hfromUpper
  have hpos : 0 < fine.position.board.left.coordinates.length := by
    obtain ⟨xs, hx⟩ := History.word_run fine false
    exact hx.relaxed_coordinates_pos hrFine
  obtain ⟨L, hLK, hL, Dbound, d, c, s, D, hc, hs, hsd, su, tu, hfineSU,
      hfromTU, hpSU, hcp, hUroot, hUbody, hUlabel, hUindex, hnTU, hUshape,
      hTUrel, hTUroot, hTUbody, hTUlabel, hTUindex, hTUother, hTUmode, hUpperTU, hTUsep⟩ :=
    strict_nonlast_anchor_opening_at_target hHN hKH hK blue origin fine R hRs hRfrom ha hop hboard
      hmode hwin hfromFine hpos hall hlast hfixed
      (fun z w hpath hz => hfixedUpper z w
        (by simpa only [hRt] using pathM hpath) hz)
  have hfromSU := hfromFine.trans (pathH hfineSU)
  have hUpperTUM : Relation.ReflTransGen ((exactGame N blue).FollowStep σ M b) upperOrigin tu := by
    simpa only [hRt] using pathM hUpperTU
  obtain ⟨newAtoms, hnewRun, hnewPool⟩ := follow_word_inputs_above_bound hfineSU false
  have hstartFine := LabeledWord.relaxed_ne_start
    ((Position.history_dataInvariant fine).2.1 false).1 hrFine
  have hSUroot : su.position.board.left.rootLabel = S.upper :=
    (hnewRun.rootLabel_eq hstartFine).trans hrootFine
  have hSUlast : su.position.board.left.lastSelectedBody = S.pivot := by
    rw [LabeledWord.lastSelectedBody, hSUroot, S.upper_sup]
  have hSUbody : su.position.board.left.bodyLabels.length = S.upperPenultimate := by
    have hselected : su.position.board.left.bodyLabels.length ∈ S.upper :=
      hSUroot ▸ (of_decide_eq_true hcp.left_relaxed).2.1
    have hle := (S.upper_bounds_penultimate _ hselected).resolve_left
      (by simpa only [hSUlast] using ne_of_lt hcp.left_before)
    have hge := hcp.left_penultimate S.upperPenultimate (hSUroot ▸ S.upperPenultimate_mem)
      (by simpa only [hSUlast] using S.upperPenultimate_lt_pivot)
    omega
  refine ⟨K, hKM, hK, C, e, j, U, hj, hje, L, hLK, hL,
    (fun x hx => hKfresh x (hLK hx)), Dbound, d, c, s, D, hc, hs, hsd, su, tu, hfromSU, hfromTU,
    hUpperTUM, (hwin.of_reachable (exactGame N blue) hfromSU).mono
      (exactGame N blue) (hLK.trans hKH) (fun _ => le_rfl), hpSU, hcp, hSUroot, hSUbody,
    ?_, ?_, hUlabel, hUindex, hnTU, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hTUmode, ?_, ?_,
    frontAtoms ++ newAtoms, hfront.append hnewRun, ?_⟩
  · simpa only [hRlower] using hUroot
  · simpa only [hRshared] using hUbody
  · simpa only [hRs, hRt, Board.get, Bool.not_true] using hTUother
  · simpa only [hRs, Board.get] using hUshape
  · simpa only [hRs, Board.get] using hTUrel
  · simpa only [hRs, Board.get, hRupper] using hTUroot
  · simpa only [hRs, Board.get, hRshared] using hTUbody
  · simpa only [hRs, Board.get, CriticalRootLabels.leaf_view] using hTUlabel
  · simpa only [hRs, Board.get, CriticalRootLabels.leaf_view] using hTUindex
  · simpa only [hRs, Board.get, Bool.not_true] using hTUsep
  · intro z w htail hz
    apply hfixedUpper z w (hUpperTUM.trans ?_) hz
    exact Relation.ReflTransGen.mono (fun _ _ hs =>
      FiniteResponseGame.FollowStep.mono (exactGame N blue) (hLK.trans hKM)
        (fun _ => le_rfl) hs) _ _ htail
  · intro atom hatom
    rcases List.mem_append.mp hatom with hatom | hatom
    · exact hfrontPool atom hatom
    · exact ⟨hKH (hnewPool atom hatom).1, hKfresh atom.2 (hnewPool atom hatom).1⟩

#print axioms reserved_nonlast_separated_checkpoint

end Erdos591.Positive.Game.Payoff


end Erdos118.Reused591
