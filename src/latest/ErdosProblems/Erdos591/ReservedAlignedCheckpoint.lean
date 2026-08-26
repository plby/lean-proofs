import ErdosProblems.Erdos591.ReservedAlignedPreparation
import ErdosProblems.Erdos591.AlignedCriticalOpening
import ErdosProblems.Erdos591.LastLastUpper

/-!
# The inserted aligned critical checkpoint and the upper pair's two first leaves

All new first-word coordinates retain the old pending-response bound.
The two lower first-word prefixes end at their respective penultimate
selected bodies. The upper play has its two first selected leaves.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact
open Relay

theorem reserved_aligned_checkpoint {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) (htri : blue.CliqueFree 3) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy}
    (hroot : (exactGame N blue).ArchitectWins H b σ
      (History.initial (Position.Next N) Position.initial))
    (origin old upperOrigin : Concrete.Hist N) {B a c : ℕ} (L : LastLastLabels H B a)
    (ha : 2 ≤ a) (hc : 2 ≤ c)
    (hwinOrigin : (exactGame N blue).ArchitectWins H b σ origin)
    (hopening : origin.position.pending = some ⟨false, .advance a⟩)
    (hboardOrigin : origin.position.board = Board.initial)
    (hmodeOrigin : origin.position.mode = some true)
    (hB : max origin.position.bound (b origin) ≤ B)
    (hfromUpper : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin upperOrigin)
    (hOldBody : old.position.board.left.bodyLabels.length = L.penultimate)
    (hpUpper : upperOrigin.position.pending = some ⟨true, .advance c⟩)
    (hUpperInit : upperOrigin.position.board.right = LabeledWord.initial)
    (hall : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin z →
      (exactGame N blue).kind z = .terminal w → alignedBodyCountColor z = true)
    {as : List (Finset ℕ × ℕ)}
    (hraw : (LabeledCode.rootCursor L.lower L.marker).runAtoms as = some old.position.board.left)
    (hinc : (L.marker :: as.map Prod.snd).Pairwise (· < ·))
    (hpool : ∀ x ∈ as.map Prod.snd, x ∈ H) :
    ∃ J, J ⊆ H ∧ J.Infinite ∧ (∀ x ∈ J, max old.position.bound (b old) < x) ∧
      ∃ C e d, ∃ U : AlignedRootLabels J C e d, d = c ∧ ∃ su tu,
        Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin su ∧
        Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin tu ∧
        (exactGame N blue).ArchitectWins J b σ su ∧
        su.position.pending = some ⟨false, .advance 0⟩ ∧
        su.position.board.left.rootLabel = L.upper ∧
        su.position.board.left.bodyLabels.length = L.upperPenultimate ∧
        su.position.board.left.relaxed = true ∧ su.position.board.left.NoLeafPending ∧
        su.position.board.right.relaxed = true ∧ su.position.board.right.NoLeafPending ∧
        su.position.board.right.rootLabel = U.lower ∧
        su.position.board.right.bodyLabels.length = U.shared ∧
        tu.position.pending = none ∧ tu.position.board.left = upperOrigin.position.board.left ∧
        LabeledWord.SameStructure su.position.board.right tu.position.board.right ∧
        tu.position.board.right.relaxed = true ∧ tu.position.board.right.rootLabel = U.upper ∧
        tu.position.board.right.bodyLabels.length = U.shared ∧ tu.position.mode = some true ∧
        (∀ x ∈ tu.position.board.left.coordinates,
          x ≤ tu.position.board.right.coordinates.getLastD 0) ∧
        ∃ frontAtoms, LabeledWord.LegalRun
          (LabeledWord.rootRelabel L.upper old.position.board.left) frontAtoms
            su.position.board.left ∧
          ∀ atom ∈ frontAtoms, atom.2 ∈ H ∧ max old.position.bound (b old) < atom.2 := by
  obtain ⟨J, hJH, hJ, hJfresh, fine, hfromFine, hwinFine, _hnFine, hrFine, hrootFine,
      _hbodyFine, frontAtoms, hfront, hfrontPool, R, hRt, hRs⟩ :=
    reserved_aligned_preparation hHN hH blue htri hroot origin old upperOrigin L ha hc
      hwinOrigin hopening hboardOrigin hmodeOrigin hB hfromUpper hOldBody hpUpper
      hUpperInit hall hraw hinc hpool
  have pathH {p q : Concrete.Hist N}
      (hp : Relation.ReflTransGen ((exactGame N blue).FollowStep σ J b) p q) :
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q :=
    Relation.ReflTransGen.mono (fun _ _ hs =>
      FiniteResponseGame.FollowStep.mono (exactGame N blue) hJH (fun _ => le_rfl) hs) _ _ hp
  have hRfrom : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin R.target := by
    simpa only [hRt] using hfromUpper
  have hpos : 0 < fine.position.board.left.coordinates.length := by
    obtain ⟨as, has⟩ := History.word_run fine false
    exact has.relaxed_coordinates_pos hrFine
  obtain ⟨su, tu, hfineSU, hTU, hpSU, hrSU, hbeforeSU, hpenSU, hnoSU, hrU, hrootU,
      hbodyU, hnoU, hnTU, hUshape, hTUrel, hTUroot, hTUbody, _hTUfirst, hTUother,
      hTUmode, hTUsep⟩ :=
    aligned_critical_opening_on_subset hHN hH hJH hJ blue origin fine R (by omega)
      hopening hboardOrigin hmodeOrigin hwinOrigin hfromFine hRfrom hpos hall
  have hfromSU := hfromFine.trans (pathH hfineSU)
  obtain ⟨newAtoms, hnewRun, hnewPool⟩ := follow_word_inputs_above_bound hfineSU false
  have hstartFine := LabeledWord.relaxed_ne_start
    ((Position.history_dataInvariant fine).2.1 false).1 hrFine
  have hSUroot : su.position.board.left.rootLabel = L.upper :=
    (hnewRun.rootLabel_eq hstartFine).trans hrootFine
  have hSUlast : su.position.board.left.lastSelectedBody = L.pivot := by
    rw [LabeledWord.lastSelectedBody, hSUroot, L.upper_sup]
  have hSUbody : su.position.board.left.bodyLabels.length = L.upperPenultimate := by
    have hselected : su.position.board.left.bodyLabels.length ∈ L.upper :=
      hSUroot ▸ (of_decide_eq_true hrSU).2.1
    have hle := (L.upper_bounds_penultimate _ hselected).resolve_left
      (by simpa only [hSUlast] using ne_of_lt hbeforeSU)
    have hge := hpenSU L.upperPenultimate (hSUroot ▸ L.upperPenultimate_mem)
      (by simpa only [hSUlast] using L.upperPenultimate_lt_pivot)
    omega
  have hsize : R.upperSize = c := by
    have hp : upperOrigin.position.pending = some ⟨true, .advance R.upperSize⟩ := by
      simpa only [hRt, hRs] using R.targetPending
    exact congrArg Request.size (Option.some.inj (hp.symm.trans hpUpper))
  refine ⟨J, hJH, hJ, hJfresh, R.budget, R.lowerSize, R.upperSize, R.labels, hsize,
    su, tu, hfromSU, hTU, hwinFine.of_reachable (exactGame N blue) hfineSU,
    hpSU, hSUroot, hSUbody, hrSU, hnoSU, hrU, hnoU, hrootU, hbodyU, hnTU,
    ?_, ?_, ?_, ?_, ?_, hTUmode, ?_, frontAtoms ++ newAtoms, hfront.append hnewRun, ?_⟩
  · simpa only [hRs, hRt, Board.get, Bool.not_true] using hTUother
  · simpa only [hRs, Board.get] using hUshape
  · simpa only [hRs, Board.get] using hTUrel
  · simpa only [hRs, Board.get] using hTUroot
  · simpa only [hRs, Board.get] using hTUbody
  · simpa only [hRs, Board.get, Bool.not_true] using hTUsep
  · intro atom hatom
    rcases List.mem_append.mp hatom with hatom | hatom
    · exact hfrontPool atom hatom
    · exact ⟨hJH (hnewPool atom hatom).1, hJfresh atom.2 (hnewPool atom hatom).1⟩

#print axioms reserved_aligned_checkpoint

end Erdos591.Positive.Game.Payoff
