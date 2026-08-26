import ErdosProblems.Erdos118.Reused591.ReservedOpeningHistory
import ErdosProblems.Erdos118.Reused591.FirstRequestRecovery
import ErdosProblems.Erdos118.Reused591.FirstLeafGluingHistory
import ErdosProblems.Erdos118.Reused591.LastLastLabels
import ErdosProblems.Erdos118.Reused591.PrepareRootHistory
import ErdosProblems.Erdos118.Reused591.ManagedWord

namespace Erdos118.Reused591

/-!
# Common reserved insertion and managed opposite-root preparation

Complete the inserted root response beyond the retained old prefix.
Restrict subsequent inputs to the tail above the older response bound,
and prepare the opposite word against its already pending upper root.
The literal fresh prefix and both actual origins are retained. This
construction is independent of singleton or marker-order hypotheses.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact
open Relay

theorem reserved_inside_preparation {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) (htri : blue.CliqueFree 3) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy}
    (hroot : (exactGame N blue).ArchitectWins H b σ
      (History.initial (Position.Next N) Position.initial))
    (origin old upperOrigin : Concrete.Hist N) {B a c : ℕ} (L : LastLastLabels H B a)
    (hwinOrigin : (exactGame N blue).ArchitectWins H b σ origin)
    (hopening : origin.position.pending = some ⟨false, .advance a⟩)
    (hboardOrigin : origin.position.board = Board.initial)
    (hB : max origin.position.bound (b origin) ≤ B)
    (hfromUpper : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin upperOrigin)
    (hOldBody : old.position.board.left.bodyLabels.length = L.penultimate)
    (hpUpper : upperOrigin.position.pending = some ⟨true, .advance c⟩) (hc : 0 < c)
    (hUpperInit : upperOrigin.position.board.right = LabeledWord.initial)
    (hUpperMode : upperOrigin.position.mode = some true)
    {as : List (Finset ℕ × ℕ)}
    (hraw : (LabeledCode.rootCursor L.lower L.marker).runAtoms as = some old.position.board.left)
    (hinc : (L.marker :: as.map Prod.snd).Pairwise (· < ·))
    (hpool : ∀ x ∈ as.map Prod.snd, x ∈ H) :
    ∃ J, J ⊆ H ∧ J.Infinite ∧ (∀ x ∈ J, max old.position.bound (b old) < x) ∧
      ∃ fine, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin fine ∧
        (exactGame N blue).ArchitectWins J b σ fine ∧ fine.position.pending = none ∧
        fine.position.board.left.relaxed = true ∧ fine.position.board.left.rootLabel = L.upper ∧
        fine.position.board.left.bodyLabels.length = L.firstUpper ∧
        ((∀ q v d, (exactGame N blue).FollowStep σ H b origin q →
            (exactGame N blue).FollowStep σ H b q v →
            v.position.pending = some ⟨false, .advance d⟩ → 2 ≤ d) →
          fine.position.board.left.leafIndex < fine.position.board.left.currentLabel.sup id) ∧
        ∃ frontAtoms, LabeledWord.LegalRun
          (LabeledWord.rootRelabel L.upper old.position.board.left) frontAtoms fine.position.board.left ∧
          (∀ atom ∈ frontAtoms, atom.2 ∈ H ∧ max old.position.bound (b old) < atom.2) ∧
          ∃ M : Managed N J blue b σ true true upperOrigin.position.board.left fine.position.board.right,
            Relation.ReflTransGen ((exactGame N blue).FollowStep σ J b) upperOrigin M.target := by
  let K := max old.position.bound (b old)
  let J := H \ Set.Iic K
  have hJ : J.Infinite := hH.sdiff (Set.finite_Iic K)
  have hJH : J ⊆ H := fun _ hx => hx.1
  have hJN := hJH.trans hHN
  have hJfresh : ∀ x ∈ J, K < x := fun _ hx => lt_of_not_ge hx.2
  have pathH {p q : Concrete.Hist N}
      (hpath : Relation.ReflTransGen ((exactGame N blue).FollowStep σ J b) p q) :
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q :=
    Relation.ReflTransGen.mono (fun _ _ hs =>
      FiniteResponseGame.FollowStep.mono (exactGame N blue) hJH (fun _ => le_rfl) hs) _ _ hpath
  have hbeforeUpper : ∀ k ∈ L.upper, old.position.board.left.bodyLabels.length < k := by
    intro k hk
    rw [hOldBody]
    exact (L.upper_bounds k hk).1
  obtain ⟨suBody, d, hsuBodyPath, hpBody, hd, hmBody, hnoBody, hrootBody,
      hotherBody, tail, htailRun, htailPool, _htailCoords⟩ :=
    winning_reserved_root_request hHN hH blue hwinOrigin false hopening
      (by simp [hboardOrigin, Board.initial, Board.get]) hraw L.upper_fresh L.marker_fresh
      L.upper_card ⟨L.pivot, L.pivot_upper⟩ hbeforeUpper hinc hpool hB K
  change suBody.position.board.left.markerEvent = true at hmBody
  change suBody.position.board.left.NoRootPassed at hnoBody
  change suBody.position.board.left.rootLabel = L.upper at hrootBody
  change suBody.position.board.right = origin.position.board.right at hotherBody
  have hiBody : suBody.position.board.left.bodyLabels.length + 1 = L.firstUpper := by
    apply le_antisymm
    · exact hnoBody L.firstUpper (hrootBody ▸ L.firstUpper_mem)
    · exact L.firstUpper_le _ (hrootBody ▸ LabeledWord.marker_body_mem hmBody)
  have hrootJ := hroot.mono (exactGame N blue) hJH (fun _ => le_rfl)
  have hwinBodyH := hwinOrigin.of_reachable (exactGame N blue) hsuBodyPath
  have hwinBody := hwinBodyH.mono (exactGame N blue) hJH (fun _ => le_rfl)
  let Bbody := max suBody.position.bound (b suBody)
  obtain ⟨D⟩ := LastFirstLabels.exists_of_infinite hJ Bbody 1 d (by omega) hd
  obtain ⟨suLeaf, _sameLeaf, hbodyLeaf, _hbodyLeaf', hnLeaf, _hnLeaf', _hshapeLeaf,
      hrLeaf, _hrLeaf', hiLeaf, _hiLeaf', hbLeaf, _hbLeaf', hoLeaf, _hoLeaf'⟩ :=
    first_leaf_gluing hJN hJ blue σ suBody suBody false false D D rfl rfl hpBody hpBody
      hmBody hmBody (LabeledWord.SameStructure.refl _) le_rfl le_rfl
  have hwinLeaf := hwinBody.of_reachable (exactGame N blue) (Relation.ReflTransGen.single hbodyLeaf)
  have hLeafInit : suLeaf.position.board.right = LabeledWord.initial := by
    have ho : suLeaf.position.board.right = suBody.position.board.right := hoLeaf
    simp [ho, hotherBody, hboardOrigin, Board.initial]
  obtain ⟨suR, e, hLeafR, hboardR, hpR, he⟩ :=
    winning_initial_right_request hJN hJ blue htri hrootJ hwinLeaf hnLeaf hLeafInit hrLeaf
  let BU := max (max suR.position.bound (b suR)) (max upperOrigin.position.bound (b upperOrigin))
  obtain ⟨U⟩ := LastFirstLabels.exists_of_infinite hJ BU e c he hc
  have hwinUpper := (hwinOrigin.of_reachable (exactGame N blue) hfromUpper).mono
    (exactGame N blue) hJH (fun _ => le_rfl)
  obtain ⟨fine, hRfine, hnFine, _hmFine, hoFine, R, hRtarget, hRside, _hRlabels⟩ :=
    prepare_root hJN hJ blue hwinUpper true true U hpR hpUpper
      (by simpa [hboardR, Board.get] using hLeafInit) hUpperInit
      (le_max_left _ _) (le_max_right _ _)
  have hBodyFine := ((Relation.ReflTransGen.single hbodyLeaf).tail hLeafR).tail hRfine
  have hfromFine := hsuBodyPath.trans (pathH hBodyFine)
  have hwinFine := hwinBody.of_reachable (exactGame N blue) hBodyFine
  let M : Managed N J blue b σ true true upperOrigin.position.board.left
      fine.position.board.right := .root R hRside (by simp [hRtarget, hRside, Board.get])
        (by simpa only [hRtarget] using hUpperMode)
  have hMfrom : Relation.ReflTransGen ((exactGame N blue).FollowStep σ J b) upperOrigin M.target := by
    change Relation.ReflTransGen ((exactGame N blue).FollowStep σ J b) upperOrigin R.target
    rw [hRtarget]
  have hFineS : fine.position.board.left = suLeaf.position.board.left := by
    simpa [hboardR, Board.get] using hoFine
  have hFineBody : fine.position.board.left.bodyLabels.length = L.firstUpper := by
    rw [hFineS]
    have hb : suLeaf.position.board.left.bodyLabels =
        suBody.position.board.left.bodyLabels ++ [D.upper] := hbLeaf
    rw [hb, List.length_append, List.length_singleton]
    exact hiBody
  have hFineRel : fine.position.board.left.relaxed = true := by
    simpa only [hFineS, Board.get] using hrLeaf
  obtain ⟨r, hparse⟩ := LabeledWord.marker_blocks hmBody
  have hstartBody : suBody.position.board.left.parser ≠ .start := by simp [hparse]
  obtain ⟨newAtoms, hnewRun, hnewPool⟩ := follow_word_inputs hBodyFine 0 (fun _ => Nat.zero_le _) false
  have hFineRoot : fine.position.board.left.rootLabel = L.upper :=
    (hnewRun.rootLabel_eq hstartBody).trans hrootBody
  have hfullRun := htailRun.append hnewRun
  have hfullPool : ∀ atom ∈ (tail.map fun n => (∅, n)) ++ newAtoms,
      atom.2 ∈ H ∧ K < atom.2 := by
    intro atom ha
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
      exact htailPool x hx
    · exact ⟨hJH (hnewPool atom ha).1, hJfresh atom.2 (hnewPool atom ha).1⟩
  refine ⟨J, hJH, hJ, hJfresh, fine, hfromFine, hwinFine, hnFine, hFineRel,
    hFineRoot, hFineBody, ?_, _, hfullRun, hfullPool, M, hMfrom⟩
  intro hfirst
  have ha : 0 < a := L.lower_card ▸ Finset.card_pos.mpr ⟨L.pivot, L.pivot_lower⟩
  have hdLarge := first_body_request_large_of_reachable hHN hH blue origin suBody
    hwinOrigin ha hopening (by simp [hboardOrigin, Board.initial]) hfirst hsuBodyPath
    hpBody hmBody hnoBody
  have hcur : fine.position.board.left.currentLabel = D.upper := by
    have hb : suLeaf.position.board.left.bodyLabels =
        suBody.position.board.left.bodyLabels ++ [D.upper] := hbLeaf
    simp [hFineS, LabeledWord.currentLabel, hb]
  have hi : fine.position.board.left.leafIndex = D.pivot := by
    simpa only [hFineS, Board.get] using hiLeaf
  rw [hcur, hi]
  exact D.pivot_lt_upper_sup hdLarge

#print axioms reserved_inside_preparation

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
