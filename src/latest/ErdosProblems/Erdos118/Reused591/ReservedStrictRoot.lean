import ErdosProblems.Erdos118.Reused591.ReservedOpeningHistory
import ErdosProblems.Erdos118.Reused591.FirstLeafGluingHistory
import ErdosProblems.Erdos118.Reused591.LastLastLabels
import ErdosProblems.Erdos118.Reused591.LocalCriticalUniformization

namespace Erdos118.Reused591

/-!
# Insert SU and localize its pending U root on the already restricted tail

The old S prefix is replayed with its reserved root label. New S
coordinates exceed the pending ST bound; new body and U-root inputs
come from the supplied future pool. The literal S continuation is
retained for the subsequent common last-marker response.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem reserved_strict_root_request {N H M : Set ℕ}
    (hHN : H ⊆ N) (hMH : M ⊆ H) (hM : M.Infinite)
    (blue : SimpleGraph G) (htri : blue.CliqueFree 3) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy}
    (hroot : (exactGame N blue).ArchitectWins H b σ
      (History.initial (Position.Next N) Position.initial))
    (origin old : Concrete.Hist N) {B a : ℕ} (S : LastLastLabels H B a) (ha : 2 ≤ a)
    (hwin : (exactGame N blue).ArchitectWins H b σ origin)
    (hop : origin.position.pending = some ⟨false, .advance a⟩)
    (hboard : origin.position.board = Board.initial) (hmode : origin.position.mode = some true)
    (hB : max origin.position.bound (b origin) ≤ B)
    (hOldBody : old.position.board.left.bodyLabels.length = S.penultimate)
    (hall : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin z →
      (exactGame N blue).kind z = .terminal w →
        z.position.board.left.beforeLastLeafCount < z.position.board.right.beforeLastLeafCount)
    {as : List (Finset ℕ × ℕ)}
    (hraw : (LabeledCode.rootCursor S.lower S.marker).runAtoms as = some old.position.board.left)
    (hinc : (S.marker :: as.map Prod.snd).Pairwise (· < ·))
    (hpool : ∀ x ∈ as.map Prod.snd, x ∈ H) :
    ∃ J, J ⊆ M ∧ J.Infinite ∧ (∀ x ∈ J, max old.position.bound (b old) < x) ∧
      ∃ su e, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin su ∧
        (exactGame N blue).ArchitectWins J b σ su ∧
        su.position.pending = some ⟨true, .advance e⟩ ∧ 0 < e ∧
        su.position.board.left.relaxed = true ∧ su.position.board.left.rootLabel = S.upper ∧
        su.position.board.left.bodyLabels.length = S.firstUpper ∧
        su.position.board.right = LabeledWord.initial ∧
        ∃ frontAtoms, LabeledWord.LegalRun
          (LabeledWord.rootRelabel S.upper old.position.board.left) frontAtoms
            su.position.board.left ∧
          (∀ atom ∈ frontAtoms, atom.2 ∈ H ∧ max old.position.bound (b old) < atom.2) ∧
          ∃ K, K ⊆ J ∧ K.Infinite ∧ ∃ j, 0 < j ∧ j < e ∧ ∀ z w,
            Relation.ReflTransGen ((exactGame N blue).FollowStep σ K b) su z →
            (exactGame N blue).kind z = .terminal w →
              z.position.board.right.criticalBodyRank z.position.board.left.lastSelectedLabel.card =
                j ∧ (criticalLastColor z = true → j + 1 < e) := by
  let bound := max old.position.bound (b old)
  let J := M \ Set.Iic bound
  have hJ : J.Infinite := hM.sdiff (Set.finite_Iic bound)
  have hJM : J ⊆ M := fun _ hx => hx.1
  have hJH := hJM.trans hMH
  have hJN := hJH.trans hHN
  have hJfresh : ∀ x ∈ J, bound < x := fun _ hx => lt_of_not_ge hx.2
  have pathH {p q : Concrete.Hist N}
      (hp : Relation.ReflTransGen ((exactGame N blue).FollowStep σ J b) p q) :
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q :=
    Relation.ReflTransGen.mono (fun _ _ hs =>
      FiniteResponseGame.FollowStep.mono (exactGame N blue) hJH (fun _ => le_rfl) hs) _ _ hp
  have hbefore : ∀ k ∈ S.upper, old.position.board.left.bodyLabels.length < k := by
    intro k hk
    rw [hOldBody]
    exact (S.upper_bounds k hk).1
  obtain ⟨suBody, d, hsuBodyPath, hpBody, hd, hmBody, hnoBody, hrootBody,
      hotherBody, tail, htailRun, htailPool, _htailCoords⟩ :=
    winning_reserved_root_request hHN (hM.mono hMH) blue hwin false hop
      (by simp [hboard, Board.initial, Board.get]) hraw S.upper_fresh S.marker_fresh
      S.upper_card ⟨S.pivot, S.pivot_upper⟩ hbefore hinc hpool hB bound
  change suBody.position.board.left.markerEvent = true at hmBody
  change suBody.position.board.left.NoRootPassed at hnoBody
  change suBody.position.board.left.rootLabel = S.upper at hrootBody
  change suBody.position.board.right = origin.position.board.right at hotherBody
  have hiBody : suBody.position.board.left.bodyLabels.length + 1 = S.firstUpper := by
    apply le_antisymm
    · exact hnoBody S.firstUpper (hrootBody ▸ S.firstUpper_mem)
    · exact S.firstUpper_le _ (hrootBody ▸ LabeledWord.marker_body_mem hmBody)
  have hrootJ := hroot.mono (exactGame N blue) hJH (fun _ => le_rfl)
  have hwinBody := (hwin.of_reachable (exactGame N blue) hsuBodyPath).mono
    (exactGame N blue) hJH (fun _ => le_rfl)
  let Bbody := max suBody.position.bound (b suBody)
  obtain ⟨D⟩ := LastFirstLabels.exists_of_infinite hJ Bbody 1 d (by omega) hd
  obtain ⟨suLeaf, _sameLeaf, hbodyLeaf, _hbodyLeaf', hnLeaf, _hnLeaf', _hshapeLeaf,
      hrLeaf, _hrLeaf', _hiLeaf, _hiLeaf', hbLeaf, _hbLeaf', hoLeaf, _hoLeaf'⟩ :=
    first_leaf_gluing hJN hJ blue σ suBody suBody false false D D rfl rfl hpBody hpBody
      hmBody hmBody (LabeledWord.SameStructure.refl _) le_rfl le_rfl
  have hwinLeaf := hwinBody.of_reachable (exactGame N blue) (.single hbodyLeaf)
  have hLeafInit : suLeaf.position.board.right = LabeledWord.initial := by
    have ho : suLeaf.position.board.right = suBody.position.board.right := hoLeaf
    simp [ho, hotherBody, hboard, Board.initial]
  obtain ⟨su, e, hLeafR, hboardR, hpR, he⟩ :=
    winning_initial_right_request hJN hJ blue htri hrootJ hwinLeaf hnLeaf hLeafInit hrLeaf
  have hBodyR := (Relation.ReflTransGen.single hbodyLeaf).tail hLeafR
  have hfromR := hsuBodyPath.trans (pathH hBodyR)
  have hsuInit : su.position.board.right = LabeledWord.initial := by
    simpa only [hboardR] using hLeafInit
  have hsuBody : su.position.board.left.bodyLabels.length = S.firstUpper := by
    rw [hboardR]
    have hb : suLeaf.position.board.left.bodyLabels =
        suBody.position.board.left.bodyLabels ++ [D.upper] := hbLeaf
    rw [hb, List.length_append, List.length_singleton]
    exact hiBody
  have hsuRel : su.position.board.left.relaxed = true := by
    simpa only [hboardR, Board.get] using hrLeaf
  obtain ⟨r, hparse⟩ := LabeledWord.marker_blocks hmBody
  have hstartBody : suBody.position.board.left.parser ≠ .start := by simp [hparse]
  obtain ⟨newAtoms, hnewRun, hnewPool⟩ := follow_word_inputs hBodyR 0 (fun _ => Nat.zero_le _) false
  have hsuRoot : su.position.board.left.rootLabel = S.upper :=
    (hnewRun.rootLabel_eq hstartBody).trans hrootBody
  have hfullPool : ∀ atom ∈ (tail.map fun n => (∅, n)) ++ newAtoms,
      atom.2 ∈ H ∧ bound < atom.2 := by
    intro atom hatom
    rcases List.mem_append.mp hatom with hatom | hatom
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hatom
      exact htailPool x hx
    · exact ⟨hJH (hnewPool atom hatom).1, hJfresh atom.2 (hnewPool atom hatom).1⟩
  obtain ⟨K, hKJ, hK, j, hj, hje, hfixed⟩ := strict_critical_body_local
    hHN hJH hJ blue origin su ha he hop hboard hmode hwin hfromR hpR hsuInit hall
  exact ⟨J, hJM, hJ, hJfresh, su, e, hfromR,
    hwinBody.of_reachable (exactGame N blue) hBodyR, hpR, he, hsuRel, hsuRoot, hsuBody, hsuInit,
    _, htailRun.append hnewRun, hfullPool, K, hKJ, hK, j, hj, hje, hfixed⟩

#print axioms reserved_strict_root_request

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
