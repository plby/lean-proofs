import ErdosProblems.Erdos118.Reused591.InsideSingletonEarly
import ErdosProblems.Erdos118.Reused591.InsideSingletonInsertion
import ErdosProblems.Erdos118.Reused591.InsideFirstBodyReduction

namespace Erdos118.Reused591

/-!
# The complete last-body singleton inside case

Choose separated root labels sharing only their last index. Construct
the actual first lower response and its nonlast first leaf, retain its
root-prefix execution, build the early histories, insert the other lower
play, and apply the checked singleton bridge. The first-body reduction
removes the provisional nonsingleton-first-body hypothesis.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem inside_last_singleton_of_first_large {N H : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (hroot : (exactGame N blue).ArchitectWins H b σ
      (History.initial (Position.Next N) Position.initial))
    {p : Concrete.Hist N} (hwin : (exactGame N blue).ArchitectWins H b σ p)
    {a : ℕ} (ha : 2 ≤ a) (hp : p.position.pending = some ⟨false, .advance a⟩)
    (hboard : p.position.board = Board.initial) (hmode : p.position.mode = some true)
    (hfirst : ∀ q v d, (exactGame N blue).FollowStep σ H b p q →
      (exactGame N blue).FollowStep σ H b q v →
      v.position.pending = some ⟨false, .advance d⟩ → 2 ≤ d)
    (hall : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p z →
      (exactGame N blue).kind z = .terminal w → lastBodySingletonColor false z = true) :
    ¬ blue.CliqueFree 3 := by
  intro htri
  let B := max p.position.bound (b p)
  obtain ⟨L⟩ := LastLastLabels.exists_of_infinite hH B a ha
  obtain ⟨u, last, tail, hr, huH, huB, htailRun, htailPool, hm, hno, hlastRoot, _hcoords⟩ :=
    Reply.reserved_root_exists_run hH p.position.board false
      (by simp [hboard, Board.initial, Board.get])
      (D := L.lower) (C := L.lower) (as := [])
      (w := LabeledCode.rootCursor L.lower L.marker) rfl L.lower_fresh L.marker_fresh
      ⟨L.pivot, L.pivot_lower⟩
      (fun k hk => by simpa [LabeledCode.rootCursor] using
        (Nat.zero_le B).trans_lt (L.lower_fresh k hk).2.1)
      (by simp) (by simp) B
  rw [L.lower_card] at hr
  obtain ⟨q, hpq, hqBoard, hqNone⟩ := Concrete.follow_reply hHN (payoff blue) σ p hp hr huH
    (fun x hx => ⟨(le_max_left _ _).trans_lt (huB x hx),
      (le_max_right _ _).trans_lt (huB x hx)⟩)
  have hqWord : q.position.board.left = last := by simp [hqBoard, Board.update]
  have hwinQ := hwin.of_reachable (exactGame N blue) (Relation.ReflTransGen.single hpq)
  obtain ⟨body, d, hqBody, hBodyBoard, hpBody, hd⟩ := winning_request_at_marker hHN hH blue
    hwinQ false hqNone (by simpa [Board.get, hqWord] using hm)
  have hdLarge : 2 ≤ d := hfirst q body d hpq hqBody hpBody
  have hpBodyPath := (Relation.ReflTransGen.single hpq).tail hqBody
  have hBodyWord : body.position.board.left = last := by simpa only [hBodyBoard] using hqWord
  have hBodyRoot : body.position.board.left.rootLabel = L.lower := by
    simpa only [hBodyWord] using hlastRoot
  have hmBody : body.position.board.left.markerEvent = true := by simpa only [hBodyWord] using hm
  have hNoBody : body.position.board.left.NoRootPassed := by simpa only [hBodyWord] using hno
  have hiBody : body.position.board.left.bodyLabels.length + 1 = L.firstLower := by
    apply le_antisymm (hNoBody L.firstLower (hBodyRoot ▸ L.firstLower_mem))
    exact L.firstLower_le _ (hBodyRoot ▸ LabeledWord.marker_body_mem hmBody)
  have hbaseRun : LabeledWord.LegalRun (LabeledCode.rootCursor L.lower L.marker)
      (tail.map fun n => (∅, n)) body.position.board.left := by
    simpa only [LabeledWord.rootRelabel_rootCursor, hBodyWord] using htailRun
  let Bbody := max body.position.bound (b body)
  obtain ⟨D⟩ := LastFirstLabels.exists_of_infinite hH Bbody 1 d (by omega) hd
  obtain ⟨st, _st', hBodyLeaf, _hBodyLeaf', hnST, _hnST', _hshapeST, hrST, _hrST',
      hiST, _hiST', hbST, _hbST', hoST, _hoST'⟩ :=
    first_leaf_gluing hHN hH blue σ body body false false D D rfl rfl hpBody hpBody
      hmBody hmBody (LabeledWord.SameStructure.refl _) le_rfl le_rfl
  have hpST := hpBodyPath.tail hBodyLeaf
  have hSTinit : st.position.board.right = LabeledWord.initial := by
    have ho : st.position.board.right = body.position.board.right := hoST
    have hrootOther : q.position.board.right = p.position.board.right := by
      simpa [hqBoard, Board.get] using hr.other_eq
    simp [ho, hBodyBoard, hrootOther, hboard, Board.initial]
  have hSTbody : st.position.board.left.bodyLabels.length = L.firstLower := by
    have hb : st.position.board.left.bodyLabels = body.position.board.left.bodyLabels ++ [D.upper] :=
      hbST
    rw [hb, List.length_append, List.length_singleton]
    exact hiBody
  obtain ⟨r, hparse⟩ := LabeledWord.marker_blocks hmBody
  have hBodyStart : body.position.board.left.parser ≠ .start := by simp [hparse]
  obtain ⟨leafAtoms, hleafRun, _hleafPool⟩ := follow_step_word_inputs hBodyLeaf false
  have hSTroot : st.position.board.left.rootLabel = L.lower :=
    (hleafRun.rootLabel_eq hBodyStart).trans hBodyRoot
  have hSTcurrent : st.position.board.left.currentLabel = D.upper := by
    simp [LabeledWord.currentLabel, show st.position.board.left.bodyLabels =
      body.position.board.left.bodyLabels ++ [D.upper] from hbST]
  have hSTstrict : st.position.board.left.leafIndex < st.position.board.left.currentLabel.sup id := by
    rw [hSTcurrent, show st.position.board.left.leafIndex = D.pivot from hiST]
    exact D.pivot_lt_upper_sup hdLarge
  obtain ⟨old, upper, c, hstOld, hpUpper, hpOld, hOldRoot, hOldBody, hOldRel, hOldNo,
      hTRel, hTLast, hUpperP, hc, hUpperInit, hUpperMode, hT⟩ :=
    inside_singleton_early_histories hHN hH blue htri hroot p st L hwin hp hboard hmode
      hpST hall hnST hSTinit hrST hSTroot hSTbody hSTstrict
  have hbodyOld := (Relation.ReflTransGen.single hBodyLeaf).trans hstOld
  obtain ⟨newAtoms, hnewRun, hnewPool⟩ := follow_word_inputs hbodyOld 0 (fun _ => Nat.zero_le _) false
  have hfullRun := hbaseRun.append hnewRun
  let atoms := (tail.map fun n => (∅, n)) ++ newAtoms
  have hraw : (LabeledCode.rootCursor L.lower L.marker).runAtoms atoms =
      some old.position.board.left := hfullRun.run
  have hcoords : old.position.board.left.coordinates = L.marker :: atoms.map Prod.snd := by
    simpa [LabeledCode.rootCursor] using LabeledWord.runAtoms_coordinates hraw
  have hinc : (L.marker :: atoms.map Prod.snd).Pairwise (· < ·) := by
    rw [← hcoords]
    exact ((Position.history_dataInvariant old).2.1 false).2
  have hpool : ∀ x ∈ atoms.map Prod.snd, x ∈ H := by
    intro x hx
    obtain ⟨atom, ha, rfl⟩ := List.mem_map.mp hx
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp ha
      exact (htailPool y hy).1
    · exact (hnewPool atom ha).1
  exact (inside_singleton_insertion_triangle hHN hH blue htri hroot p old upper L hwin hp
    hboard hmode le_rfl (hpST.trans hstOld) hpUpper hall hpOld hOldRoot hOldBody hOldRel hOldNo
    hTRel hTLast hUpperP hc hUpperInit hUpperMode hT hraw hinc hpool) htri

theorem inside_last_singleton_triangle {N H : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (hroot : (exactGame N blue).ArchitectWins H b σ
      (History.initial (Position.Next N) Position.initial))
    {p : Concrete.Hist N} (hwin : (exactGame N blue).ArchitectWins H b σ p)
    {a : ℕ} (ha : 0 < a) (hp : p.position.pending = some ⟨false, .advance a⟩)
    (hboard : p.position.board = Board.initial) (hmode : p.position.mode = some true)
    (hall : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p z →
      (exactGame N blue).kind z = .terminal w → lastBodySingletonColor false z = true) :
    ¬ blue.CliqueFree 3 := by
  intro htri
  obtain ⟨haLarge, L, hLH, hL, hfirst⟩ :=
    inside_large_first_body_reduction hHN hH blue htri hroot hwin ha hp hboard hmode
  apply inside_last_singleton_of_first_large (hLH.trans hHN) hL blue
    (hroot.mono (exactGame N blue) hLH (fun _ => le_rfl))
    (hwin.mono (exactGame N blue) hLH (fun _ => le_rfl)) haLarge hp hboard hmode hfirst _ htri
  intro z w hpath hz
  apply hall z w _ hz
  exact Relation.ReflTransGen.mono (fun _ _ hs =>
    FiniteResponseGame.FollowStep.mono (exactGame N blue) hLH (fun _ => le_rfl) hs) _ _ hpath

#print axioms inside_last_singleton_of_first_large
#print axioms inside_last_singleton_triangle

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
