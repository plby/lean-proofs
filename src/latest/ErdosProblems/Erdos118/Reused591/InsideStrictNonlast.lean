import ErdosProblems.Erdos118.Reused591.StrictNonlastEarly
import ErdosProblems.Erdos118.Reused591.InsideStrictNonlastRankOnePivotTriangle
import ErdosProblems.Erdos118.Reused591.InsideStrictNonlastSplicedPivotTriangle

namespace Erdos118.Reused591

/-!
# The complete strict case with a nonlast critical second-word leaf

Retain the original S root prefix through the actual lower critical
checkpoint. The positive upper critical body rank is either one or
at least two; the two proved actual-root constructions cover both.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem inside_strict_nonlast_triangle {N H : Set ℕ}
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
      (exactGame N blue).kind z = .terminal w →
        z.position.board.left.beforeLastLeafCount < z.position.board.right.beforeLastLeafCount)
    (hlast : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p z →
      (exactGame N blue).kind z = .terminal w → criticalLastColor z = false) :
    ¬ blue.CliqueFree 3 := by
  intro htri
  let B := max p.position.bound (b p)
  obtain ⟨L⟩ := LastLastLabels.exists_of_infinite hH B a ha
  obtain ⟨u, last, tail, hr, huH, huB, htailRun, htailPool, hm, _hno, hlastRoot, _hcoords⟩ :=
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
  have hpBodyPath := (Relation.ReflTransGen.single hpq).tail hqBody
  have hBodyWord : body.position.board.left = last := by simpa only [hBodyBoard] using hqWord
  have hBodyRoot : body.position.board.left.rootLabel = L.lower := by
    simpa only [hBodyWord] using hlastRoot
  have hmBody : body.position.board.left.markerEvent = true := by simpa only [hBodyWord] using hm
  have hbaseRun : LabeledWord.LegalRun (LabeledCode.rootCursor L.lower L.marker)
      (tail.map fun n => (∅, n)) body.position.board.left := by
    simpa only [LabeledWord.rootRelabel_rootCursor, hBodyWord] using htailRun
  let Bbody := max body.position.bound (b body)
  obtain ⟨D⟩ := LastFirstLabels.exists_of_infinite hH Bbody 1 d (by omega) hd
  obtain ⟨st, _st', hBodyLeaf, _hBodyLeaf', hnST, _hnST', _hshapeST, hrST, _hrST',
      _hiST, _hiST', _hbST, _hbST', hoST, _hoST'⟩ :=
    first_leaf_gluing hHN hH blue σ body body false false D D rfl rfl hpBody hpBody
      hmBody hmBody (LabeledWord.SameStructure.refl _) le_rfl le_rfl
  have hpST := hpBodyPath.tail hBodyLeaf
  have hSTinit : st.position.board.right = LabeledWord.initial := by
    have ho : st.position.board.right = body.position.board.right := hoST
    have hrootOther : q.position.board.right = p.position.board.right := by
      simpa [hqBoard, Board.get] using hr.other_eq
    simp [ho, hBodyBoard, hrootOther, hboard, Board.initial]
  obtain ⟨r, hparse⟩ := LabeledWord.marker_blocks hmBody
  have hBodyStart : body.position.board.left.parser ≠ .start := by simp [hparse]
  obtain ⟨leafAtoms, hleafRun, _hleafPool⟩ := follow_step_word_inputs hBodyLeaf false
  have hSTroot : st.position.board.left.rootLabel = L.lower :=
    (hleafRun.rootLabel_eq hBodyStart).trans hBodyRoot
  obtain ⟨K, hKH, _hK, C, e, j, T, _hj, _hje, J, hJK, _hJ,
      BE, dE, cE, sE, E, _hcE, _hsE, _hsdE, old, upper, g, hstOld, hpUpperPath,
      hpOld, hOld, hTroot, hTbody, hTlabel, hTindex, hpUpper, hTshape,
      hUpperRel, hUpperRoot, _hUpperBody, hUpperLabel, hUpperIndex, hUpperInit,
      _hUpperMode, M, hMJ, hM, k, hk, hkg, hfixedUpper⟩ :=
    inside_strict_nonlast_early_histories hHN hH blue htri hroot p st ha hp hboard hmode hwin
      hpST hnST hSTinit hrST hfirst hall hlast
  have hSstart := LabeledWord.relaxed_ne_start
    ((Position.history_dataInvariant st).2.1 false).1 hrST
  obtain ⟨oldAtoms, hOldRun, _hOldPool⟩ :=
    follow_word_inputs hstOld 0 (fun _ => Nat.zero_le _) false
  have hOldRoot : old.position.board.left.rootLabel = L.lower :=
    (hOldRun.rootLabel_eq hSstart).trans hSTroot
  have hOldLast : old.position.board.left.lastSelectedBody = L.pivot := by
    rw [LabeledWord.lastSelectedBody, hOldRoot, L.lower_sup]
  have hOldBody : old.position.board.left.bodyLabels.length = L.penultimate := by
    have hselected : old.position.board.left.bodyLabels.length ∈ L.lower :=
      hOldRoot ▸ (of_decide_eq_true hOld.left_relaxed).2.1
    have hle := (L.lower_bounds _ hselected).resolve_left
      (by simpa only [hOldLast] using ne_of_lt hOld.left_before)
    have hge := hOld.left_penultimate L.penultimate (hOldRoot ▸ L.penultimate_lower)
      (by simpa only [hOldLast] using L.penultimate_lt_pivot)
    omega
  have hbodyOld := (Relation.ReflTransGen.single hBodyLeaf).trans hstOld
  obtain ⟨newAtoms, hnewRun, hnewPool⟩ :=
    follow_word_inputs hbodyOld 0 (fun _ => Nat.zero_le _) false
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
    obtain ⟨atom, hatom, rfl⟩ := List.mem_map.mp hx
    rcases List.mem_append.mp hatom with hatom | hatom
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hatom
      exact (htailPool y hy).1
    · exact (hnewPool atom hatom).1
  by_cases hkOne : k = 1
  · exact (inside_strict_nonlast_rank_one_pivot_triangle hHN
      ((hMJ.trans hJK).trans hKH) hM blue htri hroot p old upper L T E ha (by omega)
      hwin hp hboard hmode le_rfl (hpST.trans hstOld) hpUpperPath hpOld hOld
      hOldRoot hOldBody hTroot hTbody hTlabel hTindex hTshape hUpperRel hUpperRoot
      hUpperLabel hUpperIndex hpUpper hUpperInit hall hlast
      (fun z w hpath hz => by simpa only [hkOne] using hfixedUpper z w hpath hz)
      hraw hinc hpool) htri
  · exact (inside_strict_nonlast_spliced_pivot_triangle hHN
      ((hMJ.trans hJK).trans hKH) hM blue htri hroot p old upper L T E ha (by omega) hkg
      hwin hp hboard hmode le_rfl (hpST.trans hstOld) hpUpperPath hpOld hOld
      hOldRoot hOldBody hTroot hTbody hTlabel hTindex hTshape hUpperRel hUpperRoot
      hUpperLabel hUpperIndex hpUpper hUpperInit hall hlast hfixedUpper
      hraw hinc hpool) htri

#print axioms inside_strict_nonlast_triangle

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
