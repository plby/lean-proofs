import ErdosProblems.Erdos118.Reused591.InsideAlignedEarly
import ErdosProblems.Erdos118.Reused591.InsideAlignedLastStart
import ErdosProblems.Erdos118.Reused591.InsideAlignedLastBridge
import ErdosProblems.Erdos118.Reused591.LastBodyUniformization

namespace Erdos118.Reused591

/-!
# The complete aligned inside case

Start at the actual positive first-root request, choose its separated
root labels, retain its literal execution, and build the three aligned
plays. The final bridge applies after a single preliminary thinning of
the right last-body singleton test. No first-body size assumption is
needed here; the initial first leaf is used only as a relaxed cursor.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem inside_aligned_of_uniform_last {N H : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (hroot : (exactGame N blue).ArchitectWins H b σ
      (History.initial (Position.Next N) Position.initial))
    {p : Concrete.Hist N} (hwin : (exactGame N blue).ArchitectWins H b σ p)
    {a : ℕ} (ha : 2 ≤ a) (hp : p.position.pending = some ⟨false, .advance a⟩)
    (hboard : p.position.board = Board.initial) (hmode : p.position.mode = some true)
    (hlarge : ∀ v d, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p v →
      v.position.pending = some ⟨false, .advance d⟩ → v.position.board.left.markerEvent = true →
      (∀ k ∈ v.position.board.left.rootLabel,
        k ≤ v.position.board.left.bodyLabels.length + 1) → 2 ≤ d)
    (hall : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p z →
      (exactGame N blue).kind z = .terminal w → alignedBodyCountColor z = true)
    (value : Bool)
    (hone : ∀ v d, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p v →
      v.position.pending = some ⟨true, .advance d⟩ → v.position.board.right.markerEvent = true →
      (∀ k ∈ v.position.board.right.rootLabel,
        k ≤ v.position.board.right.bodyLabels.length + 1) → decide (d = 1) = value) :
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
  obtain ⟨C, e, T, old, upper, c, _he, hstOld, hpUpper, hpOld, hOldRoot, hOldBody,
      hOldRel, hOldNo, hTRel, hTNo, hTroot, hTbody, hUpperP, hc, hUpperInit,
      _hUpperMode, hT, _hUpperRel, hUpperRoot, _hUpperBody, _hUpperFirst⟩ :=
    inside_aligned_early_histories hHN hH blue htri hroot p st L ha hwin hp hboard hmode
      hpST hall hnST hSTinit hrST hSTroot
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
  obtain ⟨J, _hJH, _hJ, CU, f, U, E, m, n, S, _hm, _hn, st₁, su₁, tu₁,
      hfromST, hfromSU, hfromTU, hpST₁, hpSU₁, hnTU₁, hS, hrST₁, hrSU₁,
      hlST₁, hlSU₁, hiST₁, hiSU₁, hrootST₁, hrootSU₁, hrT, hnoT, hrootT₁,
      hbodyT₁, hrU, hnoU, hrootU, hbodyU, hT₁, hU, hrootTV, hrootUV, hrUV, hsep⟩ :=
    inside_aligned_last_start hHN hH blue htri hroot p old upper L T ha hc hwin hp hboard
      hmode le_rfl (hpST.trans hstOld) hpUpper hpOld hOldRoot hOldBody hOldRel hOldNo
      hTRel hTNo hTroot hTbody hT hUpperRoot hUpperP hUpperInit hall hlarge hraw hinc hpool
  exact (inside_aligned_last_bridge_triangle hHN hH blue p st₁ su₁ tu₁ S T U ha
    hp hboard hmode hwin hfromST hfromSU hfromTU hall hlarge value hone hpST₁ hpSU₁ hnTU₁
    hS hrST₁ hrSU₁ hlST₁ hlSU₁ hiST₁ hiSU₁ hrootST₁ hrootSU₁ hrT hnoT hrootT₁ hbodyT₁
    hrU hnoU hrootU hbodyU hT₁ hU hrootTV hrootUV hrUV hsep) htri

theorem inside_aligned_triangle {N H : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (hroot : (exactGame N blue).ArchitectWins H b σ
      (History.initial (Position.Next N) Position.initial))
    {p : Concrete.Hist N} (hwin : (exactGame N blue).ArchitectWins H b σ p)
    {a : ℕ} (ha : 2 ≤ a) (hp : p.position.pending = some ⟨false, .advance a⟩)
    (hboard : p.position.board = Board.initial) (hmode : p.position.mode = some true)
    (hlarge : ∀ v d, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p v →
      v.position.pending = some ⟨false, .advance d⟩ → v.position.board.left.markerEvent = true →
      (∀ k ∈ v.position.board.left.rootLabel,
        k ≤ v.position.board.left.bodyLabels.length + 1) → 2 ≤ d)
    (hall : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p z →
      (exactGame N blue).kind z = .terminal w → alignedBodyCountColor z = true) :
    ¬ blue.CliqueFree 3 := by
  obtain ⟨L, hLH, hL, c, hbc, value, hone⟩ :=
    last_body_request_uniformization hHN hH blue b σ p true
  have paths {v w : Concrete.Hist N}
      (hpath : Relation.ReflTransGen ((exactGame N blue).FollowStep σ L c) v w) :
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) v w :=
    Relation.ReflTransGen.mono (fun _ _ hs =>
      FiniteResponseGame.FollowStep.mono (exactGame N blue) hLH hbc hs) _ _ hpath
  apply inside_aligned_of_uniform_last (hLH.trans hHN) hL blue
    (hroot.mono (exactGame N blue) hLH hbc) (hwin.mono (exactGame N blue) hLH hbc)
    ha hp hboard hmode
    (fun v d hpath hpv hm hr => hlarge v d (paths hpath) hpv hm hr)
    (fun z w hpath hz => hall z w (paths hpath) hz) value
  intro v d hpath hpv hm hr
  exact hone v ⟨true, .advance d⟩ hpath hpv rfl hm hr

#print axioms inside_aligned_of_uniform_last
#print axioms inside_aligned_triangle

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
