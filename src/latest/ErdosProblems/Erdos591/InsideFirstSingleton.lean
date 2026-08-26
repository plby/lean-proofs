import ErdosProblems.Erdos591.InsideRootTriangle
import ErdosProblems.Erdos591.InsideForks
import ErdosProblems.Erdos591.FirstMarkerGluingHistory
import ErdosProblems.Erdos591.FirstBodyThinning

/-!
# Multiple root selections with singleton first-body requests

Use double-overlap root labels and identical singleton labels in their
common first selected body. The uniform first-body hypothesis is applied
to the two actual, potentially different opening histories. After the
inside forks, the lower last root index is the upper next root index.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem inside_first_singleton_triangle {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy}
    (hroot : (exactGame N blue).ArchitectWins H b σ
      (History.initial (Position.Next N) Position.initial))
    {p : Concrete.Hist N} (hwin : (exactGame N blue).ArchitectWins H b σ p)
    {a : ℕ} (ha : 2 ≤ a) (hp : p.position.pending = some ⟨false, .advance a⟩)
    (hboard : p.position.board = Board.initial) (hmode : p.position.mode = some true)
    (hfirst : ∀ q v d, (exactGame N blue).FollowStep σ H b p q →
      (exactGame N blue).FollowStep σ H b q v →
      v.position.pending = some ⟨false, .advance d⟩ → d = 1) : ¬ blue.CliqueFree 3 := by
  intro htri
  let B := max p.position.bound (b p)
  obtain ⟨D⟩ := DoubleOverlapLabels.exists_of_infinite hH B a ha
  have hi : p.position.board.get false = LabeledWord.initial := by
    simp [hboard, Board.initial, Board.get]
  obtain ⟨mSU, mST, hsMSU, hsMST, hnMSU, hnMST, hshapeM, hmSU, hmST,
      hidxMSU, hidxMST, hrootSU, hrootST, hoMSU, hoMST⟩ :=
    first_marker_gluing hHN hH blue σ p p false false D.first_to_lower D.first_to_upper
      rfl rfl hp hp hi hi le_rfl le_rfl
  have hwinMSU := hwin.of_reachable (exactGame N blue) (Relation.ReflTransGen.single hsMSU)
  have hwinMST := hwin.of_reachable (exactGame N blue) (Relation.ReflTransGen.single hsMST)
  obtain ⟨bSU, dSU, hsBSU, hbSU, hpBSU, _hdSU⟩ :=
    winning_request_at_marker hHN hH blue hwinMSU false hnMSU hmSU
  obtain ⟨bST, dST, hsBST, hbST, hpBST, _hdST⟩ :=
    winning_request_at_marker hHN hH blue hwinMST false hnMST hmST
  have hdSU := hfirst mSU bSU dSU hsMSU hsBSU hpBSU
  have hdST := hfirst mST bST dST hsMST hsBST hpBST
  subst dSU
  subst dST
  let C := max (max bSU.position.bound (b bSU)) (max bST.position.bound (b bST))
  obtain ⟨L⟩ := LastFirstLabels.exists_of_infinite hH C 1 1 (by omega) (by omega)
  obtain ⟨su₀, st₀, hsSU, hsST, hnSU, hnST, hshape₀, hrSU, hrST, _hidxSU, hidxST,
      hlabelsSU, hlabelsST, hoSU, hoST⟩ := first_leaf_gluing hHN hH blue σ bSU bST false false
    L L rfl rfl hpBSU hpBST (by simpa [hbSU] using hmSU) (by simpa [hbST] using hmST)
      (by rw [hbSU, hbST]; exact hshapeM) (le_max_left _ _) (le_max_right _ _)
  have hpathSU₀ := ((Relation.ReflTransGen.single hsMSU).tail hsBSU).tail hsSU
  have hpathST₀ := ((Relation.ReflTransGen.single hsMST).tail hsBST).tail hsST
  have hwinSU₀ := hwin.of_reachable (exactGame N blue) hpathSU₀
  have hwinST₀ := hwin.of_reachable (exactGame N blue) hpathST₀
  have hiSU : su₀.position.board.right = LabeledWord.initial := by
    have hoM : mSU.position.board.right = LabeledWord.initial := by
      simpa [Board.get, hboard, Board.initial] using hoMSU
    simpa [Board.get, hbSU, hoM] using hoSU
  have hiST : st₀.position.board.right = LabeledWord.initial := by
    have hoM : mST.position.board.right = LabeledWord.initial := by
      simpa [Board.get, hboard, Board.initial] using hoMST
    simpa [Board.get, hbST, hoM] using hoST
  obtain ⟨pSU, e, hreqSU, hbRSU, hpRSU, he⟩ := winning_initial_right_request hHN hH blue htri hroot
    hwinSU₀ hnSU hiSU hrSU
  obtain ⟨pST, f, hreqST, hbRST, hpRST, hf⟩ := winning_initial_right_request hHN hH blue htri hroot
    hwinST₀ hnST hiST hrST
  have hpathSU := hpathSU₀.tail hreqSU
  have hpathST := hpathST₀.tail hreqST
  let upper : Bool → Concrete.Hist N := fun s => if s then pSU else pST
  let sizes : Bool → ℕ := fun s => if s then e else f
  have hwins : ∀ s, (exactGame N blue).ArchitectWins H b σ (upper s) := by
    intro s
    cases s
    · exact hwin.of_reachable (exactGame N blue) hpathST
    · exact hwin.of_reachable (exactGame N blue) hpathSU
  have hpos : ∀ s, 0 < sizes s := by intro s; cases s <;> assumption
  have hpend : ∀ s, (upper s).position.pending = some ⟨true, .advance (sizes s)⟩ := by
    intro s
    cases s
    · exact hpRST
    · exact hpRSU
  have hinit : ∀ s, (upper s).position.board.right = LabeledWord.initial := by
    intro s
    cases s <;> simp [upper, hbRST, hbRSU, hiST, hiSU]
  have hmodes : ∀ s, (upper s).position.mode = some true := by
    intro s
    cases s
    · exact follow_mode_some hpathST hmode
    · exact follow_mode_some hpathSU hmode
  obtain ⟨tu, _hpathTU, hwinTU, hmTU, hlast, hforks⟩ := Relay.inside_forks hHN hH blue htri hroot
    hwin (by omega) hp hboard hmode upper sizes hwins hpos hpend hinit hmodes
  obtain ⟨hrT, st, hwinST, _hnST, _hmST, hT, hrSTright, hleftST, hsepST⟩ := hforks false
  obtain ⟨hrU, su, hwinSU, _hnSU, hmSU', hU, hrSUright, hleftSU, _hsepSU⟩ := hforks true
  have hleftST' : st.position.board.left = st₀.position.board.left := by
    simpa [upper, hbRST] using hleftST
  have hleftSU' : su.position.board.left = su₀.position.board.left := by
    simpa [upper, hbRSU] using hleftSU
  have hcountSU : su.position.board.left.bodyLabels.length = D.first := by
    rw [hleftSU']
    have hl := congrArg List.length hlabelsSU
    simp only [List.length_append, List.length_singleton, hbSU, Board.get] at hl
    change mSU.position.board.left.bodyLabels.length + 1 = D.first at hidxMSU
    omega
  have hcountST : st.position.board.left.bodyLabels.length = D.first := by
    rw [hleftST']
    have hl := congrArg List.length hlabelsST
    simp only [List.length_append, List.length_singleton, hbST, Board.get] at hl
    change mST.position.board.left.bodyLabels.length + 1 = D.first at hidxMST
    omega
  have hrootsSU : su.position.board.left.rootLabel = D.lower := by
    rw [hleftSU']
    obtain ⟨r, hparse⟩ := LabeledWord.marker_blocks hmSU
    obtain ⟨as, has, _⟩ := follow_word_inputs ((Relation.ReflTransGen.single hsBSU).tail hsSU)
      0 (fun _ => Nat.zero_le _) false
    exact (has.rootLabel_eq (by simp [hparse])).trans hrootSU
  have hrootsST : st.position.board.left.rootLabel = D.upper := by
    rw [hleftST']
    obtain ⟨r, hparse⟩ := LabeledWord.marker_blocks hmST
    obtain ⟨as, has, _⟩ := follow_word_inputs ((Relation.ReflTransGen.single hsBST).tail hsST)
      0 (fun _ => Nat.zero_le _) false
    exact (has.rootLabel_eq (by simp [hparse])).trans hrootST
  have hnoLeaf : st.position.board.left.NoLeafPending := by
    rw [hleftST']
    have hcurrent : st₀.position.board.left.currentLabel = L.upper := by
      simp [LabeledWord.currentLabel, show st₀.position.board.left.bodyLabels =
        bST.position.board.left.bodyLabels ++ [L.upper] from hlabelsST]
    intro k hk
    have heq : k = L.pivot := Finset.card_le_one.mp L.upper_card.le k (hcurrent ▸ hk)
      L.pivot L.pivot_upper
    change k ≤ st₀.position.board.left.leafIndex
    exact heq.le.trans hidxST.ge
  apply inside_triangle_of_root_forks hHN hH blue st su tu hwinST hwinSU hwinTU hmSU' hmTU
    hlast hrT hrU hrSTright hsepST hrSUright
    (by rw [hleftST', hleftSU']; exact hshape₀.symm) hT.symm hU.symm
    (by rw [hleftST']; exact hrST) hnoLeaf
    (i := D.pivot) ⟨hrootsST ▸ D.pivot_upper, hcountST ▸ D.first_lt_pivot⟩ ?_
    ⟨hrootsSU ▸ D.pivot_lower, hcountSU ▸ D.first_lt_pivot⟩
    (fun k hk => (D.lower_bounds k (hrootsSU ▸ hk)).2) htri
  intro k hk hlt
  rcases D.upper_bounds k (hrootsST ▸ hk) with heq | hle
  · rw [heq, hcountST] at hlt
    exact (Nat.lt_irrefl _ hlt).elim
  · exact hle

#print axioms inside_first_singleton_triangle

end Erdos591.Positive.Game.Payoff
