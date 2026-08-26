import ErdosProblems.Erdos591.InsideLeafTriangle
import ErdosProblems.Erdos591.InsideForks
import ErdosProblems.Erdos591.InsideLastBodySize

/-!
# An inside first-word marker that is already the last selected body

Use double-overlap leaf labels in two copies of the same pending body
history. Their common first leaf starts the two delayed right plays;
the lower last leaf is the upper next leaf. The actual fork construction
and the last/next-leaf triangle discharge all subsequent play choices.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem inside_last_body_triangle {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy}
    (hroot : (exactGame N blue).ArchitectWins H b σ
      (History.initial (Position.Next N) Position.initial))
    {opening : Concrete.Hist N} (hwinOpening : (exactGame N blue).ArchitectWins H b σ opening)
    {a : ℕ} (ha : 0 < a) (hpOpening : opening.position.pending = some ⟨false, .advance a⟩)
    (hbOpening : opening.position.board = Board.initial)
    (hmOpening : opening.position.mode = some true)
    {p : Concrete.Hist N} (hwin : (exactGame N blue).ArchitectWins H b σ p)
    (hmode : p.position.mode = some true) (hi : p.position.board.right = LabeledWord.initial)
    {d : ℕ} (hd : 0 < d) (hp : p.position.pending = some ⟨false, .advance d⟩)
    (hm : p.position.board.left.markerEvent = true)
    (hrootLast : ∀ i ∈ p.position.board.left.rootLabel,
      i ≤ p.position.board.left.bodyLabels.length + 1) : ¬ blue.CliqueFree 3 := by
  intro htri
  have hd₂ := winning_inside_last_body_size hHN hH blue htri hroot hwin hmode hi hd hp hm hrootLast
  let B := max p.position.bound (b p)
  obtain ⟨L⟩ := DoubleOverlapLabels.exists_of_infinite hH B d hd₂
  obtain ⟨su₀, st₀, hsSU, hsST, hnSU, hnST, hshape₀, hrSU, hrST, hidxSU, hidxST,
      hlabelsSU, hlabelsST, hoSU, hoST⟩ := first_leaf_gluing hHN hH blue σ p p false false
    L.first_to_lower L.first_to_upper rfl rfl hp hp hm hm
    (LabeledWord.SameStructure.refl _) le_rfl le_rfl
  have hwinSU₀ := hwin.of_reachable (exactGame N blue) (Relation.ReflTransGen.single hsSU)
  have hwinST₀ := hwin.of_reachable (exactGame N blue) (Relation.ReflTransGen.single hsST)
  obtain ⟨pSU, e, hreqSU, hbSU, hpSU, he⟩ := winning_initial_right_request hHN hH blue htri hroot
    hwinSU₀ hnSU (by simpa [Board.get, hi] using hoSU) hrSU
  obtain ⟨pST, f, hreqST, hbST, hpST, hf⟩ := winning_initial_right_request hHN hH blue htri hroot
    hwinST₀ hnST (by simpa [Board.get, hi] using hoST) hrST
  have hpathSU := (Relation.ReflTransGen.single hsSU).tail hreqSU
  have hpathST := (Relation.ReflTransGen.single hsST).tail hreqST
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
    · exact hpST
    · exact hpSU
  have hinit : ∀ s, (upper s).position.board.right = LabeledWord.initial := by
    intro s
    cases s
    · simpa [upper, hbST, Board.get, hi] using hoST
    · simpa [upper, hbSU, Board.get, hi] using hoSU
  have hmodes : ∀ s, (upper s).position.mode = some true := by
    intro s
    cases s
    · exact follow_mode_some hpathST hmode
    · exact follow_mode_some hpathSU hmode
  obtain ⟨tu, _hpathTU, hwinTU, hmTU, hlast, hforks⟩ := Relay.inside_forks hHN hH blue htri hroot
    hwinOpening ha hpOpening hbOpening hmOpening upper sizes hwins hpos hpend hinit hmodes
  obtain ⟨hrT, st, hwinST, _hnST, _hmST, hT, hrSTright, hleftST, hsepST⟩ := hforks false
  obtain ⟨hrU, su, hwinSU, _hnSU, hmSU, hU, hrSUright, hleftSU, _hsepSU⟩ := hforks true
  have hleftST' : st.position.board.left = st₀.position.board.left := by
    simpa [upper, hbST] using hleftST
  have hleftSU' : su.position.board.left = su₀.position.board.left := by
    simpa [upper, hbSU] using hleftSU
  have hlabelSU : su.position.board.left.currentLabel = L.lower := by
    rw [hleftSU']
    simp [LabeledWord.currentLabel, show su₀.position.board.left.bodyLabels =
      p.position.board.left.bodyLabels ++ [L.lower] from hlabelsSU]
  have hlabelST : st.position.board.left.currentLabel = L.upper := by
    rw [hleftST']
    simp [LabeledWord.currentLabel, show st₀.position.board.left.bodyLabels =
      p.position.board.left.bodyLabels ++ [L.upper] from hlabelsST]
  have hindexSU : su.position.board.left.leafIndex = L.first := by
    rw [hleftSU']
    exact hidxSU
  have hindexST : st.position.board.left.leafIndex = L.first := by
    rw [hleftST']
    exact hidxST
  have hselectSU : su.position.board.left.bodyLabels.length ∈ su.position.board.left.rootLabel := by
    rw [hleftSU']
    exact (of_decide_eq_true hrSU).2.1
  have hselectST : st.position.board.left.bodyLabels.length ∈ st.position.board.left.rootLabel := by
    rw [hleftST']
    exact (of_decide_eq_true hrST).2.1
  have hrootFinal : ∀ i ∈ su.position.board.left.rootLabel,
      i ≤ su.position.board.left.bodyLabels.length := by
    rw [hleftSU']
    obtain ⟨r, hparse⟩ := LabeledWord.marker_blocks hm
    obtain ⟨as, has, _hpool⟩ := follow_word_inputs (Relation.ReflTransGen.single hsSU)
      0 (fun _ => Nat.zero_le _) false
    have hroots := has.rootLabel_eq (by simp [Board.get, hparse])
    intro i himem
    have hi' := hrootLast i (hroots ▸ himem)
    have hlen : su₀.position.board.left.bodyLabels.length =
        p.position.board.left.bodyLabels.length + 1 := by
      simpa only [List.length_append, List.length_singleton, Board.get] using
        congrArg List.length hlabelsSU
    omega
  apply inside_triangle_of_leaf_forks hHN hH blue st su tu hwinST hwinSU hwinTU hmSU hmTU
    hlast hrT hrU hrSTright hsepST hrSUright
    (by rw [hleftST', hleftSU']; exact hshape₀.symm) hT.symm hU.symm
    (j := L.pivot) ⟨hselectST, hlabelST ▸ L.pivot_upper,
      hindexST ▸ L.first_lt_pivot.le⟩ (hindexST ▸ L.first_lt_pivot) ?_
    ⟨hselectSU, hlabelSU ▸ L.pivot_lower, hindexSU ▸ L.first_lt_pivot.le⟩ hrootFinal
    (fun k hk => (L.lower_bounds k (hlabelSU ▸ hk)).2) htri
  intro k hk hlt
  rcases L.upper_bounds k (hlabelST ▸ hk) with heq | hle
  · rw [heq, hindexST] at hlt
    exact (Nat.lt_irrefl _ hlt).elim
  · exact hle

#print axioms inside_last_body_triangle

end Erdos591.Positive.Game.Payoff
