/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos916.Reduction

namespace Erdos916

universe u

/-- The minimum-degree case needed after repeatedly deleting vertices of degree at most two. -/
def MinDegreeCorePrinciple : Prop :=
  ∀ (W : Type u) [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj],
      4 ≤ Fintype.card W →
      2 * Fintype.card W ≤ H.edgeFinset.card + 2 →
      (∀ w : W, 3 ≤ H.degree w) →
      HasWheelWitness H

/-- Four vertices and density `2n-2` force the complete graph. -/
theorem eq_top_of_card_four_of_dense {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V = 4)
    (hdense : 2 * Fintype.card V ≤ G.edgeFinset.card + 2) :
    G = ⊤ := by
  have hle := G.card_edgeFinset_le_card_choose_two
  have htopcard := SimpleGraph.card_edgeFinset_top_eq_card_choose_two (V := V)
  have hGcard : G.edgeFinset.card = 6 := by
    have hchoose : (4 : ℕ).choose 2 = 6 := by decide
    rw [hcard] at hdense hle
    rw [hchoose] at hle
    norm_num at hdense
    omega
  apply SimpleGraph.edgeFinset_inj.mp
  apply Finset.eq_of_subset_of_card_le (SimpleGraph.edgeFinset_mono le_top)
  rw [hGcard, htopcard, hcard]
  decide

/-- The elementary peeling step reducing the density theorem to minimum degree three. -/
theorem dense_hasWheel_of_minDegreeCore
    (hcore : ∀ (W : Type u) [Fintype W] [DecidableEq W]
      (H : SimpleGraph W) [DecidableRel H.Adj],
        4 ≤ Fintype.card W →
        2 * Fintype.card W ≤ H.edgeFinset.card + 2 →
        (∀ w : W, 3 ≤ H.degree w) →
        HasWheelWitness H)
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : 4 ≤ Fintype.card V)
    (hdense : 2 * Fintype.card V ≤ G.edgeFinset.card + 2) :
    HasWheelWitness G := by
  classical
  induction hn : Fintype.card V using Nat.strong_induction_on generalizing V with
  | h n ih =>
      by_cases hn4 : n = 4
      · have htop : G = ⊤ :=
          eq_top_of_card_four_of_dense G (by omega) (by simpa [hn] using hdense)
        have hle : (⊤ : SimpleGraph V) ≤ G := by rw [htop]
        exact HasWheelWitness.mono hle
          (hasWheelWitness_top (by simpa [hn] using hcard))
      · have hn5 : 5 ≤ n := by omega
        by_cases hmin : ∀ v : V, 3 ≤ G.degree v
        · exact hcore V G (by simpa [hn] using hcard)
            (by simpa [hn] using hdense) hmin
        · push Not at hmin
          obtain ⟨v, hv⟩ := hmin
          have hv2 : G.degree v ≤ 2 := by omega
          let W : Type u := {x : V // x ∈ ({v}ᶜ : Set V)}
          let H : SimpleGraph W := G.induce ({v}ᶜ : Set V)
          have hcardW : Fintype.card W = n - 1 := by
            dsimp [W]
            simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
            rw [Fintype.card_subtype_compl]
            simp [hn]
          have hcardW4 : 4 ≤ Fintype.card W := by omega
          have hcardWlt : Fintype.card W < n := by omega
          have hedgeInd := G.card_edgeFinset_induce_compl_singleton v
          have hedgeDel := G.card_edgeFinset_deleteIncidenceSet v
          have hHedges : H.edgeFinset.card = G.edgeFinset.card - G.degree v := by
            exact hedgeInd.trans hedgeDel
          have hHdense : 2 * Fintype.card W ≤ H.edgeFinset.card + 2 := by
            omega
          have hHW : HasWheelWitness H :=
            ih _ hcardWlt H hcardW4 hHdense rfl
          exact HasWheelWitness.induce ({v}ᶜ : Set V) hHW

/-- The full density induction from the Thomassen--Toft minimum-degree reduction. -/
theorem dense_hasWheel_of_reduction
    (hstruct : ∀ (W : Type u) [Fintype W] [DecidableEq W]
      (H : SimpleGraph W) [DecidableRel H.Adj],
        4 ≤ Fintype.card W →
        (∀ w : W, 3 ≤ H.degree w) →
        HasWheelWitness H ∨ Nonempty (K23Reduction H))
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : 4 ≤ Fintype.card V)
    (hdense : 2 * Fintype.card V ≤ G.edgeFinset.card + 2) :
    HasWheelWitness G := by
  classical
  induction hn : Fintype.card V using Nat.strong_induction_on generalizing V with
  | h n ih =>
      by_cases hn4 : n = 4
      · have htop : G = ⊤ :=
          eq_top_of_card_four_of_dense G (by omega) (by simpa [hn] using hdense)
        have hle : (⊤ : SimpleGraph V) ≤ G := by rw [htop]
        exact HasWheelWitness.mono hle
          (hasWheelWitness_top (by simpa [hn] using hcard))
      · have hn5 : 5 ≤ n := by omega
        by_cases hmin : ∀ v : V, 3 ≤ G.degree v
        · rcases hstruct V G (by simpa [hn] using hcard) hmin with hW | hR
          · exact hW
          · obtain ⟨R⟩ := hR
            have hn6 : 6 ≤ n := by
              rw [← hn]
              exact R.six_le_card
            by_cases hn8 : 8 ≤ n
            · let W : Type u := {v : V // v ∉ R.deletedFour}
              letI : Fintype R.remaining.edgeSet := R.remaining.fintypeEdgeSet
              have hWcard : Fintype.card W = n - 4 := by
                simpa [W, hn] using R.card_remaining_vertices
              have hWcard4 : 4 ≤ Fintype.card W := by omega
              have hWlt : Fintype.card W < n := by omega
              have hWedges : R.remaining.edgeFinset.card + 8 = G.edgeFinset.card := by
                change R.remaining.edgeSet.toFinset.card + 8 = G.edgeSet.toFinset.card
                rw [← Set.ncard_eq_toFinset_card', ← Set.ncard_eq_toFinset_card']
                exact R.ncard_remaining_add_eight
              have hWdense :
                  2 * Fintype.card W ≤ R.remaining.edgeFinset.card + 2 := by
                omega
              have hWH : HasWheelWitness R.remaining :=
                ih _ hWlt R.remaining hWcard4 hWdense rfl
              exact R.wheel_of_remaining hWH
            · have hnle7 : n ≤ 7 := by omega
              have hn67 : n = 6 ∨ n = 7 := by omega
              rcases hn67 with hn6eq | hn7eq
              · have hV6 : Fintype.card V = 6 := hn.trans hn6eq
                have hedge := R.edge_card_le_nine_of_card_eq_six hV6
                omega
              · have hV7 : Fintype.card V = 7 := hn.trans hn7eq
                have hedge := R.edge_card_le_eleven_of_card_eq_seven hV7
                omega
        · push Not at hmin
          obtain ⟨v, hv⟩ := hmin
          have hv2 : G.degree v ≤ 2 := by omega
          let W : Type u := {x : V // x ∈ ({v}ᶜ : Set V)}
          let H : SimpleGraph W := G.induce ({v}ᶜ : Set V)
          have hcardW : Fintype.card W = n - 1 := by
            dsimp [W]
            simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
            rw [Fintype.card_subtype_compl]
            simp [hn]
          have hcardW4 : 4 ≤ Fintype.card W := by omega
          have hcardWlt : Fintype.card W < n := by omega
          have hedgeInd := G.card_edgeFinset_induce_compl_singleton v
          have hedgeDel := G.card_edgeFinset_deleteIncidenceSet v
          have hHedges : H.edgeFinset.card = G.edgeFinset.card - G.degree v := by
            exact hedgeInd.trans hedgeDel
          have hHdense : 2 * Fintype.card W ≤ H.edgeFinset.card + 2 := by
            omega
          have hHW : HasWheelWitness H :=
            ih _ hcardWlt H hcardW4 hHdense rfl
          exact HasWheelWitness.induce ({v}ᶜ : Set V) hHW

end Erdos916
