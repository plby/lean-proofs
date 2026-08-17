import ErdosProblems.Erdos113.FourCycleSelection

open scoped SimpleGraph

namespace Erdos113SelectedLift

noncomputable section

open Erdos113Cycles Erdos113FourCycles Erdos113ManyLifts
  Erdos113Incidence Erdos113AnchoredLifts Erdos113AnchorConstruction
  Erdos113FourCycleSelection

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] {side : V → Bool}

namespace FirstSelection.SecondSelection

variable (S : FirstSelection G side) (R : S.SecondSelection)

/-- The lift system encoded by the two dyadic selections. -/
noncomputable def liftSystem
    (hcross : ∀ ⦃x y⦄, G.Adj x y → side y = !side x) :
    LiftSystem (S.auxiliaryGraph R.index) G :=
  selectedLiftSystem G side hcross S.anchor S.predicate
    S.predicate_symm (2 ^ R.index.val) (by positivity)

lemma middle_codegree_lt_scaleCap
    (hcross : ∀ ⦃x y⦄, G.Adj x y → side y = !side x)
    {y : V} (hy : IsMiddleVertex (liftSystem S R hcross) y) :
    codegree G S.anchor y < 2 ^ (S.scaleIndex.val + 1) := by
  rcases hy with ⟨a, b, hy⟩
  have hmem : y ∈ selectedMiddle G S.anchor S.predicate a b := by
    simpa [liftSystem, selectedLiftSystem] using hy
  have hp := (mem_selectedMiddle G S.anchor S.predicate).mp hmem
  exact (S.data hp.2.2.2).2.2.2.2.2.2.2.2

lemma linked_selected_data
    (hcross : ∀ ⦃x y⦄, G.Adj x y → side y = !side x)
    {t : NeighborVertex G S.anchor} {y : V}
    (hy : Linked (liftSystem S R hcross) t y) :
    G.Adj t.1 y ∧ y ≠ S.anchor ∧
      2 ^ S.scaleIndex.val ≤ codegree G S.anchor y := by
  rcases hy with ⟨b, hy⟩ | ⟨a, hy⟩
  · have hmem : y ∈ selectedMiddle G S.anchor S.predicate t b := by
      simpa [liftSystem, selectedLiftSystem] using hy
    have hm := (mem_selectedMiddle G S.anchor S.predicate).mp hmem
    have hd := S.data hm.2.2.2
    exact ⟨hm.1, hm.2.2.1, hd.2.2.2.2.2.2.2.1⟩
  · have hmem : y ∈ selectedMiddle G S.anchor S.predicate a t := by
      simpa [liftSystem, selectedLiftSystem] using hy
    have hm := (mem_selectedMiddle G S.anchor S.predicate).mp hmem
    have hp : S.predicate t.1 y a.1 :=
      (S.predicate_symm a.1 y t.1).mp hm.2.2.2
    have hd := S.data hp
    exact ⟨hm.2.1, hm.2.2.1, hd.2.2.2.2.2.2.2.1⟩

lemma leftPartners_subset_highCodegreeNeighbors
    (hcross : ∀ ⦃x y⦄, G.Adj x y → side y = !side x)
    (t : NeighborVertex G S.anchor) :
    leftPartners (liftSystem S R hcross) t ⊆
      highCodegreeNeighbors G (2 ^ S.scaleIndex.val - 1) S.anchor t.1 := by
  intro y hy
  have hd := linked_selected_data S R hcross
    ((mem_leftPartners (liftSystem S R hcross)).mp hy)
  rw [mem_highCodegreeNeighbors]
  exact ⟨hd.1, hd.2.1.symm, by
    have hpos : 0 < 2 ^ S.scaleIndex.val := by positivity
    omega⟩

theorem leftPartners_card_mul_threshold_le_extensions
    (hcross : ∀ ⦃x y⦄, G.Adj x y → side y = !side x)
    (t : NeighborVertex G S.anchor) :
    (leftPartners (liftSystem S R hcross) t).card *
        (2 ^ S.scaleIndex.val - 1) ≤
      (extensionsThroughEdge G S.anchor t.1).card := by
  calc
    (leftPartners (liftSystem S R hcross) t).card *
        (2 ^ S.scaleIndex.val - 1) ≤
      (highCodegreeNeighbors G (2 ^ S.scaleIndex.val - 1)
        S.anchor t.1).card * (2 ^ S.scaleIndex.val - 1) := by
      gcongr
      exact leftPartners_subset_highCodegreeNeighbors S R hcross t
    _ ≤ (extensionsThroughEdge G S.anchor t.1).card :=
      card_highCodegreeNeighbors_mul_le_extensionsThroughEdge G
        (2 ^ S.scaleIndex.val - 1)
        ((G.mem_neighborFinset S.anchor t.1).mp t.2 |>.symm)

theorem leftPartners_card_le_of_cycle_cap
    (hcross : ∀ ⦃x y⦄, G.Adj x y → side y = !side x)
    (Q : ℕ)
    (hcycle : ∀ t : NeighborVertex G S.anchor,
      (cyclesThroughEdge G 4 s(S.anchor, t.1)).card ≤ Q)
    (t : NeighborVertex G S.anchor) :
    (leftPartners (liftSystem S R hcross) t).card ≤
      Q / (2 ^ S.scaleIndex.val - 1) := by
  have hthreshold : 0 < 2 ^ S.scaleIndex.val - 1 := by
    have hne : S.scaleIndex.val ≠ 0 := Nat.ne_of_gt S.scaleIndex_pos
    have : 1 < 2 ^ S.scaleIndex.val := Nat.one_lt_two_pow hne
    omega
  rw [Nat.le_div_iff_mul_le hthreshold]
  exact (leftPartners_card_mul_threshold_le_extensions S R hcross t).trans
    ((card_extensionsThroughEdge_le_cyclesThroughEdge G S.anchor t.1
      ((G.mem_neighborFinset S.anchor t.1).mp t.2 |>.symm)).trans
        (hcycle t))

/-- Package the selected lift system with the two incidence caps. -/
noncomputable def anchoredLiftSystem
    (hcross : ∀ ⦃x y⦄, G.Adj x y → side y = !side x)
    (Q : ℕ)
    (hcycle : ∀ t : NeighborVertex G S.anchor,
      (cyclesThroughEdge G 4 s(S.anchor, t.1)).card ≤ Q) :
    AnchoredLiftSystem (S.auxiliaryGraph R.index) G :=
  selectedAnchoredLiftSystem G side hcross S.anchor S.predicate
    S.predicate_symm (2 ^ R.index.val) (by positivity)
    (Q / (2 ^ S.scaleIndex.val - 1))
    (2 ^ (S.scaleIndex.val + 1))
    (fun y hy ↦ (middle_codegree_lt_scaleCap S R hcross hy).le)
    (leftPartners_card_le_of_cycle_cap S R hcross Q hcycle)

end FirstSelection.SecondSelection

end

end Erdos113SelectedLift
