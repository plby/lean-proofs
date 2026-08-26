/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim68
import ErdosProblems.Erdos547b.EC2

/-! # Hall assignment into two disjoint, independently budgeted pools -/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoTwoPoolAssignment

open Finset Fintype SimpleGraph Erdos547EC2

variable {I B : Type*} [Fintype I] [DecidableEq I] [Fintype B] [DecidableEq B]

omit [Fintype B] in
theorem exists_injective_twoPools
    (High : Finset I) (choices : I → Finset B) (P Q : Finset B) (hPQ : Disjoint P Q)
    (hhighSub : ∀ i ∈ High, choices i ⊆ P) (hlowSub : ∀ i ∉ High, choices i ⊆ Q)
    (hhighCard : ∀ i ∈ High, High.card ≤ (choices i).card)
    (hlowCard : ∀ i ∉ High, Fintype.card I - High.card ≤ (choices i).card) :
    ∃ g : I → B, Function.Injective g ∧ ∀ i, g i ∈ choices i := by
  apply (Finset.all_card_le_biUnion_card_iff_exists_injective choices).mp
  intro s
  by_cases hs : s = ∅
  · simp [hs]
  by_cases hsub : s ⊆ High
  · obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hs
    exact (Finset.card_le_card hsub).trans ((hhighCard i (hsub hi)).trans
      (Finset.card_le_card (Finset.subset_biUnion_of_mem choices hi)))
  obtain ⟨j, hj, hjLow⟩ := Finset.not_subset.mp hsub
  by_cases hsome : ∃ i ∈ s, i ∈ High
  · obtain ⟨i, hi, hiHigh⟩ := hsome
    have hdis := hPQ.mono (hhighSub i hiHigh) (hlowSub j hjLow)
    have hsubChoices : choices i ∪ choices j ⊆ s.biUnion choices :=
      Finset.union_subset (Finset.subset_biUnion_of_mem choices hi) (Finset.subset_biUnion_of_mem choices hj)
    have hu := Finset.card_le_card hsubChoices
    rw [Finset.card_union_of_disjoint hdis] at hu
    have hsCard := Finset.card_le_univ s
    have hHCard := Finset.card_le_univ High
    have hc1 := hhighCard i hiHigh
    have hc2 := hlowCard j hjLow
    omega
  · have hsubLow : s ⊆ Finset.univ \ High := by
      intro i hi
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h => hsome ⟨i, hi, h⟩⟩
    have hcard : s.card ≤ Fintype.card I - High.card := by
      simpa only [Finset.card_sdiff_of_subset (Finset.subset_univ High), Finset.card_univ] using
        Finset.card_le_card hsubLow
    exact hcard.trans ((hlowCard j hjLow).trans
      (Finset.card_le_card (Finset.subset_biUnion_of_mem choices hj)))

omit [Fintype B] in
theorem exists_adjacent_twoPools
    (G : SimpleGraph B) [DecidableRel G.Adj] (parent : I → B)
    (High : Finset I) (P Q : Finset B) (hPQ : Disjoint P Q)
    (hhigh : ∀ i ∈ High, High.card ≤ degreeInto G (parent i) P)
    (hlow : ∀ i ∉ High, Fintype.card I - High.card ≤ degreeInto G (parent i) Q) :
    ∃ g : I → B, Function.Injective g ∧ (∀ i, G.Adj (parent i) (g i)) ∧
      (∀ i ∈ High, g i ∈ P) ∧ (∀ i ∉ High, g i ∈ Q) := by
  classical
  let choices := fun i => if i ∈ High then P.filter (G.Adj (parent i)) else Q.filter (G.Adj (parent i))
  obtain ⟨g, hinj, hmem⟩ := exists_injective_twoPools High choices P Q hPQ
    (fun i hi => by simpa only [choices, if_pos hi] using Finset.filter_subset (G.Adj (parent i)) P)
    (fun i hi => by simpa only [choices, if_neg hi] using Finset.filter_subset (G.Adj (parent i)) Q)
    (fun i hi => by simpa only [choices, if_pos hi, degreeInto] using hhigh i hi)
    (fun i hi => by simpa only [choices, if_neg hi, degreeInto] using hlow i hi)
  refine ⟨g, hinj, ?_, ?_, ?_⟩
  · intro i
    have h := hmem i
    by_cases hi : i ∈ High
    · exact (Finset.mem_filter.mp (show g i ∈ P.filter (G.Adj (parent i)) from by simpa only [choices, if_pos hi] using h)).2
    · exact (Finset.mem_filter.mp (show g i ∈ Q.filter (G.Adj (parent i)) from by simpa only [choices, if_neg hi] using h)).2
  · intro i hi
    exact (Finset.mem_filter.mp (show g i ∈ P.filter (G.Adj (parent i)) from by simpa only [choices, if_pos hi] using hmem i)).1
  · intro i hi
    exact (Finset.mem_filter.mp (show g i ∈ Q.filter (G.Adj (parent i)) from by simpa only [choices, if_neg hi] using hmem i)).1

end Erdos547b.ZhaoTwoPoolAssignment

#print axioms Erdos547b.ZhaoTwoPoolAssignment.exists_injective_twoPools
#print axioms Erdos547b.ZhaoTwoPoolAssignment.exists_adjacent_twoPools
