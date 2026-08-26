/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.RegularRowConcentration

/-! # One actual root with both upper and lower almost-all-target typicality -/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoTwoSidedRootSelection

open Finset SimpleGraph Erdos547EC2
open Erdos547b.ZhaoSourceRootIncidence Erdos547b.ZhaoRegularRowConcentration

variable {V I : Type*} [DecidableEq V] [DecidableEq I]

theorem exists_root_bothTypical_most
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (A pool : Finset V) (J : Finset I) (whole : I → Finset V)
    (ε δ : ℝ) (hδ : 0 < δ) (hεδ : ε ≤ δ ^ 2)
    (huniform : ∀ j ∈ J, H.IsUniform ε A (whole j))
    (hpool : pool ⊆ A) (hpoolCard : 2 * δ * A.card < pool.card) :
    ∃ z ∈ pool, ∃ DU ⊆ J, ∃ DL ⊆ J,
      (DU.card : ℝ) ≤ δ * J.card ∧ (DL.card : ℝ) ≤ δ * J.card ∧
      (∀ j ∈ J \ DU, (degreeInto H z (whole j) : ℝ) ≤
        ((H.edgeDensity A (whole j) : ℝ) + ε) * (whole j).card) ∧
      (∀ j ∈ J \ DL, ((H.edgeDensity A (whole j) : ℝ) - ε) * (whole j).card ≤
        (degreeInto H z (whole j) : ℝ)) := by
  let BU := upperBad H A J whole ε δ
  let BL := lowerBad H A J whole ε δ
  have hBU := card_upperBad_le H A J whole ε δ hδ hεδ huniform
  have hBL := card_lowerBad_le H A J whole ε δ hδ hεδ huniform
  have hUnion : ((BU ∪ BL).card : ℝ) ≤ 2 * δ * A.card := by
    have hu : ((BU ∪ BL).card : ℝ) ≤ (BU.card : ℝ) + BL.card := by
      exact_mod_cast Finset.card_union_le BU BL
    linarith only [hu, hBU, hBL]
  have hlt : (BU ∪ BL).card < pool.card := by exact_mod_cast hUnion.trans_lt hpoolCard
  obtain ⟨z, hz, hnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have hzU : z ∉ BU := fun h => hnot (Finset.mem_union_left _ h)
  have hzL : z ∉ BL := fun h => hnot (Finset.mem_union_right _ h)
  let DU := badTargets J (fun j => upperAtypicalVertices H ε A (whole j)) z
  let DL := badTargets J (fun j => lowerAtypicalVertices H ε A (whole j)) z
  refine ⟨z, hz, DU, Finset.filter_subset _ _, DL, Finset.filter_subset _ _, ?_, ?_, ?_, ?_⟩
  · exact le_of_not_gt (fun h => hzU (Finset.mem_filter.mpr ⟨hpool hz, h⟩))
  · exact le_of_not_gt (fun h => hzL (Finset.mem_filter.mpr ⟨hpool hz, h⟩))
  · intro j hj
    apply le_of_not_gt
    intro h
    exact (Finset.mem_sdiff.mp hj).2 (Finset.mem_filter.mpr
      ⟨(Finset.mem_sdiff.mp hj).1, Finset.mem_filter.mpr ⟨hpool hz, h⟩⟩)
  · intro j hj
    apply le_of_not_gt
    intro h
    exact (Finset.mem_sdiff.mp hj).2 (Finset.mem_filter.mpr
      ⟨(Finset.mem_sdiff.mp hj).1, Finset.mem_filter.mpr ⟨hpool hz, h⟩⟩)

end Erdos547b.ZhaoTwoSidedRootSelection

#print axioms Erdos547b.ZhaoTwoSidedRootSelection.exists_root_bothTypical_most
