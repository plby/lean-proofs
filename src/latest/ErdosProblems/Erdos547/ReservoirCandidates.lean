import ErdosProblems.Erdos547.RegularityTypical

/-!
# Choosing distinguished roots from reservoir neighbours
-/

namespace Erdos547

open Finset SimpleGraph

variable {V : Type*} [DecidableEq V]

theorem candidate_card_after_used (Q candidate used : Finset V) (hsub : candidate ⊆ Q) :
    candidate.card ≤ (candidate \ used).card + (Q ∩ used).card := by
  have hh := Finset.card_sdiff_add_card_inter candidate used
  have hs : candidate ∩ used ⊆ Q ∩ used := Finset.inter_subset_inter_right hsub
  have hc := Finset.card_le_card hs
  omega

theorem secondary_reservoir_pool (Q candidate used A : Finset V) (v : V) (b : ℝ)
    (hsub : candidate ⊆ Q) (hQA : Disjoint Q A)
    (hroom : b + ((Q ∩ used).card : ℝ) + 1 ≤ candidate.card) :
    ∃ R : Finset V, R ⊆ candidate ∧ Disjoint R used ∧ Disjoint R A ∧
      v ∉ R ∧ b ≤ R.card := by
  let R := (candidate \ used).erase v
  have hRsub : R ⊆ candidate := (Finset.erase_subset _ _).trans Finset.sdiff_subset
  have hused : Disjoint R used := by
    apply Finset.disjoint_left.mpr
    intro u hu huused
    exact (Finset.mem_sdiff.mp (Finset.mem_of_mem_erase hu)).2 huused
  have hRA : Disjoint R A := hQA.mono_left (hRsub.trans hsub)
  have hc := candidate_card_after_used Q candidate used hsub
  have herase : (candidate \ used).card ≤ R.card + 1 := by
    change (candidate \ used).card ≤ ((candidate \ used).erase v).card + 1
    by_cases hv : v ∈ candidate \ used
    · have he := Finset.card_erase_add_one hv
      omega
    · simp only [Finset.erase_eq_of_notMem hv]
      omega
  have hcast : (candidate.card : ℝ) ≤ (R.card : ℝ) + ((Q ∩ used).card : ℝ) + 1 := by
    exact_mod_cast (show candidate.card ≤ R.card + (Q ∩ used).card + 1 by omega)
  exact ⟨R, hRsub, hused, hRA, Finset.notMem_erase _ _, by linarith only [hroom, hcast]⟩

theorem exists_typical_unused_reservoir_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    {X Y B Q candidate used : Finset V} {ε b : ℝ}
    (hreg : G.IsUniform ε X Y) (hB : B ⊆ Y) (hBsize : (Y.card : ℝ) * ε ≤ B.card)
    (hQ : Q ⊆ X) (hsub : candidate ⊆ Q)
    (hroom : (X.card : ℝ) * ε + (Q ∩ used).card < candidate.card)
    (hdegree : b ≤ ((G.edgeDensity X Y : ℝ) - ε) * B.card) :
    ∃ v ∈ candidate, v ∉ used ∧ b ≤ (degreeIn G B v : ℝ) := by
  have hc := candidate_card_after_used Q candidate used hsub
  have hcast : (candidate.card : ℝ) ≤ ((candidate \ used).card : ℝ) + (Q ∩ used).card := by
    exact_mod_cast hc
  have hlarge : (X.card : ℝ) * ε < (candidate \ used).card := by
    linarith only [hroom, hcast]
  obtain ⟨v, hv, hd⟩ := exists_typical_in_large_subset G hreg hB hBsize
    (Finset.sdiff_subset.trans (hsub.trans hQ)) hlarge
  obtain ⟨hvc, hvused⟩ := Finset.mem_sdiff.mp hv
  exact ⟨v, hvc, hvused, hdegree.trans hd⟩

end Erdos547

#print axioms Erdos547.secondary_reservoir_pool
#print axioms Erdos547.exists_typical_unused_reservoir_vertex
