import ErdosProblems.Erdos1105.SharpCoreCount

namespace Erdos1105

open SimpleGraph Finset

/-- Sharp disintegration can be stopped at any prescribed order at least
the core order, without losing equality in the edge count. -/
theorem exists_sharp_core_subset {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) (S : Finset V) (m : ℕ)
    (hsub : vertexCore G d ⊆ S) (hm : (vertexCore G d).card ≤ m) (hSm : m ≤ S.card)
    (hsharp : (E767EGApi.edgesInside G S).card = (E767EGApi.edgesInside G (vertexCore G d)).card +
      d * (S.card - (vertexCore G d).card)) :
    ∃ T ⊆ S, vertexCore G d ⊆ T ∧ T.card = m ∧
      (E767EGApi.edgesInside G T).card = (E767EGApi.edgesInside G (vertexCore G d)).card +
        d * (m - (vertexCore G d).card) := by
  classical
  induction hcard : S.card using Nat.strong_induction_on generalizing S with
  | h n ih =>
    by_cases heq : S.card = m
    · exact ⟨S, Subset.rfl, hsub, heq, heq ▸ hsharp⟩
    · have hne : S ≠ vertexCore G d := by intro h; rw [h] at hSm heq; omega
      obtain ⟨v, hv, hvc, hdeg⟩ := exists_low_degree_outside_core G d hsub hne
      have hdeg' : degreeWithin G S v = d :=
        Nat.le_antisymm hdeg (degreeWithin_ge_of_sharp_core_count G d S hsub hsharp hv hvc)
      have hsub' : vertexCore G d ⊆ S.erase v := by
        intro w hw
        exact mem_erase.mpr ⟨fun h ↦ hvc (h ▸ hw), hsub hw⟩
      have hsharp' := sharp_core_count_erase G d S hsub hsharp hv hvc hdeg'
      have hpos := card_pos.mpr ⟨v, hv⟩
      have hlt : (S.erase v).card < n := by rw [card_erase_of_mem hv]; omega
      have hSm' : m ≤ (S.erase v).card := by rw [card_erase_of_mem hv]; omega
      obtain ⟨T, hTS, hTC, hTm, hTe⟩ := ih _ hlt (S.erase v) hsub' hSm' hsharp' rfl
      exact ⟨T, hTS.trans (erase_subset _ _), hTC, hTm, hTe⟩

end Erdos1105

#print axioms Erdos1105.exists_sharp_core_subset
