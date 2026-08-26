import ErdosProblems.Erdos19.ExceptionalColorTrace

/-! # Choosing the one exceptional color in a special palette -/

namespace Erdos19.SetHypergraph

variable {V C : Type*} [Fintype V]

theorem buffer_lower_of_small_trace (Y T : Set V) (d : ℕ)
    (hY : 2 * d + 1 ≤ Y.ncard) (htrace : 2 * (Y ∩ T).ncard ≤ Y.ncard + 1) :
    d ≤ (Y \ T).ncard := by
  have hcount := Set.ncard_inter_add_ncard_sdiff_eq_ncard Y T
  omega

theorem exists_exceptional_color_with_buffer (J : SetHypergraph V) (hlinear : J.IsLinear)
    (color : J → C) (A : ℕ) (hbounded : J.IsCoverBoundedColoring color A)
    (Y : Set V) (hA : 2 * A ≤ Y.ncard + 1) (S : Finset C) (hS : S.Nonempty)
    (d : ℕ) (hY : 2 * (d + S.card) + 1 ≤ Y.ncard) :
    ∃ bad ∈ S, ∀ a ∈ S, a ≠ bad →
      d + S.card ≤ (Y \ J.coveredVertices {e | color e = a}).ncard := by
  classical
  let exceptional : Set C := {a | Y.ncard + 1 <
    2 * (Y ∩ J.coveredVertices {e | color e = a}).ncard}
  have hsingleton : exceptional.Subsingleton :=
    J.large_trace_colors_subsingleton hlinear color A hbounded Y hA
  by_cases hex : ∃ a ∈ S, a ∈ exceptional
  · obtain ⟨bad, hbadS, hbad⟩ := hex
    refine ⟨bad, hbadS, ?_⟩
    intro a _ hne
    have hnot : a ∉ exceptional := fun h ↦ hne (hsingleton h hbad)
    have htrace : 2 * (Y ∩ J.coveredVertices {e | color e = a}).ncard ≤ Y.ncard + 1 :=
      Nat.le_of_not_gt hnot
    exact buffer_lower_of_small_trace Y _ (d + S.card) hY htrace
  · obtain ⟨bad, hbad⟩ := hS
    refine ⟨bad, hbad, ?_⟩
    intro a ha _
    have hnot : a ∉ exceptional := fun h ↦ hex ⟨a, ha, h⟩
    have htrace : 2 * (Y ∩ J.coveredVertices {e | color e = a}).ncard ≤ Y.ncard + 1 :=
      Nat.le_of_not_gt hnot
    exact buffer_lower_of_small_trace Y _ (d + S.card) hY htrace

#print axioms exists_exceptional_color_with_buffer

end Erdos19.SetHypergraph
