import ErdosProblems.Erdos19.ColorIncidence

/-! # Counting covered vertices across all color classes -/

namespace Erdos19

open Finset

attribute [local instance] Classical.propDecidable

theorem ncard_eq_sum_indicator {V : Type*} [Fintype V] (S : Set V) :
    S.ncard = ∑ v : V, if v ∈ S then 1 else 0 := by
  classical
  rw [← Set.fintypeCard_eq_ncard S]
  simp [Fintype.card_subtype]

namespace SetHypergraph

variable {V I : Type*} [Fintype V] [Fintype I]

theorem sum_colorCovered_ncard (H : SetHypergraph V) (c : H.EdgeColoring I) :
    (∑ i : I, (H.colorCovered c i).ncard) = ∑ e : H, e.1.ncard := by
  classical
  calc
    (∑ i : I, (H.colorCovered c i).ncard) =
        ∑ i : I, ∑ v : V, if v ∈ H.colorCovered c i then 1 else 0 := by
      exact sum_congr rfl (fun i _ ↦ ncard_eq_sum_indicator _)
    _ = ∑ v : V, ∑ i : I, if v ∈ H.colorCovered c i then 1 else 0 := sum_comm
    _ = ∑ v : V, (H.incidentEdges v).ncard := by simp only [colorCovered_count]
    _ = ∑ v : V, ∑ e : H, if v ∈ e.1 then 1 else 0 := by
      apply sum_congr rfl
      intro v _
      exact ncard_eq_sum_indicator (H.incidentEdges v)
    _ = ∑ e : H, ∑ v : V, if v ∈ e.1 then 1 else 0 := sum_comm
    _ = ∑ e : H, e.1.ncard := by
      exact sum_congr rfl (fun e _ ↦ (ncard_eq_sum_indicator _).symm)

theorem colorCovered_eq_coveredVertices (H : SetHypergraph V) (c : H.EdgeColoring I) (i : I) :
    H.colorCovered c i = H.coveredVertices {e | c.color e = i} := by
  ext v
  simp [colorCovered, coveredVertices]

theorem large_colorClasses_mul_le_total_incidence (H : SetHypergraph V)
    (c : H.EdgeColoring I) (A : ℕ) :
    ({i : I | A < (H.coveredVertices {e | c.color e = i}).ncard} : Set I).ncard * (A + 1) ≤
      ∑ e : H, e.1.ncard := by
  classical
  let B := (univ : Finset I).filter fun i ↦ A < (H.colorCovered c i).ncard
  have hcard : B.card =
      ({i : I | A < (H.coveredVertices {e | c.color e = i}).ncard} : Set I).ncard := by
    rw [ncard_eq_sum_indicator]
    simp only [sum_boole, Set.mem_setOf_eq, ← colorCovered_eq_coveredVertices]
    rfl
  rw [← hcard, ← H.sum_colorCovered_ncard c]
  calc
    B.card * (A + 1) = ∑ _i ∈ B, (A + 1) := by simp
    _ ≤ ∑ i ∈ B, (H.colorCovered c i).ncard := by
      apply sum_le_sum
      intro i hi
      exact (mem_filter.mp hi).2
    _ ≤ ∑ i : I, (H.colorCovered c i).ncard := sum_le_sum_of_subset (subset_univ _)

theorem coveredVertices_ncard_le_of_singleton_class (H : SetHypergraph V) (S : Set H) (A : ℕ)
    (hS : S.ncard ≤ 1) (hedge : ∀ e : H, e.1.ncard ≤ A) :
    (H.coveredVertices S).ncard ≤ A := by
  by_cases hnonempty : S.Nonempty
  · obtain ⟨e, he⟩ := hnonempty
    have hs : H.coveredVertices S ⊆ e.1 := by
      intro v hv
      obtain ⟨f, hf⟩ := Set.mem_iUnion.mp hv
      obtain ⟨hfS, hvf⟩ := Set.mem_iUnion.mp hf
      have hfe := (Set.ncard_le_one_iff_subsingleton.mp hS) hfS he
      exact hfe ▸ hvf
    exact (Set.ncard_le_ncard hs).trans (hedge e)
  · have hSempty := Set.not_nonempty_iff_eq_empty.mp hnonempty
    simp [hSempty, coveredVertices]

#print axioms large_colorClasses_mul_le_total_incidence

end SetHypergraph
end Erdos19
