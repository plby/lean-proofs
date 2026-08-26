import ErdosProblems.Erdos73.ParityPacking

/-! Bounded vertex congestion turns many parity-breaking paths into a disjoint packing. -/

namespace Erdos73
noncomputable section
open scoped Classical

open SimpleGraph Finset Erdos73Infrastructure.SimpleGraph
open scoped BigOperators

theorem card_le_mul_of_hits_with_congestion {I V : Type*} [DecidableEq I] [DecidableEq V]
    (s : Finset I) (R : I → Finset V) (X : Finset V) (r : ℕ)
    (hhit : ∀ i ∈ s, ∃ v ∈ R i, v ∈ X)
    (hcong : ∀ v ∈ X, (s.filter (fun i => v ∈ R i)).card ≤ r) : s.card ≤ X.card * r := by
  have hsub : s ⊆ X.biUnion (fun v => s.filter (fun i => v ∈ R i)) := by
    intro i hi
    obtain ⟨v, hvR, hvX⟩ := hhit i hi
    exact mem_biUnion.mpr ⟨v, hvX, mem_filter.mpr ⟨hi, hvR⟩⟩
  calc
    s.card ≤ (X.biUnion (fun v => s.filter (fun i => v ∈ R i))).card := card_le_card hsub
    _ ≤ ∑ v ∈ X, (s.filter (fun i => v ∈ R i)).card := card_biUnion_le
    _ ≤ ∑ v ∈ X, r := sum_le_sum hcong
    _ = X.card * r := by simp

theorem parityBreaking_packing_of_bounded_congestion
    {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) (c : V → Bool) (T : Finset V) (P : I → GraphPath G)
    (hP : ∀ i, IsParityBreakingPath c T (P i)) (k r : ℕ)
    (hsize : r * (2 * k - 2) < Fintype.card I)
    (hcong : ∀ v, (Finset.univ.filter (fun i => v ∈ (P i).vertexSet)).card ≤ r) :
    HasParityBreakingPathPacking G c T k := by
  rcases parityBreaking_paths_packing_or_covering G c T k with hp | ⟨X, hXcard, hX⟩
  · exact hp
  · have hhits : ∀ i ∈ (Finset.univ : Finset I), ∃ v ∈ (P i).vertexSet, v ∈ X := by
      intro i _
      exact Finset.not_disjoint_iff.mp (hX (P i) (hP i))
    have hbound := card_le_mul_of_hits_with_congestion Finset.univ
      (fun i => (P i).vertexSet) X r hhits (fun v _ => hcong v)
    rw [card_univ] at hbound
    have hmul := Nat.mul_le_mul_right r hXcard
    rw [Nat.mul_comm (2 * k - 2) r] at hmul
    omega

end
end Erdos73
