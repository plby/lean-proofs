import ErdosProblems.Erdos547.ShrubPartSizes
import ErdosProblems.Erdos547.WeightedBinAllocation

/-!
# Simultaneous allocation of the two colour classes of each shrub
-/

namespace Erdos547.FineTreePartition

open Finset SimpleGraph
open scoped BigOperators

variable {U I : Type*} [Fintype U] [DecidableEq U] [Fintype I] [Nonempty I] [DecidableEq I]
  {T : SimpleGraph U} [DecidableRel T.Adj] {r : U} {ℓ : ℕ}
  {col : T.Coloring (Fin 2)}

open scoped Classical in
theorem exists_shrub_allocation (P : FineTreePartition T r ℓ col) (c : Fin 2)
    (allowed : ↥(P.shrubsOfColour c) → Finset I) (w : I → ℝ) (A C : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hA : 0 < A) (hC : 0 ≤ C)
    (hallowed : ∀ S, A ≤ ∑ i ∈ allowed S, w i)
    (hsmall : (ℓ : ℝ) * ((P.nearVertices c).card + (P.farVertices c).card) < C ^ 2) :
    ∃ f : ↥(P.shrubsOfColour c) → I, (∀ S, f S ∈ allowed S) ∧
      ∀ i,
        (∑ S ∈ (Finset.univ : Finset ↥(P.shrubsOfColour c)).filter (fun S ↦ f S = i),
          ((S.val.filter (fun v ↦ col v ≠ c)).card : ℝ)) <
            w i / A * (P.nearVertices c).card + C ∧
        (∑ S ∈ (Finset.univ : Finset ↥(P.shrubsOfColour c)).filter (fun S ↦ f S = i),
          ((S.val.filter (fun v ↦ col v = c)).card : ℝ)) <
            w i / A * (P.farVertices c).card + C := by
  classical
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  let u : ↥(P.shrubsOfColour c) → Fin 2 → ℝ := fun S j ↦
    if j = 0 then ((S.val.filter (fun v ↦ col v ≠ c)).card : ℝ)
      else ((S.val.filter (fun v ↦ col v = c)).card : ℝ)
  have hu (S : ↥(P.shrubsOfColour c)) (j : Fin 2) : 0 ≤ u S j ∧ u S j ≤ ℓ := by
    have hs : S.val.card ≤ ℓ := P.shrub_size S.val (Finset.mem_filter.mp S.property).1
    dsimp [u]
    split_ifs
    · exact ⟨Nat.cast_nonneg _, by exact_mod_cast (Finset.card_filter_le _ _).trans hs⟩
    · exact ⟨Nat.cast_nonneg _, by exact_mod_cast (Finset.card_filter_le _ _).trans hs⟩
  have hsum₀ : (∑ S : ↥(P.shrubsOfColour c), u S 0) = (P.nearVertices c).card := by
    simp only [u, if_pos rfl]
    exact_mod_cast P.sum_near_shrub_sizes c
  have hsum₁ : (∑ S : ↥(P.shrubsOfColour c), u S 1) = (P.farVertices c).card := by
    simp only [u, if_neg h10]
    exact_mod_cast P.sum_far_shrub_sizes c
  have htotal : (∑ S : ↥(P.shrubsOfColour c), ∑ j : Fin 2, u S j) =
      (P.nearVertices c).card + (P.farVertices c).card := by
    rw [Finset.sum_comm, Fin.sum_univ_two, hsum₀, hsum₁]
  obtain ⟨f, hf, hload⟩ := exists_weighted_bin_assignment allowed w u A ℓ C hw hA hC
    hallowed hu (by rwa [htotal])
  refine ⟨f, hf, ?_⟩
  intro i
  have hzero := hload i 0
  have hone := hload i 1
  rw [hsum₀] at hzero
  rw [hsum₁] at hone
  exact ⟨by simpa only [u, if_pos rfl] using hzero,
    by simpa only [u, if_neg h10] using hone⟩

end Erdos547.FineTreePartition

#print axioms Erdos547.FineTreePartition.exists_shrub_allocation
