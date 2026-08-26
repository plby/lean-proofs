import ErdosProblems.Erdos547.HullSeeds
import ErdosProblems.Erdos547.FiniteTreeBoundary

/-!
# Expanding one colour of a hull cut set
-/

namespace Erdos547

open Finset SimpleGraph
open scoped BigOperators

variable {U : Type*} (T : SimpleGraph U) [DecidableRel T.Adj]

theorem sum_degreeIn_hull_seeds [DecidableEq U] {S H : Finset U}
    (hH : (T.induce (H : Set U)).IsTree) (hSH : S ⊆ H)
    (hdeg : ∀ u ∈ H, u ∉ S → degreeIn T H u = 2) :
    (∑ u ∈ S, degreeIn T H u) + 2 = 2 * S.card := by
  classical
  have hdis : Disjoint S (H \ S) := by
    apply Finset.disjoint_left.mpr
    intro v hv hh
    exact (Finset.mem_sdiff.mp hh).2 hv
  have hsum : (∑ u ∈ S, degreeIn T H u) + (∑ u ∈ H \ S, degreeIn T H u) =
      ∑ u ∈ H, degreeIn T H u := by
    rw [← Finset.sum_union hdis, Finset.union_sdiff_of_subset hSH]
  have hrest : (∑ u ∈ H \ S, degreeIn T H u) = 2 * (H \ S).card := by
    calc
      _ = ∑ _u ∈ H \ S, 2 := Finset.sum_congr rfl (fun u hu ↦
        hdeg u (Finset.mem_sdiff.mp hu).1 (Finset.mem_sdiff.mp hu).2)
      _ = _ := by simp [Nat.mul_comm]
  have hcard : S.card + (H \ S).card = H.card := by
    rw [← Finset.card_union_of_disjoint hdis, Finset.union_sdiff_of_subset hSH]
  have htree := sum_degreeIn_tree T hH
  omega

open scoped Classical in
theorem exists_one_colour_closed_seed_extension {S H : Finset U}
    (hH : (T.induce (H : Set U)).IsTree) (hSH : S ⊆ H)
    (hdeg : ∀ u ∈ H, u ∉ S → degreeIn T H u = 2) (col : T.Coloring (Fin 2)) :
    ∃ Z : Finset U, S ⊆ Z ∧ Z ⊆ H ∧ Z.card ≤ 3 * S.card ∧
      (∀ u ∈ H, u ∉ Z → degreeIn T H u = 2) ∧
      ∀ u ∈ Z, col u = 1 → ∀ v ∈ H, T.Adj u v → v ∈ Z := by
  classical
  let B := S.filter (fun u ↦ col u = 1)
  let N := H.filter (fun v ↦ 0 < degreeIn T B v)
  have hNcard : N.card ≤ 2 * S.card := by
    have hcount : N.card ≤ ∑ v ∈ H, degreeIn T B v := by
      calc
        _ = ∑ v ∈ H, (if 0 < degreeIn T B v then 1 else 0 : ℕ) := by simp [N]
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro v _
          split_ifs <;> omega
    rw [sum_degreeIn_comm] at hcount
    have hle : (∑ u ∈ B, degreeIn T H u) ≤ ∑ u ∈ S, degreeIn T H u :=
      Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    have hsum := sum_degreeIn_hull_seeds T hH hSH hdeg
    omega
  let Z := S ∪ N
  have hSZ : S ⊆ Z := Finset.subset_union_left
  have hZH : Z ⊆ H := Finset.union_subset hSH (Finset.filter_subset _ _)
  refine ⟨Z, hSZ, hZH, ?_, ?_, ?_⟩
  · have hh := Finset.card_union_le S N
    change Z.card ≤ S.card + N.card at hh
    omega
  · intro u hu hn
    exact hdeg u hu (fun hs ↦ hn (hSZ hs))
  · intro u hu hcol v hv huv
    have huS : u ∈ S := by
      rcases Finset.mem_union.mp hu with hs | hn
      · exact hs
      · obtain ⟨b, hb⟩ := Finset.card_pos.mp (Finset.mem_filter.mp hn).2
        obtain ⟨hbB, hub⟩ := Finset.mem_filter.mp hb
        have hbcol := (Finset.mem_filter.mp hbB).2
        exact ((col.valid hub) (hcol.trans hbcol.symm)).elim
    apply Finset.mem_union.mpr
    right
    apply Finset.mem_filter.mpr
    refine ⟨hv, Finset.card_pos.mpr ⟨u, ?_⟩⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨huS, hcol⟩, huv.symm⟩

end Erdos547

#print axioms Erdos547.exists_one_colour_closed_seed_extension
