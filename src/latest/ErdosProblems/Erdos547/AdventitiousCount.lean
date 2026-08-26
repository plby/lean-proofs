import ErdosProblems.Erdos547.FinePartitionSums

/-!
# At most one fewer two-attachment shrubs than seeds
-/

namespace Erdos547.FineTreePartition

open Finset SimpleGraph
open scoped BigOperators

variable {U : Type*} [Fintype U] [DecidableEq U] {T : SimpleGraph U}
  [DecidableRel T.Adj] {r : U} {ℓ : ℕ} {col : T.Coloring (Fin 2)}
variable (P : FineTreePartition T r ℓ col)

theorem cross_degrees_add_one_le (hT : T.IsTree) :
    (∑ S ∈ P.shrubs, ∑ v ∈ P.seeds, degreeIn T S v) + 1 ≤
      P.seeds.card + P.shrubs.card := by
  have hglobal : (∑ v, T.degree v) + 2 = 2 * Fintype.card U := by
    have he := hT.card_edgeFinset
    have hd := T.sum_degrees_eq_twice_card_edges
    omega
  have htrees : (∑ S ∈ P.shrubs, ∑ v ∈ S, degreeIn T S v) + 2 * P.shrubs.card =
      2 * (∑ S ∈ P.shrubs, S.card) := by
    calc
      _ = ∑ S ∈ P.shrubs, ((∑ v ∈ S, degreeIn T S v) + 2) := by
        simp [Finset.sum_add_distrib, Nat.mul_comm]
      _ = ∑ S ∈ P.shrubs, 2 * S.card := Finset.sum_congr rfl
        (fun S hS ↦ sum_degreeIn_tree T (P.shrub_tree S hS))
      _ = _ := (Finset.mul_sum _ _ _).symm
  have hpart := P.card_partition
  have hdeg := P.sum_degrees_partition
  omega

open scoped Classical in
theorem two_attachment_shrubs_add_one_le_seeds (hT : T.IsTree) :
    (P.shrubs.filter (fun S ↦ 2 ≤
      (P.seeds.filter (fun z ↦ 0 < degreeIn T S z)).card)).card + 1 ≤ P.seeds.card := by
  classical
  have hpoint (S : Finset U) (hS : S ∈ P.shrubs) :
      1 + (if 2 ≤ (P.seeds.filter (fun z ↦ 0 < degreeIn T S z)).card then 1 else 0) ≤
        ∑ z ∈ P.seeds, degreeIn T S z := by
    have hboundary : (P.seeds.filter (fun z ↦ 0 < degreeIn T S z)).card ≤
        ∑ z ∈ P.seeds, degreeIn T S z := by
      calc
        _ = ∑ z ∈ P.seeds, (if 0 < degreeIn T S z then 1 else 0 : ℕ) := by simp
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro z _
          split_ifs <;> omega
    obtain ⟨z, hz, hdz⟩ := P.has_attachment S hS
    have hpos : 0 < (P.seeds.filter (fun z ↦ 0 < degreeIn T S z)).card :=
      Finset.card_pos.mpr ⟨z, Finset.mem_filter.mpr ⟨hz, hdz⟩⟩
    split_ifs <;> omega
  have hsum := Finset.sum_le_sum hpoint
  simp only [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, Nat.mul_one,
    Finset.sum_boole, Nat.cast_id] at hsum
  have hcross := P.cross_degrees_add_one_le hT
  omega

end Erdos547.FineTreePartition

#print axioms Erdos547.FineTreePartition.two_attachment_shrubs_add_one_le_seeds
