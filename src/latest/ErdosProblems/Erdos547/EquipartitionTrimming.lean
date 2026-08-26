import ErdosProblems.Erdos547.RegularitySlicing

/-!
# Trimming equipartition parts to a common positive order
-/

namespace Erdos547

open Finset SimpleGraph
open scoped BigOperators

theorem exists_equal_cluster_trimming {V : Type*} [Fintype V] [DecidableEq V]
    (P : Finpartition (Finset.univ : Finset V)) (hP : P.IsEquipartition)
    (ht : 1 ≤ P.parts.card) (J : Finset (Finset V)) (hJ : J ⊆ P.parts) :
    ∃ m : ℕ, 1 ≤ m ∧ m * P.parts.card ≤ Fintype.card V ∧
      Fintype.card V ≤ (m + 1) * P.parts.card ∧
      ∃ C : ↥J → Finset V, (∀ i, C i ⊆ i.val ∧ (C i).card = m ∧ i.val.card ≤ (C i).card + 1) ∧
        Pairwise (fun i j ↦ Disjoint (C i) (C j)) := by
  classical
  let m := Fintype.card V / P.parts.card
  have htn : P.parts.card ≤ Fintype.card V := by simpa using P.card_parts_le_card
  have hm : 1 ≤ m := Nat.div_pos htn (by omega)
  have hlow (X : Finset V) (hX : X ∈ P.parts) : m ≤ X.card := by
    simpa only [Finset.card_univ] using hP.average_le_card_part hX
  have hhigh (X : Finset V) (hX : X ∈ P.parts) : X.card ≤ m + 1 := by
    simpa only [Finset.card_univ] using hP.card_part_le_average_add_one hX
  have hsum : (∑ X ∈ P.parts, X.card) = Fintype.card V := by simpa using P.sum_card_parts
  have hmn : m * P.parts.card ≤ Fintype.card V := by
    calc
      _ = ∑ _X ∈ P.parts, m := by simp [Nat.mul_comm]
      _ ≤ ∑ X ∈ P.parts, X.card := Finset.sum_le_sum hlow
      _ = _ := hsum
  have hnm : Fintype.card V ≤ (m + 1) * P.parts.card := by
    calc
      _ = ∑ X ∈ P.parts, X.card := hsum.symm
      _ ≤ ∑ _X ∈ P.parts, (m + 1) := Finset.sum_le_sum hhigh
      _ = _ := by simp [Nat.mul_comm]
  have hchoose (i : ↥J) : ∃ C ⊆ i.val, C.card = m :=
    Finset.exists_subset_card_eq (hlow i.val (hJ i.property))
  choose C hsub hcard using hchoose
  refine ⟨m, hm, hmn, hnm, C, ?_, ?_⟩
  · intro i
    exact ⟨hsub i, hcard i, (hcard i).symm ▸ hhigh i.val (hJ i.property)⟩
  · intro i j hij
    have hne : i.val ≠ j.val := fun he ↦ hij (Subtype.ext he)
    exact (P.disjoint (hJ i.property) (hJ j.property) hne).mono (hsub i) (hsub j)

end Erdos547

#print axioms Erdos547.exists_equal_cluster_trimming
