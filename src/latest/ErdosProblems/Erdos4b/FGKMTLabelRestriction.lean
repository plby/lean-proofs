/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTFiniteEdgeFamily

/-! # Restricting a genuine finite edge family to a batch of labels -/

namespace Erdos4b.FGKMT.FiniteEdgeFamily

noncomputable section

open scoped BigOperators

variable {I Ω α : Type*} [Fintype I] [Fintype Ω] [DecidableEq α]

def restrictLabels (F : FiniteEdgeFamily I Ω α) (B : Finset I) :
    FiniteEdgeFamily B Ω α where
  vertices := F.vertices
  rank := F.rank
  edge := fun i => F.edge i.val
  mass := fun i => F.mass i.val
  mass_nonneg := fun i => F.mass_nonneg i.val
  mass_sum_one := fun i => F.mass_sum_one i.val
  edge_subset := fun i => F.edge_subset i.val
  edge_card_le := fun i => F.edge_card_le i.val

theorem restrictLabels_vertexMass (F : FiniteEdgeFamily I Ω α)
    (B : Finset I) (i : B) (v : α) :
    (F.restrictLabels B).vertexMass i v = F.vertexMass i.val v := rfl

theorem restrictLabels_pairMass (F : FiniteEdgeFamily I Ω α)
    (B : Finset I) (i : B) (v w : α) :
    (F.restrictLabels B).pairMass i v w = F.pairMass i.val v w := rfl

theorem restrictLabels_degree (F : FiniteEdgeFamily I Ω α) (B : Finset I) (v : α) :
    (F.restrictLabels B).degree v = ∑ i ∈ B, F.vertexMass i v := by
  exact Finset.sum_coe_sort B (fun i => F.vertexMass i v)

theorem restrictLabels_codegree (F : FiniteEdgeFamily I Ω α) (B : Finset I) (v w : α) :
    (F.restrictLabels B).codegree v w = ∑ i ∈ B, F.pairMass i v w := by
  exact Finset.sum_coe_sort B (fun i => F.pairMass i v w)

theorem restrictLabels_degree_le (F : FiniteEdgeFamily I Ω α) (B : Finset I) (v : α) :
    (F.restrictLabels B).degree v ≤ F.degree v := by
  rw [restrictLabels_degree, degree]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ B)
    (fun i _ _ => F.vertexMass_nonneg i v)

theorem restrictLabels_codegree_le (F : FiniteEdgeFamily I Ω α)
    (B : Finset I) (v w : α) :
    (F.restrictLabels B).codegree v w ≤ F.codegree v w := by
  rw [restrictLabels_codegree, codegree]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ B)
    (fun i _ _ => F.pairMass_nonneg i v w)

theorem restrictLabels_nonempty_of_degree_pos (F : FiniteEdgeFamily I Ω α)
    (B : Finset I) (v : α) (h : 0 < (F.restrictLabels B).degree v) : B.Nonempty := by
  rw [restrictLabels_degree] at h
  by_contra hnot
  have hB := Finset.not_nonempty_iff_eq_empty.mp hnot
  simp only [hB, Finset.sum_empty, lt_self_iff_false] at h

variable {J : Type*} [DecidableEq J]

def batchLabels (a : I → Option J) (j : J) : Finset I :=
  Finset.univ.filter fun i => a i = some j

theorem mem_batchLabels (a : I → Option J) (j : J) (i : I) :
    i ∈ batchLabels a j ↔ a i = some j := by
  simp only [batchLabels, Finset.mem_filter, Finset.mem_univ, true_and]

theorem batchLabels_disjoint (a : I → Option J) {j k : J} (hjk : j ≠ k) :
    Disjoint (batchLabels a j) (batchLabels a k) := by
  apply Finset.disjoint_left.mpr
  intro i hij hik
  exact hjk (Option.some.inj ((mem_batchLabels a j i).mp hij |>.symm.trans
    ((mem_batchLabels a k i).mp hik)))

theorem batchLabels_card_le (a : I → Option J) (j : J) :
    (batchLabels a j).card ≤ Fintype.card I := Finset.card_le_univ _

theorem batchLabels_degree (F : FiniteEdgeFamily I Ω α) (a : I → Option J) (j : J) (v : α) :
    (F.restrictLabels (batchLabels a j)).degree v =
      ∑ i, if a i = some j then F.vertexMass i v else 0 := by
  rw [restrictLabels_degree, batchLabels, Finset.sum_filter]

end

end Erdos4b.FGKMT.FiniteEdgeFamily
