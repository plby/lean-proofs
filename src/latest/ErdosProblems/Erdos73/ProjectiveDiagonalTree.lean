import ErdosProblems.Erdos73.ProjectiveDiagonalConnectivity

/-! The chosen projective diagonals form a spanning tree, with one face per edge. -/

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
open SimpleGraph

theorem card_projectiveFace_add_one {n : ℕ} (hn : 2 ≤ n) :
    Fintype.card (ProjectiveFace n) + 1 = n * n := by
  simp only [ProjectiveFace, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  have hh : n - 1 + 1 = n := by omega
  calc
    n * (n - 1) + (n - 1) + 1 = n * (n - 1) + n := by omega
    _ = n * ((n - 1) + 1) := by rw [Nat.mul_add, Nat.mul_one]
    _ = n * n := by rw [hh]

def projectiveDiagonalEdge {n : ℕ} (hn : 2 ≤ n) (f : ProjectiveFace n) :
    (projectiveDiagonalGraph hn).edgeSet :=
  ⟨s((projectiveDiagonalEnds hn f).1, (projectiveDiagonalEnds hn f).2),
    projectiveDiagonal_adj hn f⟩

theorem projectiveDiagonalEdge_surjective {n : ℕ} (hn : 2 ≤ n) :
    Function.Surjective (projectiveDiagonalEdge hn) := by
  intro e
  have he := e.property
  change e.val ∈ (fromEdgeSet (Set.range fun f : ProjectiveFace n =>
    s((projectiveDiagonalEnds hn f).1, (projectiveDiagonalEnds hn f).2))).edgeSet at he
  rw [edgeSet_fromEdgeSet] at he
  obtain ⟨f, hf⟩ := he.1
  exact ⟨f, Subtype.ext hf⟩

theorem projectiveDiagonal_isTree {n : ℕ} (hn : 2 ≤ n) (hnEven : n % 2 = 0) :
    (projectiveDiagonalGraph hn).IsTree := by
  have hconn := projectiveDiagonal_connected hn hnEven
  have hlo := hconn.card_vert_le_card_edgeSet_add_one
  have hhi := Fintype.card_le_of_surjective _ (projectiveDiagonalEdge_surjective hn)
  have hfaces := card_projectiveFace_add_one hn
  apply isTree_iff_connected_and_card.mpr
  refine ⟨hconn, ?_⟩
  simp only [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fin] at hlo ⊢
  omega

theorem projectiveDiagonalEdge_bijective {n : ℕ} (hn : 2 ≤ n) (hnEven : n % 2 = 0) :
    Function.Bijective (projectiveDiagonalEdge hn) := by
  have hT := projectiveDiagonal_isTree hn hnEven
  have he := (isTree_iff_connected_and_card.mp hT).2
  have hf := card_projectiveFace_add_one hn
  have hcard : Fintype.card (ProjectiveFace n) =
      Fintype.card (projectiveDiagonalGraph hn).edgeSet := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fin] at he
    omega
  exact (Fintype.bijective_iff_surjective_and_card _).mpr
    ⟨projectiveDiagonalEdge_surjective hn, hcard⟩

end
end Erdos73
