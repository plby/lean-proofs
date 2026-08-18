/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos570.TriangleHost

/-!
# Degree accounting at the minimum-degree vertices
-/

open scoped BigOperators SimpleGraph

noncomputable section

namespace Erdos570

open Erdos79

/-- The vertices having the same degree as a fixed minimum-degree vertex. -/
def minimumDegreeVertices {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : Finset V :=
  Finset.univ.filter fun x ↦ G.degree x = G.degree v

@[simp] theorem mem_minimumDegreeVertices
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v x : V) :
    x ∈ minimumDegreeVertices G v ↔ G.degree x = G.degree v := by
  simp [minimumDegreeVertices]

/-- Separating minimum-degree vertices from all other vertices in the
degree sum gives `(δ+1)|V| ≤ 2|E|+|S|`. -/
theorem minimumDegreeVertices_degree_sum
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (hv : G.degree v = G.minDegree) :
    (G.degree v + 1) * Fintype.card V ≤
      2 * G.edgeFinset.card + (minimumDegreeVertices G v).card := by
  let S := minimumDegreeVertices G v
  let δ := G.degree v
  have hpoint : ∀ x : V,
      δ + (if x ∈ S then 0 else 1) ≤ G.degree x := by
    intro x
    by_cases hx : x ∈ S
    · rw [if_pos hx]
      simpa [δ, S] using (mem_minimumDegreeVertices G v x).mp hx |>.symm.le
    · rw [if_neg hx]
      have hmin : δ ≤ G.degree x := by
        dsimp only [δ]
        rw [hv]
        exact G.minDegree_le_degree x
      have hne : G.degree x ≠ δ := by
        intro heq
        exact hx ((mem_minimumDegreeVertices G v x).mpr (by
          simpa [δ] using heq))
      omega
  have hsum : ∑ x : V, (δ + if x ∈ S then 0 else 1) ≤
      ∑ x : V, G.degree x :=
    Finset.sum_le_sum fun x _ ↦ hpoint x
  have hindicator : ∑ x : V, (if x ∈ S then 0 else 1) =
      Fintype.card V - S.card := by
    calc
      ∑ x : V, (if x ∈ S then 0 else 1) =
          ∑ x : V, (if x ∉ S then 1 else 0) := by
            apply Finset.sum_congr rfl
            intro x hx
            by_cases hxS : x ∈ S <;> simp [hxS]
      _ = ((Finset.univ : Finset V).filter fun x ↦ x ∉ S).card := by
            exact Finset.sum_boole (R := ℕ) (fun x : V ↦ x ∉ S) Finset.univ
      _ = ((Finset.univ : Finset V) \ S).card := by
            congr 1
            ext x
            simp
      _ = Fintype.card V - S.card := by
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ S)]
        simp
  rw [Finset.sum_add_distrib, hindicator,
    G.sum_degrees_eq_twice_card_edges] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul] at hsum
  have hScard : S.card ≤ Fintype.card V := by
    simpa using Finset.card_le_card (Finset.subset_univ S)
  have hident : (δ + 1) * Fintype.card V =
      Fintype.card V * δ + Fintype.card V := by ring
  rw [hident]
  dsimp only [δ, S] at hsum hScard ⊢
  omega

/-- If all minimum-degree vertices are independent, their incident edges
are disjoint when counted from that side. -/
theorem minimumDegreeVertices_independent_bound
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (hS : G.IsIndepSet (minimumDegreeVertices G v : Set V)) :
    G.degree v * (minimumDegreeVertices G v).card ≤ G.edgeFinset.card := by
  have hsum := sum_degrees_independent_le_card_edges G
    (minimumDegreeVertices G v) hS
  have heq : ∑ x ∈ minimumDegreeVertices G v, G.degree x =
      G.degree v * (minimumDegreeVertices G v).card := by
    calc
      _ = ∑ _x ∈ minimumDegreeVertices G v, G.degree v := by
        apply Finset.sum_congr rfl
        intro x hx
        exact (mem_minimumDegreeVertices G v x).mp hx
      _ = _ := by simp [mul_comm]
  rwa [heq] at hsum

end Erdos570
