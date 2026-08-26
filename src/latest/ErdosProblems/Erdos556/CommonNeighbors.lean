import ErdosProblems.Erdos556.Basic

/-!
# Large intersections in finite set families

A union estimate with a quadratic overlap error supplies the common
neighbors needed for path shortening. No probabilistic input is used.
-/

namespace Erdos556

open Finset

theorem sum_card_le_card_biUnion_add_sq_mul {I V : Type*} [DecidableEq I] [DecidableEq V]
    (A : Finset I) (S : I → Finset V) (m : ℕ)
    (hinter : ∀ i ∈ A, ∀ j ∈ A, i ≠ j → (S i ∩ S j).card ≤ m) :
    (∑ i ∈ A, (S i).card) ≤ (A.biUnion S).card + A.card ^ 2 * m := by
  induction A using Finset.induction_on with
  | empty => simp
  | @insert i A hi ih =>
      have hpair : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → (S a ∩ S b).card ≤ m := by
        intro a ha b hb hab
        exact hinter a (mem_insert_of_mem ha) b (mem_insert_of_mem hb) hab
      have hrec := ih hpair
      have hcross : (S i ∩ A.biUnion S).card ≤ A.card * m := by
        have hsub : S i ∩ A.biUnion S ⊆ A.biUnion (fun j => S i ∩ S j) := by
          intro x hx
          obtain ⟨hxi, hxA⟩ := mem_inter.mp hx
          obtain ⟨j, hj, hxj⟩ := mem_biUnion.mp hxA
          exact mem_biUnion.mpr ⟨j, hj, mem_inter.mpr ⟨hxi, hxj⟩⟩
        calc
          (S i ∩ A.biUnion S).card ≤ (A.biUnion (fun j => S i ∩ S j)).card := card_le_card hsub
          _ ≤ ∑ j ∈ A, (S i ∩ S j).card := card_biUnion_le
          _ ≤ ∑ _j ∈ A, m := by
            apply sum_le_sum
            intro j hj
            exact hinter i (mem_insert_self _ _) j (mem_insert_of_mem hj)
              (fun h => hi (h.symm ▸ hj))
          _ = A.card * m := by simp
      have hunion := card_union_add_card_inter (S i) (A.biUnion S)
      rw [sum_insert hi, biUnion_insert, card_insert_of_notMem hi]
      calc
        (S i).card + ∑ j ∈ A, (S j).card ≤
            (S i).card + (A.biUnion S).card + A.card ^ 2 * m := by omega
        _ = (S i ∪ A.biUnion S).card + (S i ∩ A.biUnion S).card + A.card ^ 2 * m := by omega
        _ ≤ (S i ∪ A.biUnion S).card + A.card * m + A.card ^ 2 * m := by omega
        _ ≤ (S i ∪ A.biUnion S).card + (A.card + 1) ^ 2 * m := by
          nlinarith [Nat.zero_le (A.card * m)]

theorem exists_large_intersection {I V : Type*} [Fintype I] [Fintype V]
    [DecidableEq I] [DecidableEq V] (S : I → Finset V) (d m : ℕ)
    (hsize : ∀ i, d ≤ (S i).card)
    (hcount : Fintype.card V + (Fintype.card I) ^ 2 * m < Fintype.card I * d) :
    ∃ i j : I, i ≠ j ∧ m < (S i ∩ S j).card := by
  by_contra! h
  have hsum : Fintype.card I * d ≤ ∑ i, (S i).card := by
    calc
      Fintype.card I * d = ∑ _i : I, d := by simp
      _ ≤ ∑ i, (S i).card := sum_le_sum fun i _ => hsize i
  have hbound := sum_card_le_card_biUnion_add_sq_mul univ S m
    (fun i _ j _ hij => h i j hij)
  rw [card_univ] at hbound
  have hcard := card_le_univ (univ.biUnion S)
  omega

#print axioms exists_large_intersection

theorem exists_large_common_neighbors_avoiding {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D d : ℕ)
    (hN : 0 < Fintype.card V) (hscale : Fintype.card V ≤ D * d)
    (hdegree : ∀ v, d ≤ G.degree v) (S : Finset V) (hS : 2 * S.card ≤ d)
    (a : Fin (4 * D) → V) :
    ∃ i j : Fin (4 * D), i ≠ j ∧
      Fintype.card V / (2 * (4 * D) ^ 2) <
        ((G.neighborFinset (a i) ∩ G.neighborFinset (a j)) \ S).card := by
  classical
  let W (i : Fin (4 * D)) := G.neighborFinset (a i) \ S
  have hsize (i : Fin (4 * D)) : d - S.card ≤ (W i).card := by
    have hi := hdegree (a i)
    have hint : (S ∩ G.neighborFinset (a i)).card ≤ S.card := card_le_card inter_subset_left
    dsimp [W]
    rw [card_sdiff]
    rw [G.card_neighborFinset_eq_degree]
    omega
  have hcount : Fintype.card V + (4 * D) ^ 2 *
      (Fintype.card V / (2 * (4 * D) ^ 2)) < 4 * D * (d - S.card) := by
    have hd : d ≤ 2 * (d - S.card) := by omega
    have hmul := Nat.mul_le_mul_left (2 * D) hd
    have hdiv := Nat.div_mul_le_self (Fintype.card V) (2 * (4 * D) ^ 2)
    nlinarith
  obtain ⟨i, j, hij, hc⟩ := exists_large_intersection W (d - S.card)
    (Fintype.card V / (2 * (4 * D) ^ 2)) hsize (by simpa only [Fintype.card_fin] using hcount)
  refine ⟨i, j, hij, ?_⟩
  have heq : W i ∩ W j = (G.neighborFinset (a i) ∩ G.neighborFinset (a j)) \ S := by
    ext v
    simp only [W, mem_inter, mem_sdiff]
    tauto
  rwa [heq] at hc

#print axioms exists_large_common_neighbors_avoiding

end Erdos556
