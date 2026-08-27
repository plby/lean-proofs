import Arxiv.Arxiv2411_18291.FrozenEdgeLoss

/-!
# Edge-neighborhood estimates with the tracked edge excluded

Removing all possible selections through the tracked edge costs at most
one pair codegree in each other edge neighborhood. Combining this with
the union overlap estimate gives an explicit error for the frozen drift.
-/

open Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

omit [Fintype V] in
theorem excludedEdge_degree_partition (H : Finset (Block V q)) (e f : Block V r) :
    ((H.filter fun Q => ¬e.val ⊆ Q.val).filter fun Q => f.val ⊆ Q.val).card +
      (H.filter fun Q => e.val ⊆ Q.val ∧ f.val ⊆ Q.val).card =
        (H.filter fun Q => f.val ⊆ Q.val).card := by
  have heq : (H.filter fun Q => ¬e.val ⊆ Q.val).filter (fun Q => f.val ⊆ Q.val) =
      (H.filter fun Q => f.val ⊆ Q.val) \
        (H.filter fun Q => e.val ⊆ Q.val ∧ f.val ⊆ Q.val) := by
    ext Q
    simp only [mem_filter, mem_sdiff]
    tauto
  rw [heq]
  apply card_sdiff_add_card_eq_card
  intro Q hQ
  exact mem_filter.mpr ⟨(mem_filter.mp hQ).1, (mem_filter.mp hQ).2.2⟩

omit [Fintype V] in
theorem excludedEdge_degree_self (H : Finset (Block V q)) (e : Block V r) :
    ((H.filter fun Q => ¬e.val ⊆ Q.val).filter fun Q => e.val ⊆ Q.val).card = 0 := by
  have heq : (H.filter fun Q => ¬e.val ⊆ Q.val).filter (fun Q => e.val ⊆ Q.val) = ∅ := by
    ext Q
    simp
  rw [heq, card_empty]

theorem excludedEdge_neighborhood_bounds (hqr : r < q) (H : Finset (Block V q))
    (e : Block V r) (P : Block V q) (heP : e.val ⊆ P.val) :
    (cliqueNeighborhood r (H.filter fun Q => ¬e.val ⊆ Q.val) P).card ≤
        (∑ f ∈ (cliqueEdges r P).erase e, (H.filter fun Q => f.val ⊆ Q.val).card) ∧
      (∑ f ∈ (cliqueEdges r P).erase e, (H.filter fun Q => f.val ⊆ Q.val).card) ≤
        (cliqueNeighborhood r (H.filter fun Q => ¬e.val ⊆ Q.val) P).card +
          ((q.choose r) ^ 2 + q.choose r) * (Fintype.card V) ^ (q - r - 1) := by
  let K := H.filter fun Q => ¬e.val ⊆ Q.val
  let L := (Fintype.card V) ^ (q - r - 1)
  have hzero : (K.filter fun Q => e.val ⊆ Q.val).card = 0 := excludedEdge_degree_self H e
  have hsum : (∑ f ∈ cliqueEdges r P, (K.filter fun Q => f.val ⊆ Q.val).card) =
      ∑ f ∈ (cliqueEdges r P).erase e, (K.filter fun Q => f.val ⊆ Q.val).card := by
    have h := sum_erase_add (cliqueEdges r P)
      (fun f => (K.filter fun Q => f.val ⊆ Q.val).card) ((mem_cliqueEdges _ _).mpr heP)
    simpa only [hzero, add_zero] using h.symm
  have hmono (f : Block V r) : (K.filter fun Q => f.val ⊆ Q.val).card ≤
      (H.filter fun Q => f.val ⊆ Q.val).card :=
    card_le_card (filter_subset_filter _ (filter_subset _ _))
  have hplus : ∀ f ∈ (cliqueEdges r P).erase e,
      (H.filter fun Q => f.val ⊆ Q.val).card ≤ (K.filter fun Q => f.val ⊆ Q.val).card + L := by
    intro f hf
    have hpart := excludedEdge_degree_partition H e f
    have hcodeg := clique_codegree_le_power hqr H e f (Ne.symm (mem_erase.mp hf).1)
    dsimp only [K, L]
    omega
  have hcard : ((cliqueEdges r P).erase e).card ≤ q.choose r := by
    simpa only [card_cliqueEdges] using card_erase_le (s := cliqueEdges r P) (a := e)
  constructor
  · calc
      _ ≤ ∑ f ∈ cliqueEdges r P, (K.filter fun Q => f.val ⊆ Q.val).card :=
        cliqueNeighborhood_card_le_sum K P
      _ = _ := hsum
      _ ≤ _ := sum_le_sum fun f _ => hmono f
  · calc
      _ ≤ ∑ f ∈ (cliqueEdges r P).erase e,
          ((K.filter fun Q => f.val ⊆ Q.val).card + L) := sum_le_sum hplus
      _ = (∑ f ∈ cliqueEdges r P, (K.filter fun Q => f.val ⊆ Q.val).card) +
          ((cliqueEdges r P).erase e).card * L := by rw [sum_add_distrib, sum_const, hsum]; simp
      _ ≤ (∑ f ∈ cliqueEdges r P, (K.filter fun Q => f.val ⊆ Q.val).card) + q.choose r * L :=
        Nat.add_le_add_left (Nat.mul_le_mul_right L hcard) _
      _ ≤ (cliqueNeighborhood r K P).card + (q.choose r) ^ 2 * L + q.choose r * L :=
        Nat.add_le_add_right (cliqueNeighborhood_sum_le_card_add_error hqr K P) _
      _ = _ := by simp only [K, L, add_mul, add_assoc]

end Arxiv2411_18291
