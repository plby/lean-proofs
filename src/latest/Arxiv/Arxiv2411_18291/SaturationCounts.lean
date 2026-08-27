import Arxiv.Arxiv2411_18291.ModularCliqueGenerators
import Arxiv.Arxiv2411_18291.Decomposition
import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-!
# Counting saturated faces, saturated cliques, and heavy edges

These deterministic double counts implement the counting steps in
`lem:KSG`. They separate the finite selection argument from the typicality
estimates used later to choose the thresholds.
-/

open Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

theorem sum_clique_face_load (G : Finset (Block V q)) (r : ℕ) :
    (∑ S : Block V r, (G.filter fun Q => S.val ⊆ Q.val).card) = q.choose r * G.card := by
  calc
    _ = ∑ Q ∈ G, (cliqueEdges r Q).card := by
      simpa only [bipartiteAbove, bipartiteBelow, cliqueEdges] using
        (sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
          (fun S : Block V r => fun Q : Block V q => S.val ⊆ Q.val) (s := univ) (t := G))
    _ = _ := by simp only [card_cliqueEdges, sum_const, smul_eq_mul, Nat.mul_comm]

def saturatedFaces (G : Finset (Block V q)) (r cap : ℕ) : Finset (Block V r) :=
  univ.filter fun S => cap ≤ (G.filter fun Q => S.val ⊆ Q.val).card

def saturatedCliques (D G : Finset (Block V q)) (r cap : ℕ) : Finset (Block V q) :=
  D.filter fun Q => ∃ S ∈ saturatedFaces G r cap, S.val ⊆ Q.val

theorem saturatedFaces_card_bound (G : Finset (Block V q)) (r cap : ℕ) :
    cap * (saturatedFaces G r cap).card ≤ q.choose r * G.card := by
  calc
    _ = ∑ S ∈ saturatedFaces G r cap, cap := by
      simp only [sum_const, smul_eq_mul, Nat.mul_comm]
    _ ≤ ∑ S ∈ saturatedFaces G r cap, (G.filter fun Q => S.val ⊆ Q.val).card :=
      sum_le_sum fun _ hS => (mem_filter.mp hS).2
    _ ≤ ∑ S : Block V r, (G.filter fun Q => S.val ⊆ Q.val).card :=
      sum_le_sum_of_subset (subset_univ _)
    _ = _ := sum_clique_face_load G r

theorem saturatedCliques_eq_biUnion (D G : Finset (Block V q)) (r cap : ℕ) :
    saturatedCliques D G r cap =
      (saturatedFaces G r cap).biUnion fun S => D.filter fun Q => S.val ⊆ Q.val := by
  ext Q
  constructor
  · intro hQ
    obtain ⟨hQD, S, hS, hSQ⟩ := mem_filter.mp hQ
    exact mem_biUnion.mpr ⟨S, hS, mem_filter.mpr ⟨hQD, hSQ⟩⟩
  · intro hQ
    obtain ⟨S, hS, hQ⟩ := mem_biUnion.mp hQ
    obtain ⟨hQD, hSQ⟩ := mem_filter.mp hQ
    exact mem_filter.mpr ⟨hQD, S, hS, hSQ⟩

theorem saturatedCliques_card_bound (D G : Finset (Block V q)) (r cap L : ℕ)
    (hL : ∀ S ∈ saturatedFaces G r cap, (D.filter fun Q => S.val ⊆ Q.val).card ≤ L) :
    (saturatedCliques D G r cap).card ≤ (saturatedFaces G r cap).card * L := by
  rw [saturatedCliques_eq_biUnion]
  apply card_biUnion_le.trans
  calc
    _ ≤ ∑ S ∈ saturatedFaces G r cap, L := sum_le_sum hL
    _ = _ := by simp only [sum_const, smul_eq_mul]

def heavyCliqueEdges (K : Hypergraph V r) (D : Finset (Block V q)) (threshold : ℕ) :=
  K.filter fun e => threshold ≤ (D.filter fun Q => e.val ⊆ Q.val).card

omit [Fintype V] in
theorem heavyCliqueEdges_card_bound [Finite V] (K : Hypergraph V r) (D : Finset (Block V q))
    (threshold : ℕ) :
    threshold * (heavyCliqueEdges K D threshold).card ≤ q.choose r * D.card := by
  let : Fintype V := Fintype.ofFinite V
  have hsub : heavyCliqueEdges K D threshold ⊆ saturatedFaces D r threshold := by
    intro e he
    exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp he).2⟩
  exact (Nat.mul_le_mul_left threshold (card_le_card hsub)).trans
    (saturatedFaces_card_bound D r threshold)

theorem exists_modular_generators_outside_saturation (N : ℕ) (hN : 0 < N)
    (K : Hypergraph V (r + 1)) (D : Finset (Block V q))
    (hD : ∀ Q ∈ D, cliqueEdges (r + 1) Q ⊆ K) (cap : ℕ) :
    ∃ G : Finset (Block V q), G ⊆ D ∧
      (∀ S : Block V r, (G.filter fun Q => S.val ⊆ Q.val).card ≤ cap) ∧
      G.card ≤ N * K.card ∧
      cap * (saturatedFaces G r cap).card ≤ q.choose r * (N * K.card) ∧
      ∀ Q ∈ D \ saturatedCliques D G r cap,
        modularCliqueVector N (r + 1) Q ∈ generatedSubgroup (modularCliqueVector N (r + 1)) G := by
  obtain ⟨G, hGD, hdegree, hsize, hgen⟩ := exists_modular_generating_cliques N hN K D hD cap
  refine ⟨G, hGD, hdegree, hsize,
    (saturatedFaces_card_bound G r cap).trans (Nat.mul_le_mul_left _ hsize), ?_⟩
  intro Q hQ
  obtain ⟨hQD, hnot⟩ := mem_sdiff.mp hQ
  apply hgen Q hQD
  intro S hSQ
  by_contra hs
  exact hnot (mem_filter.mpr ⟨hQD, S, mem_filter.mpr ⟨mem_univ _, Nat.le_of_not_gt hs⟩, hSQ⟩)

end Arxiv2411_18291
