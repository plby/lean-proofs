import Arxiv.Arxiv2411_18291.BoundedCliqueGrouping
import Arxiv.Arxiv2411_18291.Basic

/-!
# Disjoint clique groups labelled by their unique root edge

If every clique meets a prescribed edge set in at most one edge, partition
the cliques through each edge into bounded groups. Groups from different
roots are disjoint, and every rooted clique belongs to a group carrying
its root. Both group sizes and the number of groups per root are bounded.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

structure RootedCliqueGrouping (D : Finset (Block V q)) (B : Hypergraph V r) (m : ℕ) where
  groups : Finset (Finset (Block V q))
  nonempty : ∀ c ∈ groups, c.Nonempty
  subset : ∀ c ∈ groups, c ⊆ D
  disjoint : Pairwise fun c d : groups => Disjoint c.val d.val
  root : groups → B
  root_mem : ∀ c, ∀ Q ∈ c.val, (root c).val.val ⊆ Q.val
  covers : ∀ e : B, ∀ Q ∈ D, e.val.val ⊆ Q.val → ∃ c : groups, root c = e ∧ Q ∈ c.val
  size : ∀ c ∈ groups, c.card ≤ m
  root_count : ∀ e : B, (univ.filter fun c : groups => root c = e).card ≤ m

theorem exists_rooted_clique_grouping (D : Finset (Block V q)) (B : Hypergraph V r)
    (hsingle : ∀ Q ∈ D, (cliqueEdges r Q ∩ B).card ≤ 1) (m : ℕ)
    (hsize : ∀ e ∈ B, (D.filter fun Q => e.val ⊆ Q.val).card ≤ m * m) :
    Nonempty (RootedCliqueGrouping D B m) := by
  classical
  have hpart (e : B) := exists_finpartition_bounded_size
    (D.filter fun Q => e.val.val ⊆ Q.val) m m (hsize e.val e.property)
  choose P hcount hpartsize using hpart
  let G := univ.biUnion fun e : B => (P e).parts
  have hsource (c : G) : ∃ e : B, c.val ∈ (P e).parts := by
    obtain ⟨e, _, he⟩ := mem_biUnion.mp c.property
    exact ⟨e, he⟩
  choose root hroot using hsource
  have hsub (c : G) : c.val ⊆ D :=
    ((P (root c)).subset (hroot c)).trans (filter_subset _ D)
  have hmem (c : G) (Q : Block V q) (hQ : Q ∈ c.val) : (root c).val.val ⊆ Q.val :=
    (mem_filter.mp ((P (root c)).subset (hroot c) hQ)).2
  have hsame (Q : Block V q) (hQ : Q ∈ D) (e f : B)
      (he : e.val.val ⊆ Q.val) (hf : f.val.val ⊆ Q.val) : e = f := by
    apply Subtype.ext
    exact card_le_one.mp (hsingle Q hQ) e.val
      (mem_inter.mpr ⟨(mem_cliqueEdges _ _).mpr he, e.property⟩) f.val
      (mem_inter.mpr ⟨(mem_cliqueEdges _ _).mpr hf, f.property⟩)
  refine ⟨{
    groups := G
    nonempty := fun c hc => (P (root ⟨c, hc⟩)).nonempty_of_mem_parts (hroot ⟨c, hc⟩)
    subset := fun c hc => hsub ⟨c, hc⟩
    disjoint := ?_
    root := root
    root_mem := hmem
    covers := ?_
    size := fun c hc => hpartsize (root ⟨c, hc⟩) c (hroot ⟨c, hc⟩)
    root_count := ?_ }⟩
  · intro c d hcd
    by_cases h : root c = root d
    · have hc := hroot c
      rw [h] at hc
      exact (P (root d)).disjoint hc (hroot d) (fun heq => hcd (Subtype.ext heq))
    · apply disjoint_left.mpr
      intro Q hQc hQd
      exact h (hsame Q (hsub c hQc) (root c) (root d) (hmem c Q hQc) (hmem d Q hQd))
  · intro e Q hQ heQ
    obtain ⟨c, hc, hQc⟩ := (P e).exists_mem (mem_filter.mpr ⟨hQ, heQ⟩)
    have hcG : c ∈ G := mem_biUnion.mpr ⟨e, mem_univ _, hc⟩
    exact ⟨⟨c, hcG⟩, hsame Q hQ (root ⟨c, hcG⟩) e (hmem ⟨c, hcG⟩ Q hQc) heQ, hQc⟩
  · intro e
    have hmap : (univ.filter fun c : G => root c = e).map
        (Function.Embedding.subtype (· ∈ G)) ⊆ (P e).parts := by
      intro c hc
      obtain ⟨d, hd, rfl⟩ := mem_map.mp hc
      have h := hroot d
      rwa [(mem_filter.mp hd).2] at h
    calc
      _ = ((univ.filter fun c : G => root c = e).map
          (Function.Embedding.subtype (· ∈ G))).card := (card_map _).symm
      _ ≤ (P e).parts.card := card_le_card hmap
      _ ≤ m := hcount e

theorem exists_rooted_clique_grouping_sqrt (D : Finset (Block V q)) (B : Hypergraph V r)
    (hsingle : ∀ Q ∈ D, (cliqueEdges r Q ∩ B).card ≤ 1) (x : ℕ)
    (hsize : ∀ e ∈ B, (D.filter fun Q => e.val ⊆ Q.val).card ≤ x) :
    Nonempty (RootedCliqueGrouping D B (x.sqrt + 1)) :=
  exists_rooted_clique_grouping D B hsingle (x.sqrt + 1)
    (fun e he => (hsize e he).trans (Nat.lt_succ_sqrt x).le)

end Arxiv2411_18291
