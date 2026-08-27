import Arxiv.Arxiv2411_18291.PreparedFamily

/-! # Adding a newly prepared edge to the invariant -/

open Finset

noncomputable section

namespace Arxiv2411_18291.PreparedFamily

variable {V : Type*} [DecidableEq V] {q r : ℕ}
variable {ι : Type*} [DecidableEq ι]
variable {G : Hypergraph V r} {D : Finset (Block V q)} {B : Block V q}
variable {s : Finset ι} {edge : ι → Block V r}

def insert (P : PreparedFamily G D B s edge) (j : ι) (hj : j ∉ s)
    (N : Block V q) (R : Finset V) (hN : N ∈ D)
    (heN : (edge j).val ⊆ N.val) (hNR : N.val ⊆ R)
    (hRB : R ∩ B.val = (edge j).val)
    (hold_new : ∀ i ∈ s, Disjoint (P.region i) (N.val \ B.val))
    (hnew_old : ∀ i ∈ s, Disjoint R ((P.clique i).val \ B.val))
    (hlocalE : ∀ e ∈ G, ¬Disjoint e.val (N.val \ B.val) → e.val ⊆ R)
    (hlocalD : ∀ Q ∈ D, ¬Disjoint Q.val (N.val \ B.val) → Q.val ⊆ R) :
    PreparedFamily G D B (Insert.insert j s) edge where
  clique := Function.update P.clique j N
  region := Function.update P.region j R
  clique_mem := by
    intro i hi
    rcases mem_insert.mp hi with rfl | hi
    · simpa only [Function.update_self] using hN
    · simpa only [Function.update_of_ne (ne_of_mem_of_not_mem hi hj)] using P.clique_mem i hi
  edge_subset := by
    intro i hi
    rcases mem_insert.mp hi with rfl | hi
    · simpa only [Function.update_self] using heN
    · simpa only [Function.update_of_ne (ne_of_mem_of_not_mem hi hj)] using P.edge_subset i hi
  clique_subset := by
    intro i hi
    rcases mem_insert.mp hi with rfl | hi
    · simpa only [Function.update_self] using hNR
    · simpa only [Function.update_of_ne (ne_of_mem_of_not_mem hi hj)] using P.clique_subset i hi
  region_base := by
    intro i hi
    rcases mem_insert.mp hi with rfl | hi
    · simpa only [Function.update_self] using hRB
    · simpa only [Function.update_of_ne (ne_of_mem_of_not_mem hi hj)] using P.region_base i hi
  separated := by
    intro i hi k hk hik
    rcases mem_insert.mp hi with hij | hi_s
    · subst i
      rcases mem_insert.mp hk with hkj | hk_s
      · subst k
        exact (hik rfl).elim
      · simpa only [Function.update_self,
          Function.update_of_ne (ne_of_mem_of_not_mem hk_s hj)] using hnew_old k hk_s
    · rcases mem_insert.mp hk with hkj | hk_s
      · subst k
        simpa only [Function.update_self,
          Function.update_of_ne (ne_of_mem_of_not_mem hi_s hj)] using hold_new i hi_s
      · simpa only [Function.update_of_ne (ne_of_mem_of_not_mem hi_s hj),
          Function.update_of_ne (ne_of_mem_of_not_mem hk_s hj)] using
          P.separated i hi_s k hk_s hik
  edge_local := by
    intro i hi
    rcases mem_insert.mp hi with rfl | hi
    · simpa only [Function.update_self] using hlocalE
    · simpa only [Function.update_of_ne (ne_of_mem_of_not_mem hi hj)] using P.edge_local i hi
  clique_local := by
    intro i hi
    rcases mem_insert.mp hi with rfl | hi
    · simpa only [Function.update_self] using hlocalD
    · simpa only [Function.update_of_ne (ne_of_mem_of_not_mem hi hj)] using P.clique_local i hi

/-- A new region that meets all old regions only inside the base automatically
satisfies the cross-separation requirements for insertion. -/
def insert_fresh (P : PreparedFamily G D B s edge) (j : ι) (hj : j ∉ s)
    (N : Block V q) (R U : Finset V) (hN : N ∈ D)
    (heN : (edge j).val ⊆ N.val) (hNR : N.val ⊆ R)
    (hRB : R ∩ B.val = (edge j).val)
    (hregions : ∀ i ∈ s, P.region i ⊆ U) (hfresh : R ∩ U ⊆ B.val)
    (hlocalE : ∀ e ∈ G, ¬Disjoint e.val (N.val \ B.val) → e.val ⊆ R)
    (hlocalD : ∀ Q ∈ D, ¬Disjoint Q.val (N.val \ B.val) → Q.val ⊆ R) :
    PreparedFamily G D B (Insert.insert j s) edge := by
  apply P.insert j hj N R hN heN hNR hRB _ _ hlocalE hlocalD
  · intro i hi
    apply Finset.disjoint_left.mpr
    intro v hvR hvN
    exact (mem_sdiff.mp hvN).2
      (hfresh (mem_inter.mpr ⟨hNR (mem_sdiff.mp hvN).1, hregions i hi hvR⟩))
  · intro i hi
    apply Finset.disjoint_left.mpr
    intro v hvR hvN
    exact (mem_sdiff.mp hvN).2 (hfresh (mem_inter.mpr
      ⟨hvR, hregions i hi (P.clique_subset i hi (mem_sdiff.mp hvN).1)⟩))

end Arxiv2411_18291.PreparedFamily
