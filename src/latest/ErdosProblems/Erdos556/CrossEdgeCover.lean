import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic

/-! A bipartite family with no two disjoint edges is covered by one vertex. -/

namespace Erdos556

open SimpleGraph Finset

theorem exists_single_vertex_cross_cover {V : Type*} [DecidableEq V]
    (A B : Finset V) (R : V → V → Prop)
    (hmatch : ∀ a ∈ A, ∀ a' ∈ A, ∀ b ∈ B, ∀ b' ∈ B,
      R a b → R a' b' → a = a' ∨ b = b') :
    ∃ S : Finset V, S.card ≤ 1 ∧ ∀ a ∈ A, ∀ b ∈ B, R a b → a ∈ S ∨ b ∈ S := by
  classical
  by_cases hex : ∃ a ∈ A, ∃ b ∈ B, R a b
  · obtain ⟨a, ha, b, hb, hab⟩ := hex
    by_cases hall : ∀ u ∈ A, ∀ v ∈ B, R u v → u = a
    · refine ⟨{a}, by simp, ?_⟩
      intro u hu v hv huv
      exact Or.inl (by simpa using hall u hu v hv huv)
    · push_neg at hall
      obtain ⟨c, hc, d, hd, hcd, hca⟩ := hall
      have hdb : d = b := (hmatch c hc a ha d hd b hb hcd hab).resolve_left hca
      subst d
      refine ⟨{b}, by simp, ?_⟩
      intro u hu v hv huv
      have hvb : v = b := by
        by_contra hne
        have hua := (hmatch u hu a ha v hv b hb huv hab).resolve_right hne
        have huc := (hmatch u hu c hc v hv b hb huv hcd).resolve_right hne
        exact hca (huc.symm.trans hua)
      exact Or.inr (by simpa using hvb)
  · refine ⟨∅, by simp, ?_⟩
    intro a ha b hb hab
    exact (hex ⟨a, ha, b, hb, hab⟩).elim

theorem complete_complement_cross_of_cover {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (A B S : Finset V) (hdis : Disjoint A B)
    (hcover : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b → a ∈ S ∨ b ∈ S) :
    ∀ a ∈ A \ S, ∀ b ∈ B \ S, Gᶜ.Adj a b := by
  intro a ha b hb
  rw [compl_adj]
  refine ⟨?_, ?_⟩
  · intro he
    exact (Finset.disjoint_left.mp hdis (mem_sdiff.mp ha).1) (he ▸ (mem_sdiff.mp hb).1)
  · intro hab
    rcases hcover a (mem_sdiff.mp ha).1 b (mem_sdiff.mp hb).1 hab with h | h
    · exact (mem_sdiff.mp ha).2 h
    · exact (mem_sdiff.mp hb).2 h

#print axioms exists_single_vertex_cross_cover

end Erdos556
