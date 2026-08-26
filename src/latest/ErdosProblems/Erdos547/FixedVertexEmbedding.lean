import ErdosProblems.Erdos547.BipartiteEmbedding

/-!
# Greedy tree embedding with two prescribed images

All ordinary target pools have enough neighbours. A second prescribed image
is kept unused until its vertex is reached, and every possible parent image
is adjacent to it. The pools need not be disjoint.
-/

namespace Erdos547

open Finset SimpleGraph

variable {U V : Type*} [Fintype U]

theorem exists_copy_of_two_prescribed_vertices (T : SimpleGraph U) (G : SimpleGraph V)
    [DecidableRel G.Adj] (hT : T.IsTree) (r x : U) (v w : V)
    (pool : U → Finset V) (hv : v ∈ pool r) (hx : pool x = {w})
    (havoid : ∀ u, u ≠ x → w ∉ pool u)
    (hdegree : ∀ u y, T.Adj u y → y ≠ r → y ≠ x → ∀ z ∈ pool u,
      Fintype.card U ≤ degreeIn G (pool y) z)
    (hattach : ∀ u, T.Adj u x → ∀ z ∈ pool u, G.Adj z w) :
    ∃ f : T.Copy G, f r = v ∧ f x = w ∧ ∀ u, f u ∈ pool u := by
  classical
  let S : Finset U := {r}
  have hrS (u : (S : Set U)) : u.val = r := by simpa [S] using u.property
  let e : (T.induce (S : Set U)).Copy G := {
    toHom := {
      toFun := fun _ ↦ v
      map_rel' := fun {u y} huy ↦ by
        have hh : T.Adj u.val y.val := huy
        rw [hrS u, hrS y] at hh
        exact (T.loopless.irrefl _ hh).elim }
    injective' := fun u y _ ↦ Subtype.ext ((hrS u).trans (hrS y).symm) }
  have hS : (T.induce (S : Set U)).Connected := by
    let : Nonempty ({r} : Set U) := ⟨⟨r, rfl⟩⟩
    have hco : (S : Set U) = {r} := by ext u; simp [S]
    rw [hco]
    exact SimpleGraph.IsTree.of_subsingleton.connected
  obtain ⟨f, hf, hpool⟩ := extend_connected_copy hT S hS e
    (fun u z ↦ z ∈ pool u) (fun u ↦ by change v ∈ pool u.val; rwa [hrS u]) (by
      intro Q hSQ _hconn f _hf hpool hQlt p y hy hpy
      by_cases hyx : y = x
      · subst y
        refine ⟨w, hattach p.val hpy (f p) (hpool p), ?_, ?_⟩
        · intro u heq
          have hux : u.val ≠ x := fun hh ↦ hy (hh ▸ u.property)
          exact havoid u.val hux (heq ▸ hpool u)
        · rw [hx]
          exact Finset.mem_singleton_self _
      · have hyr : y ≠ r := fun hh ↦ hy (hh ▸ hSQ (Finset.mem_singleton_self _))
        let used : Finset V := Finset.univ.image f
        have hused : used.card = Q.card := by
          simpa [used] using Finset.card_image_of_injective
            (Finset.univ : Finset (Q : Set U)) f.injective
        have hcount : (used ∩ pool y).card < degreeIn G (pool y) (f p) :=
          ((Finset.card_le_card Finset.inter_subset_left).trans_eq hused).trans_lt
            (hQlt.trans_le (hdegree p.val y hpy hyr hyx (f p) (hpool p)))
        obtain ⟨z, hz, hpz, hzu⟩ := exists_unused_neighbor_into G (pool y) used (f p) hcount
        refine ⟨z, hpz, ?_, hz⟩
        intro u heq
        exact hzu (Finset.mem_image.mpr ⟨u, Finset.mem_univ _, heq⟩))
  have hfx : f x = w := by simpa only [hx, Finset.mem_singleton] using hpool x
  exact ⟨f, hf ⟨r, Finset.mem_singleton_self _⟩, hfx, hpool⟩

end Erdos547

#print axioms Erdos547.exists_copy_of_two_prescribed_vertices
