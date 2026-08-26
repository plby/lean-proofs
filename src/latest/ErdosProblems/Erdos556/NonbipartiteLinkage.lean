import ErdosProblems.Erdos556.Menger
import ErdosProblems.Erdos556.OddCycleArcs
import ErdosProblems.Erdos556.PathOperations
import ErdosProblems.Erdos556.InconsistentEars

/-!
# Inconsistent paths in a two-connected nonbipartite graph

Two disjoint paths link a labelled vertex set to an odd cycle. Truncating
at the first cycle vertices and choosing one of the two cycle arcs produces
a path whose parity disagrees with the endpoint labels.
-/

namespace Erdos556

open SimpleGraph

theorem exists_inconsistent_path_of_twoConnected {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (hG : TwoConnected G) (hnonbip : ¬ G.Colorable 2)
    (S : Set V) (hS : 2 ≤ S.ncard) (colour : S → Bool) :
    ∃ a b : S, ∃ p : G.Walk a.val b.val, p.IsPath ∧
      ¬ (Even p.length ↔ (colour a ↔ colour b)) := by
  classical
  obtain ⟨w, c, hc, ho⟩ : ∃ (w : V) (c : G.Walk w w), c.IsCycle ∧ Odd c.length := by
    by_contra h
    apply hnonbip
    apply (colorable_two_iff_no_odd_cycle G).mpr
    intro w c hc ho
    exact h ⟨w, c, hc, ho⟩
  let C : Set V := {z | z ∈ c.support}
  have hC : C.Nontrivial := by
    refine ⟨w, c.start_mem_support, c.snd, ?_, (c.adj_snd hc.not_nil).ne⟩
    exact List.mem_of_mem_tail (Walk.snd_mem_tail_support hc.not_nil)
  have hCcard : 2 ≤ C.ncard := Set.one_lt_ncard_iff_nontrivial.mpr hC
  obtain ⟨P⟩ := hG.exists_rawTwoPathPacking hS hCcard
  obtain ⟨x, hxC, p, hp, _, hpsub, hpC⟩ :=
    exists_path_first_meeting_set P.p P.p_isPath C P.b₁_mem
  obtain ⟨y, hyC, q, hq, _, hqsub, hqC⟩ :=
    exists_path_first_meeting_set P.q P.q_isPath C P.b₂_mem
  have hpq (z : V) (hzp : z ∈ p.support) (hzq : z ∈ q.support) : False :=
    P.disjoint_support (hpsub hzp) (hqsub hzq)
  have hxy : x ≠ y := by
    intro h
    exact hpq x p.end_mem_support (h ▸ q.end_mem_support)
  obtain ⟨r, s, hr, hs, hpar, _, _, _, _⟩ :=
    exists_opposite_parity_paths_through_cycle c hc ho p q hp hq hxC hyC hxy hpC hqC hpq
  let a : S := ⟨P.a₁, P.a₁_mem⟩
  let b : S := ⟨P.a₂, P.a₂_mem⟩
  by_cases h : Even r.length ↔ (colour a ↔ colour b)
  · refine ⟨a, b, s, hs, ?_⟩
    intro h'
    have he := h.trans h'.symm
    simp only [Nat.even_iff] at he
    apply hpar
    omega
  · exact ⟨a, b, r, hr, h⟩

#print axioms exists_inconsistent_path_of_twoConnected

theorem exists_inconsistent_ear_of_twoConnected {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (hG : TwoConnected G) (hnonbip : ¬ G.Colorable 2)
    (S : Set V) (hS : 2 ≤ S.ncard) (colour : S → Bool) :
    ∃ a b : S, a.val ≠ b.val ∧ ∃ p : G.Walk a.val b.val, p.IsPath ∧
      ¬ (Even p.length ↔ (colour a ↔ colour b)) ∧
      ∀ z ∈ p.support, z ≠ a.val → z ≠ b.val → z ∉ S := by
  obtain ⟨u, v, p, hp, hw⟩ := exists_inconsistent_path_of_twoConnected hG hnonbip S hS colour
  obtain ⟨a, b, hab, q, hq, hqw, _, hav⟩ :=
    exists_inconsistent_ear_of_path S colour (u := u) (v := v) p hp hw
  exact ⟨a, b, hab, q, hq, hqw, hav⟩

#print axioms exists_inconsistent_ear_of_twoConnected

end Erdos556
