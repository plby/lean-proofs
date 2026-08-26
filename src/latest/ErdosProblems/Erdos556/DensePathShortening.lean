import ErdosProblems.Erdos556.CommonNeighbors
import ErdosProblems.Erdos556.NearbyPathVertices
import ErdosProblems.Erdos556.PathShortcuts

/-!
# Bounded parity-preserving shortening in dense graphs

A path longer than a fixed threshold in a graph of linear minimum
degree can be shortened by a bounded positive even amount. The new
vertices, if any, avoid a prescribed small forbidden set.
-/

namespace Erdos556

open SimpleGraph Finset

theorem exists_shorter_same_parity_path_of_min_degree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D d : ℕ) (hD : 0 < D)
    (hscale : Fintype.card V ≤ D * d) (hdegree : ∀ v, d ≤ G.degree v)
    (hN : 8 * (4 * D) ^ 2 ≤ Fintype.card V)
    (R : Finset V) (hR : 2 * (R.card + 16 * D + 1) ≤ d)
    {u v : V} (p : G.Walk u v) (hp : p.IsPath) (hlen : 16 * D ≤ p.length) :
    ∃ q : G.Walk u v, q.IsPath ∧ q.length < p.length ∧
      p.length ≤ q.length + (16 * D + 8 * (4 * D) ^ 2) ∧
      q.length % 2 = p.length % 2 ∧
      ∀ z ∈ q.support, z ∈ p.support ∨ z ∉ R := by
  classical
  let S := R ∪ (p.take (16 * D)).support.toFinset
  have hprefix : (p.take (16 * D)).support.toFinset.card ≤ 16 * D + 1 := by
    have h := List.toFinset_card_le (p.take (16 * D)).support
    simpa only [Walk.length_support, Walk.take_length, min_eq_left hlen] using h
  have hS : 2 * S.card ≤ d := by
    have h := card_union_le R (p.take (16 * D)).support.toFinset
    change S.card ≤ R.card + (p.take (16 * D)).support.toFinset.card at h
    omega
  let a (i : Fin (4 * D)) := p.getVert (4 * i.val)
  have hpositive : 0 < Fintype.card V := by nlinarith
  obtain ⟨i₀, j₀, hne, hc⟩ := exists_large_common_neighbors_avoiding G D d hpositive
    hscale hdegree S hS a
  have hordered : ∃ i j : Fin (4 * D), i.val < j.val ∧
      Fintype.card V / (2 * (4 * D) ^ 2) <
        ((G.neighborFinset (a i) ∩ G.neighborFinset (a j)) \ S).card := by
    have hne' : i₀.val ≠ j₀.val := fun h => hne (Fin.ext h)
    rcases lt_or_gt_of_ne hne' with hij | hji
    · exact ⟨i₀, j₀, hij, hc⟩
    · refine ⟨j₀, i₀, hji, ?_⟩
      rwa [inter_comm]
  obtain ⟨i, j, hij, hcommon⟩ := hordered
  let W := (G.neighborFinset (a i) ∩ G.neighborFinset (a j)) \ S
  have hmem (x : V) (hx : x ∈ W) :
      G.Adj (p.getVert (4 * i.val)) x ∧ G.Adj (p.getVert (4 * j.val)) x ∧ x ∉ S := by
    obtain ⟨hxij, hxS⟩ := mem_sdiff.mp hx
    obtain ⟨hxi, hxj⟩ := mem_inter.mp hxij
    exact ⟨(G.mem_neighborFinset _ _).mp hxi, (G.mem_neighborFinset _ _).mp hxj, hxS⟩
  have h4j : 4 * j.val ≤ p.length := by have h := j.isLt; omega
  have h4i : 4 * i.val + 4 ≤ 4 * j.val := by omega
  have hpar : (4 * i.val) % 2 = (4 * j.val) % 2 := by omega
  by_cases hex : ∃ x ∈ W, x ∉ p.support
  · obtain ⟨x, hxW, hx⟩ := hex
    obtain ⟨hix, hjx, hxS⟩ := hmem x hxW
    have hxR : x ∉ R := fun h => hxS (mem_union_left _ h)
    obtain ⟨q, hq, hlt, hbound, hparq, hsupport⟩ :=
      exists_shorter_same_parity_path_external p hp (4 * i.val) (4 * j.val)
        h4i h4j hpar x hx hix hjx
    refine ⟨q, hq, hlt, ?_, hparq, ?_⟩
    · have hjlt := j.isLt
      omega
    · intro z hz
      rcases hsupport z hz with hzp | hzx
      · exact Or.inl hzp
      · exact Or.inr (hzx ▸ hxR)
  · have hW : ∀ x ∈ W, x ∈ p.support := by
      intro x hx
      by_contra h
      exact hex ⟨x, hx, h⟩
    have hK : 0 < 2 * (4 * D) ^ 2 := by positivity
    have hN' : 4 * (2 * (4 * D) ^ 2) ≤ Fintype.card V := by nlinarith only [hN]
    obtain ⟨s, t, hst, ht, hclose, hparst, hsW, htW⟩ :=
      exists_close_same_parity_path_vertices p W hW (Fintype.card V)
        (2 * (4 * D) ^ 2) hK hN' hp.length_lt hcommon
    have hs : 16 * D < s := by
      by_contra h
      have hs' : s ≤ 16 * D := by omega
      have hsP : p.getVert s ∈ (p.take (16 * D)).support :=
        (mem_support_take_iff p (16 * D) hlen).mpr ⟨s, hs', rfl⟩
      exact (hmem _ hsW).2.2 (mem_union_right R (List.mem_toFinset.mpr hsP))
    have hst2 : s + 2 ≤ t := by omega
    have hjs : 4 * j.val ≤ s := by have hjlt := j.isLt; omega
    obtain ⟨q, hq, hlt, hbound, hparq, hsupport⟩ :=
      exists_shorter_same_parity_path_reversal p hp (4 * i.val) (4 * j.val) s t
        h4i hjs hst2 ht hpar hparst (hmem _ hsW).1 (hmem _ htW).2.1
    refine ⟨q, hq, hlt, ?_, hparq, fun z hz => Or.inl (hsupport z hz)⟩
    have hjlt := j.isLt
    omega

#print axioms exists_shorter_same_parity_path_of_min_degree

end Erdos556
