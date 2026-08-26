import ErdosProblems.Erdos73.GraphPaths

/-! The support of a simple cycle remains connected after at most one vertex deletion. -/

namespace Erdos73
noncomputable section
open scoped Classical

open SimpleGraph Finset Erdos73Infrastructure.SimpleGraph

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

theorem cycle_support_erase_connected {v : V} (c : G.Walk v v) (hc : c.IsCycle) :
    (G.induce ((c.support.toFinset.erase v : Finset V) : Set V)).Connected := by
  let P : GraphPath G := ⟨c.snd, v, c.tail, hc.isPath_tail⟩
  have hnil : ¬ c.Nil := hc.not_nil
  have hne : P.source ≠ P.target := (c.adj_snd hnil).ne.symm
  have hPset : P.vertexSet = c.support.toFinset := by
    ext x
    change x ∈ c.tail.support.toFinset ↔ x ∈ c.support.toFinset
    rw [List.mem_toFinset, List.mem_toFinset, ← c.cons_support_tail hnil, List.mem_cons]
    constructor
    · exact Or.inr
    · rintro (rfl | hx)
      · exact c.tail.end_mem_support
      · exact hx
  have heq : P.dropLast.vertexSet = c.support.toFinset.erase v := by
    ext x
    rw [mem_erase, ← hPset, P.mem_vertexSet_iff_mem_dropLast_or_eq_target hne]
    constructor
    · intro hx
      have hvnot : v ∉ P.dropLast.vertexSet := P.target_not_mem_dropLast_vertexSet hne
      exact ⟨fun he => hvnot (he ▸ hx), Or.inl hx⟩
    · rintro ⟨hne', hx | hx⟩
      · exact hx
      · exact (hne' hx).elim
  rw [← heq]
  exact P.dropLast.connected_induce_vertexSet

theorem cycle_support_sdiff_connected {v : V} (c : G.Walk v v) (hc : c.IsCycle)
    (X : Finset V) (hX : X.card < 2) :
    (G.induce ((c.support.toFinset \ X : Finset V) : Set V)).Connected := by
  rcases X.eq_empty_or_nonempty with hXempty | hXnonempty
  · subst X
    have he : ((c.support.toFinset \ ∅ : Finset V) : Set V) = {x | x ∈ c.support} := by
      ext x
      change x ∈ c.support.toFinset \ ∅ ↔ x ∈ c.support
      simp only [Finset.mem_sdiff, Finset.notMem_empty, not_false_eq_true,
        and_true, List.mem_toFinset]
    rw [he]
    exact c.connected_induce_support
  · obtain ⟨a, haX⟩ := hXnonempty
    have hXa : X = {a} := Finset.eq_singleton_iff_unique_mem.mpr
      ⟨haX, fun b hb => Finset.card_le_one.mp (by omega : X.card ≤ 1) b hb a haX⟩
    subst X
    by_cases ha : a ∈ c.support
    · let d := c.rotate a ha
      have hd : d.IsCycle := hc.rotate ha
      have heq : d.support.toFinset = c.support.toFinset := by
        ext x
        simp only [List.mem_toFinset, d, Walk.mem_support_rotate_iff]
      have hh := cycle_support_erase_connected d hd
      rw [heq] at hh
      have he : ((c.support.toFinset \ {a} : Finset V) : Set V) =
          (c.support.toFinset.erase a : Set V) := by
        ext x
        change x ∈ c.support.toFinset \ {a} ↔ x ∈ c.support.toFinset.erase a
        simp only [mem_sdiff, mem_singleton, mem_erase]
        exact and_comm
      rw [he]
      exact hh
    · have heq : c.support.toFinset \ {a} = c.support.toFinset := by
        ext x
        simp only [mem_sdiff, mem_singleton, List.mem_toFinset]
        exact ⟨And.left, fun hx => ⟨hx, fun he => ha (he ▸ hx)⟩⟩
      rw [heq]
      have he : (c.support.toFinset : Set V) = {x | x ∈ c.support} := by
        ext x
        exact List.mem_toFinset
      rw [he]
      exact c.connected_induce_support

end
end Erdos73
