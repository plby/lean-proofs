import ErdosProblems.Erdos577.Replacements

/-! An actual replacement cycle can be transported to a vertex with a containing neighbor row. -/

namespace Erdos577

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

lemma QuadOn.transfer_insert {s : Finset V} {x y : V} (hx : x ∉ s) (hy : y ∉ s)
    (hrow : ∀ u ∈ s, G.Adj x u → G.Adj y u) (h : QuadOn G (insert x s)) :
    QuadOn G (insert y s) := by
  by_cases hyx : y = x
  · exact hyx.symm ▸ h
  obtain ⟨q, hq⟩ := h
  obtain ⟨i, hi⟩ := (q.mem_support x).mp (hq.symm ▸ mem_insert_self x s)
  have hyq : y ∉ q.support := by
    rw [hq, mem_insert]
    exact not_or.mpr ⟨hyx, hy⟩
  have hnew := q.quad_replaceAt i y hyq (by
    intro j hij
    have he : G.Adj x (q j) := hi ▸ q.toHom.map_rel' hij
    have hj : q j ∈ s := by
      have hm := (q.mem_support _).mpr ⟨j, rfl⟩
      rw [hq] at hm
      rcases mem_insert.mp hm with hje | hjs
      · exact False.elim (he.ne hje.symm)
      · exact hjs
    exact hrow (q j) hj he)
  rw [hi, hq, erase_insert hx] at hnew
  exact hnew

lemma universal_replace_of_row_inclusion {s : Finset V} {x y : V}
    (hx : x ∉ s) (hy : y ∉ s) (hrow : ∀ u ∈ s, G.Adj x u → G.Adj y u)
    (hrep : ∀ u ∈ s, QuadOn G (insert x (s.erase u))) :
    ∀ u ∈ s, QuadOn G (insert y (s.erase u)) := by
  intro u hu
  exact QuadOn.transfer_insert (fun hh ↦ hx (mem_erase.mp hh).2)
    (fun hh ↦ hy (mem_erase.mp hh).2) (fun z hz ↦ hrow z (mem_erase.mp hz).2) (hrep u hu)

end Erdos577
