import ErdosProblems.Erdos577.PathPatternARows
import ErdosProblems.Erdos577.CliqueReplacementObstructions

/-! Two disjoint neighbor rows that miss one cycle vertex have total size at most three. -/

namespace Erdos577.Quadrilateral

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma missed_disjoint_row_sum (q : Quadrilateral G) (x y : V) (i : Fin 4)
    (hx : ¬G.Adj x (q i)) (hy : ¬G.Adj y (q i))
    (hcommon : ∀ u ∈ q.support, ¬(G.Adj x u ∧ G.Adj y u)) :
    degreeIn G x q.support + degreeIn G y q.support ≤ 3 := by
  by_contra! hlarge
  have hsub : q.support.filter (G.Adj x) ∪ q.support.filter (G.Adj y) ⊆
      q.support.erase (q i) := by
    intro u hu
    rcases mem_union.mp hu with hu | hu
    · obtain ⟨huq, hxu⟩ := mem_filter.mp hu
      exact mem_erase.mpr ⟨fun he ↦ hx (he ▸ hxu), huq⟩
    · obtain ⟨huq, hyu⟩ := mem_filter.mp hu
      exact mem_erase.mpr ⟨fun he ↦ hy (he ▸ hyu), huq⟩
  have hbound := card_le_card hsub
  rw [card_erase_of_mem ((q.mem_support _).mpr ⟨i, rfl⟩), q.card_support] at hbound
  obtain ⟨u, hu, hxu, hyu⟩ := common_neighbor_of_union_bound x y q.support 3 hbound hlarge
  exact hcommon u hu ⟨hxu, hyu⟩

end Erdos577.Quadrilateral
