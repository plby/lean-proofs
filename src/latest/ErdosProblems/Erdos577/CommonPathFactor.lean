import ErdosProblems.Erdos577.ReplacementFactors

/-! Closing a three-vertex path at a common replacement gives two actual four-cycles. -/

namespace Erdos577

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

lemma LocalFactor.of_common_path (x m y z : V) {a : Finset V}
    (hxy : x ≠ y) (hxm : G.Adj x m) (hmy : G.Adj m y)
    (hd : Disjoint {x, m, y} a) (hz : z ∉ ({x, m, y} : Finset V) ∪ a)
    (h : CommonReplacement G x y z a) : LocalFactor G (insert z ({x, m, y} ∪ a)) := by
  obtain ⟨u, hu, hxu, hyu, hrep⟩ := h
  have hmu : m ≠ u := by
    intro he
    exact disjoint_left.mp hd (mem_insert_of_mem (mem_insert_self _ _)) (he.symm ▸ hu)
  have hquad := QuadOn.of_vertices hxy hmu hxm hmy hyu hxu.symm
  have hs : QuadOn G (insert u {x, m, y}) := by
    convert hquad using 1
    ext v
    simp only [mem_insert, mem_singleton]
    tauto
  exact LocalFactor.of_replacement hd hz hu hs hrep

end Erdos577
