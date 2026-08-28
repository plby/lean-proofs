import ErdosProblems.Erdos577.TripleForbiddenCompletion

/-! The explicit local cycles through a path or triangle and the middle-vertex replacement. -/

namespace Erdos577

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

lemma LocalFactor.of_three_path_common (x r y z : V) {j : Finset V}
    (hxy : x ≠ y) (hxr : G.Adj x r) (hry : G.Adj r y)
    (hd : Disjoint ({x, r, y} : Finset V) j) (hz : z ∉ ({x, r, y} : Finset V) ∪ j)
    (hcommon : CommonReplacement G x y z j) :
    LocalFactor G (insert z (({x, r, y} : Finset V) ∪ j)) := by
  obtain ⟨n, hn, hxn, hyn, hrep⟩ := hcommon
  have hrn : r ≠ n := fun he ↦ disjoint_left.mp hd (by simp) (he.symm ▸ hn)
  have hcycle := QuadOn.of_vertices hxy hrn hxr hry hyn hxn.symm
  have hquad : QuadOn G (insert n ({x, r, y} : Finset V)) := by
    convert hcycle using 1
    ext v
    simp only [mem_insert, mem_singleton]
    tauto
  exact LocalFactor.of_replacement hd hz hn hquad hrep

lemma LocalFactor.of_triangle_common {t j : Finset V} (ht : G.IsNClique 3 t)
    (hd : Disjoint t j) (z : V) (hz : z ∉ t ∪ j) {x y : V}
    (hx : x ∈ t) (hy : y ∈ t) (hxy : x ≠ y)
    (hcommon : CommonReplacement G x y z j) : LocalFactor G (insert z (t ∪ j)) := by
  classical
  obtain ⟨n, hn, hxn, hyn, hrep⟩ := hcommon
  have hout : n ∉ t := fun hh ↦ disjoint_left.mp hd hh hn
  have htwo := JointFinal.two_neighbors_degree hx hy hxy hxn.symm hyn.symm
  exact LocalFactor.of_replacement hd hz hn (QuadOn.of_triangle ht hout htwo) hrep

lemma Quadrilateral.replace_middle_of_common_three (q : Quadrilateral G) (z : V)
    (hz : z ∉ q.support) (hrow : ∀ i : Fin 4, i ≠ 0 → G.Adj z (q i)) :
    QuadOn G (insert z (q.support.erase (q 2))) := by
  apply q.quad_replaceAt 2 z hz
  intro i hi
  have hindex : ∀ i : Fin 4, (SimpleGraph.cycleGraph 4).Adj 2 i → i ≠ 0 := by decide +kernel
  exact hrow i (hindex i hi)

end Erdos577
