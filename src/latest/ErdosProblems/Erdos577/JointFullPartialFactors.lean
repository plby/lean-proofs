import ErdosProblems.Erdos577.JointFullPairPartition

/-! The two explicit three-cycle parts of the final five-cycle contradictions. -/

namespace Erdos577.JointFinal

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

lemma FullPattern.old_partial {v : Quadrilateral G} {x y z w : V}
    (h : FullPattern v x y z w) (hcard : ({x, y, z, w} : Finset V).card = 4)
    (hx : x ∉ v.support) (hy : y ∉ v.support) (hz : z ∉ v.support) (hw : w ∉ v.support)
    (hzw : G.Adj z w) (b : Finset V)
    (hdis : Disjoint (({x, y, z, w} : Finset V) ∪ v.support) b)
    (a : V) (ha : a ∈ b) (hay : G.Adj a y) (hat : G.Adj a (v 3))
    (hrep : QuadOn G (insert x (b.erase a))) :
    Nonempty (BlockPartition G (({x, y, z, w} ∪ v.support) ∪ b)) := by
  have hm (i : Fin 4) : v i ∈ v.support := (v.mem_support _).mpr ⟨i, rfl⟩
  have hao : a ∉ v.support := fun hh ↦ disjoint_left.mp hdis (mem_union_right _ hh) ha
  have hfirst : QuadOn G {a, v 2, y, v 3} := by
    have hh := QuadOn.of_vertices (G := G) (a := a) (b := y) (c := v 2) (d := v 3)
      (fun he ↦ hao (he.symm ▸ hm 2)) (fun he ↦ hy (he.symm ▸ hm 3))
      hay ((h.2.1 2).mpr (Or.inr rfl)) (v.adjacent 2) hat.symm
    rwa [insert_comm y (v 2)] at hh
  have hsecond : QuadOn G {z, v 0, v 1, w} := QuadOn.of_vertices
    (fun he ↦ hz (he.symm ▸ hm 1)) (fun he ↦ hw (he ▸ hm 0))
    (h.2.2.1 0) (v.adjacent 0) ((h.2.2.2.1 1).mpr (Or.inl rfl)).symm hzw.symm
  have parts := outside_pair_partition (v.rotate 2) x y z w b hcard
    (by rwa [Quadrilateral.rotate_support]) (by rwa [Quadrilateral.rotate_support])
    (by rwa [Quadrilateral.rotate_support]) (by rwa [Quadrilateral.rotate_support])
    (by rwa [Quadrilateral.rotate_support]) a ha hfirst hsecond hrep
  simpa only [Quadrilateral.rotate_support] using parts

lemma FullPattern.exposed_partial {v : Quadrilateral G} {x y z w : V}
    (h : FullPattern v x y z w) (hcard : ({x, y, z, w} : Finset V).card = 4)
    (hx : x ∉ v.support) (hy : y ∉ v.support) (hz : z ∉ v.support) (hw : w ∉ v.support)
    (hzw : G.Adj z w) (b : Finset V)
    (hdis : Disjoint (({x, y, z, w} : Finset V) ∪ v.support) b)
    (a : V) (ha : a ∈ b) (hax : G.Adj a x) (hat : G.Adj a (v 3))
    (hrep : QuadOn G (insert y (b.erase a))) :
    Nonempty (BlockPartition G (({x, y, z, w} ∪ v.support) ∪ b)) := by
  have hm (i : Fin 4) : v i ∈ v.support := (v.mem_support _).mpr ⟨i, rfl⟩
  have hao : a ∉ v.support := fun hh ↦ disjoint_left.mp hdis (mem_union_right _ hh) ha
  have hfirst : QuadOn G {a, v 0, x, v 3} := by
    have hh := QuadOn.of_vertices (G := G) (a := a) (b := x) (c := v 0) (d := v 3)
      (fun he ↦ hao (he.symm ▸ hm 0)) (fun he ↦ hx (he.symm ▸ hm 3))
      hax ((h.1 0).mpr rfl) (v.adjacent 3).symm hat.symm
    rwa [insert_comm x (v 0)] at hh
  have hsecond : QuadOn G {z, v 2, v 1, w} := QuadOn.of_vertices
    (fun he ↦ hz (he.symm ▸ hm 1)) (fun he ↦ hw (he ▸ hm 2))
    (h.2.2.1 2) (v.adjacent 1).symm ((h.2.2.2.1 1).mpr (Or.inl rfl)).symm hzw.symm
  have hcard' : ({y, x, z, w} : Finset V).card = 4 := by rwa [insert_comm y x]
  have hd : Disjoint (({y, x, z, w} : Finset V) ∪ v.reverse.support) b := by
    rwa [insert_comm y x, Quadrilateral.reverse_support]
  have parts := outside_pair_partition v.reverse y x z w b hcard'
    (by rwa [Quadrilateral.reverse_support]) (by rwa [Quadrilateral.reverse_support])
    (by rwa [Quadrilateral.reverse_support]) (by rwa [Quadrilateral.reverse_support])
    hd a ha hfirst hsecond hrep
  rwa [Quadrilateral.reverse_support, insert_comm y x] at parts

end Erdos577.JointFinal
