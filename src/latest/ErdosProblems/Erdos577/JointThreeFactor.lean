import ErdosProblems.Erdos577.JointThreeLeafRows

/-! The two terminal rows on the same adjacent pair give an exact forbidden two-cycle factor. -/

namespace Erdos577.JointFinal

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

lemma parallel_factor_geometry (v : Quadrilateral G) (x y z w : V)
    (hx : x ∉ v.support) (hy : y ∉ v.support) (hz : z ∉ v.support) (hw : w ∉ v.support)
    (hcard : ({x, y, z, w} : Finset V).card = 4) :
    Disjoint ({x, v 0, y, v 1} : Finset V) {z, v 2, v 3, w} ∧
      ({x, v 0, y, v 1} : Finset V) ∪ {z, v 2, v 3, w} = {x, y, z, w} ∪ v.support := by
  obtain ⟨_, hxz, hxw, hyz, hyw, _⟩ := JointCore.four_distinct hcard
  have hm (i : Fin 4) : v i ∈ v.support := (v.mem_support _).mpr ⟨i, rfl⟩
  have hxv (i : Fin 4) : x ≠ v i := fun he ↦ hx (he.symm ▸ hm i)
  have hyv (i : Fin 4) : y ≠ v i := fun he ↦ hy (he.symm ▸ hm i)
  have hvz (i : Fin 4) : v i ≠ z := fun he ↦ hz (he ▸ hm i)
  have hvw (i : Fin 4) : v i ≠ w := fun he ↦ hw (he ▸ hm i)
  have hinj : Function.Injective (v : Fin 4 → V) := v.injective
  refine ⟨?_, ?_⟩
  · simp only [disjoint_insert_left, disjoint_singleton_left, mem_insert, mem_singleton, not_or]
    exact ⟨⟨hxz, hxv 2, hxv 3, hxw⟩,
      ⟨hvz 0, hinj.ne (by decide), hinj.ne (by decide), hvw 0⟩,
      ⟨hyz, hyv 2, hyv 3, hyw⟩,
      ⟨hvz 1, hinj.ne (by decide), hinj.ne (by decide), hvw 1⟩⟩
  · rw [v.support_four]
    ext u
    simp only [mem_union, mem_insert, mem_singleton]
    tauto

variable [DecidableRel G.Adj]

theorem FinalRows.parallel_factor_false {v : Quadrilateral G} {x y z w : V}
    (h : FinalRows v x y z w) (hx0 : G.Adj x (v 0)) (hx1 : G.Adj x (v 1))
    (hy0 : G.Adj y (v 0)) (hy1 : G.Adj y (v 1)) (hw3 : G.Adj w (v 3)) : False := by
  obtain ⟨hxy, _, _, _, _, _⟩ := JointCore.four_distinct h.distinct
  have hm (i : Fin 4) : v i ∈ v.support := (v.mem_support _).mpr ⟨i, rfl⟩
  have hfirst : QuadOn G {x, v 0, y, v 1} := QuadOn.of_vertices hxy
    (v.injective.ne (by decide : (0 : Fin 4) ≠ 1)) hx0 hy0.symm hy1 hx1.symm
  have hsecond : QuadOn G {z, v 2, v 3, w} := QuadOn.of_vertices
    (fun he ↦ h.z_out (he.symm ▸ hm 3)) (fun he ↦ h.w_out (he ▸ hm 2))
    (h.three 2 (by decide)) (v.adjacent 2) hw3.symm h.pair_edge.symm
  obtain ⟨hd, he⟩ := parallel_factor_geometry v x y z w h.x_out h.y_out h.z_out h.w_out h.distinct
  have hf : LocalFactor G (({x, v 0, y, v 1} : Finset V) ∪ {z, v 2, v 3, w}) :=
    ⟨_, subset_union_left, hfirst, (union_sdiff_cancel_left hd).symm ▸ hsecond⟩
  exact h.factor (he ▸ hf)

end Erdos577.JointFinal
