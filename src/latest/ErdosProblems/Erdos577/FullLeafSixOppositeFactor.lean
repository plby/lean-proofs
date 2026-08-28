import ErdosProblems.Erdos577.FullLeafSixColumnsExact

/-! The two quadrilaterals in the opposite-pair case partition the exact eight vertices. -/

namespace Erdos577.FullLeafSix

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

lemma factor_of_two_quads {a b : Finset V} (ha : QuadOn G a) (hb : QuadOn G b)
    (hd : Disjoint a b) : LocalFactor G (a ∪ b) := by
  refine ⟨a, subset_union_left, ha, ?_⟩
  have he : (a ∪ b) \ a = b := by
    ext v
    simp only [mem_sdiff, mem_union]
    constructor
    · rintro ⟨h | h, hn⟩
      · exact False.elim (hn h)
      · exact h
    · intro hv
      exact ⟨Or.inr hv, fun hh ↦ disjoint_left.mp hd hh hv⟩
  rw [he]
  exact hb

lemma opposite_two_factor (q : Quadrilateral G) {x v w z : V}
    (hd : Disjoint ({v, w, z} : Finset V) q.support)
    (hx : x ∉ ({v, w, z} : Finset V) ∪ q.support)
    (hvw : v ≠ w) (hvz : v ≠ z)
    (hwz : G.Adj w z) (h13 : G.Adj (q 1) (q 3))
    (hx0 : G.Adj x (q 0)) (hx2 : G.Adj x (q 2))
    (hv0 : G.Adj v (q 0)) (hv2 : G.Adj v (q 2))
    (hw1 : G.Adj w (q 1)) (hz3 : G.Adj z (q 3)) :
    LocalFactor G (insert x ({v, w, z} ∪ q.support)) := by
  have hm (i : Fin 4) : q i ∈ q.support := (q.mem_support _).mpr ⟨i, rfl⟩
  have hout (r : V) (hr : r ∈ ({v, w, z} : Finset V)) (i : Fin 4) : r ≠ q i :=
    fun he ↦ disjoint_left.mp hd hr (he.symm ▸ hm i)
  have hxq (i : Fin 4) : x ≠ q i := fun he ↦ hx (mem_union_right _ (he.symm ▸ hm i))
  have hxv : x ≠ v := fun he ↦ hx (mem_union_left _ (he.symm ▸ by simp))
  have hxw : x ≠ w := fun he ↦ hx (mem_union_left _ (he.symm ▸ by simp))
  have hxz : x ≠ z := fun he ↦ hx (mem_union_left _ (he.symm ▸ by simp))
  have hfirst : QuadOn G {x, q 0, v, q 2} :=
    QuadOn.of_vertices hxv (q.injective.ne (by decide : (0 : Fin 4) ≠ 2))
      hx0 hv0.symm hv2 hx2.symm
  have hsecond : QuadOn G {w, z, q 3, q 1} :=
    QuadOn.of_vertices (hout w (by simp) 3) (hout z (by simp) 1)
      hwz hz3 h13.symm hw1.symm
  have hdis : Disjoint ({x, q 0, v, q 2} : Finset V) {w, z, q 3, q 1} := by
    simp only [disjoint_insert_left, disjoint_singleton_left, mem_insert, mem_singleton, not_or]
    exact ⟨⟨hxw, hxz, hxq 3, hxq 1⟩,
      ⟨(hout w (by simp) 0).symm, (hout z (by simp) 0).symm,
        q.injective.ne (by decide), q.injective.ne (by decide)⟩,
      ⟨hvw, hvz, hout v (by simp) 3, hout v (by simp) 1⟩,
      ⟨(hout w (by simp) 2).symm, (hout z (by simp) 2).symm,
        q.injective.ne (by decide), q.injective.ne (by decide)⟩⟩
  have hf := factor_of_two_quads hfirst hsecond hdis
  have he : ({x, q 0, v, q 2} ∪ {w, z, q 3, q 1} : Finset V) =
      insert x ({v, w, z} ∪ q.support) := by
    rw [q.support_four]
    ext r
    simp only [mem_union, mem_insert, mem_singleton]
    tauto
  exact he ▸ hf

end Erdos577.FullLeafSix
