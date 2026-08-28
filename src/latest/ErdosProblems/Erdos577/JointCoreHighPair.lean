import ErdosProblems.Erdos577.JointCoreDenseQuad
import ErdosProblems.Erdos577.JointCoreLocal
import ErdosProblems.Erdos577.DenseTriangle

/-! The distinguished pair with a complete primary complement at eleven triangle contacts. -/

namespace Erdos577.JointCore

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem high_core_pair (p : Paw G) {a : Finset V} (ha : G.IsNClique 4 a)
    (hd : Disjoint p.support a) (hhigh : 11 ≤ contacts G p.triangle a) :
    ∃ q : Quadrilateral G, q.support = a ∧
      G.Adj p.center (q 2) ∧ G.Adj p.center (q 3) ∧ G.Adj (q 2) (q 3) ∧
      G.IsNClique 4 ((p.triangle ∪ a) \ {p.center, q 2, q 3}) ∧
      QuadOn G ((p.triangle ∪ a) \ {q 2, p.center, p.vertices 2}) ∧
      QuadOn G ((p.triangle ∪ a) \ {q 3, p.center, p.vertices 2}) ∧
      QuadOn G ((p.triangle ∪ a) \ {q 2, q 3, p.vertices 2}) := by
  have hTA : Disjoint p.triangle a := hd.mono_left (p.support_eq ▸ subset_insert _ _)
  obtain ⟨b1, b2, b3, b4, hab, hr1, _, hr3, hcl, _⟩ :=
    dense_triangle_clique_label p.triangle_clique ha hTA hhigh p.center_mem_triangle
  have hc4 : ({b1, b2, b3, b4} : Finset V).card = 4 := hab ▸ ha.card_eq
  obtain ⟨h12, h13, h14, h23, h24, h34⟩ := four_distinct hc4
  have hb1 : b1 ∈ a := by rw [hab]; simp
  have hb2 : b2 ∈ a := by rw [hab]; simp
  have hb3 : b3 ∈ a := by rw [hab]; simp
  have hb4 : b4 ∈ a := by rw [hab]; simp
  let e := fourTuple b2 b4 b1 b3 h24 h12.symm h23 h14.symm h34.symm h13
  have hem (i : Fin 4) : e i ∈ a := by fin_cases i <;> assumption
  let q := Quadrilateral.ofEdges e (fun i ↦ ha.isClique (hem i) (hem (i + 1))
    (e.injective.ne (by fin_cases i <;> decide)))
  have hq : q.support = a := by
    change tupleSupport e = a
    rw [fourTuple_support, hab]
    ext v
    simp only [mem_insert, mem_singleton]
    tauto
  have hrA : p.center ∉ a := fun hh ↦ disjoint_left.mp hTA p.center_mem_triangle hh
  have h1T : b1 ∉ p.triangle := fun hh ↦ disjoint_left.mp hTA hh hb1
  have h3T : b3 ∉ p.triangle := fun hh ↦ disjoint_left.mp hTA hh hb3
  have hsT : p.triangle \ {p.center, b1, b3} = p.triangle.erase p.center := by
    have he : ({p.center, b1, b3} : Finset V) = {b1, b3, p.center} := by
      ext v
      simp only [mem_insert, mem_singleton]
      tauto
    rw [he, sdiff_insert_of_notMem h1T, sdiff_insert_of_notMem h3T, sdiff_singleton_eq_erase]
  have hsA : a \ {p.center, b1, b3} = {b4, b2} := by
    rw [sdiff_insert_of_notMem hrA, hab]
    ext v
    simp only [mem_sdiff, mem_insert, mem_singleton]
    aesop
  have he : (p.triangle ∪ a) \ {p.center, b1, b3} = p.triangle.erase p.center ∪ {b4, b2} := by
    rw [union_sdiff_distrib, hsT, hsA]
  have hprimary : G.IsNClique 4 ((p.triangle ∪ a) \ {p.center, b1, b3}) := by
    refine ⟨he ▸ hcl, ?_⟩
    have hsub : ({p.center, b1, b3} : Finset V) ⊆ p.triangle ∪ a :=
      insert_subset (mem_union_left _ p.center_mem_triangle)
        (insert_subset (mem_union_right _ hb1) (singleton_subset_iff.mpr (mem_union_right _ hb3)))
    rw [card_sdiff_of_subset hsub, card_union_of_disjoint hTA, p.triangle_clique.card_eq,
      ha.card_eq, card_triple_eq_three_iff.mpr
        ⟨(fun (hh : p.center = b1) ↦ hrA (hh.symm ▸ hb1)),
          (fun (hh : p.center = b3) ↦ hrA (hh.symm ▸ hb3)), h13⟩]
  have h2T : p.vertices 2 ∈ p.triangle := by simp [Paw.triangle]
  have h1r : b1 ≠ p.center := fun hh ↦ hrA (hh ▸ hb1)
  have h3r : b3 ≠ p.center := fun hh ↦ hrA (hh ▸ hb3)
  have h1b : b1 ≠ p.vertices 2 := fun hh ↦ disjoint_left.mp hTA h2T (hh ▸ hb1)
  have h3b : b3 ≠ p.vertices 2 := fun hh ↦ disjoint_left.mp hTA h2T (hh ▸ hb3)
  have hrb : p.center ≠ p.vertices 2 := p.vertices.injective.ne (by decide : (1 : Fin 4) ≠ 2)
  have hs1 := dense_complement_triple p.triangle_clique ha hTA hhigh b1 p.center (p.vertices 2)
    (mem_union_right _ hb1) (mem_union_left _ p.center_mem_triangle) (mem_union_left _ h2T)
    h1r h1b hrb
  have hs2 := dense_complement_triple p.triangle_clique ha hTA hhigh b3 p.center (p.vertices 2)
    (mem_union_right _ hb3) (mem_union_left _ p.center_mem_triangle) (mem_union_left _ h2T)
    h3r h3b hrb
  have ht := dense_complement_triple p.triangle_clique ha hTA hhigh b1 b3 (p.vertices 2)
    (mem_union_right _ hb1) (mem_union_right _ hb3) (mem_union_left _ h2T) h13 h1b h3b
  exact ⟨q, hq, hr1, hr3, ha.isClique hb1 hb3 h13, hprimary, hs1, hs2, ht⟩

end Erdos577.JointCore
