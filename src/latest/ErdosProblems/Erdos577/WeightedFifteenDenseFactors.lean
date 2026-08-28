import ErdosProblems.Erdos577.WeightedFifteenFactors
import ErdosProblems.Erdos577.PartitionImages

/-! The two explicit twelve-vertex factors needed in the reverse-A case of pattern (15). -/

namespace Erdos577.WeightedFifteen

open Finset

def denseFactorSets (second : Bool) : Fin 3 → Finset (Fin 12) :=
  if second then ![{5, 4, 8, 11}, {1, 0, 9, 10}, {2, 3, 6, 7}]
  else ![{3, 1, 8, 11}, {0, 4, 9, 10}, {2, 5, 6, 7}]

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

def twoBlockLabeling (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (v : Quadrilateral G) (hv : Disjoint (p.support ∪ q.support) v.support) : Fin 12 ↪ V :=
  joinTuples (PawEncoding.labeling p q hd) v.toEmbedding (by
    change Disjoint (univ.image (PawEncoding.labeling p q hd)) v.support
    rw [PawEncoding.labeling_image]
    exact hv)

lemma twoBlockLabeling_image (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (v : Quadrilateral G)
    (hv : Disjoint (p.support ∪ q.support) v.support) :
    univ.image (twoBlockLabeling p q hd v hv) = (p.support ∪ q.support) ∪ v.support := by
  change tupleSupport (twoBlockLabeling p q hd v hv) = _
  rw [twoBlockLabeling, tupleSupport_joinTuples]
  change univ.image (PawEncoding.labeling p q hd) ∪ v.support = _
  rw [PawEncoding.labeling_image]

lemma dense_exception_partition (second : Bool) (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern15 p q)
    (v : Quadrilateral G) (hv : Disjoint (p.support ∪ q.support) v.support)
    (hcl : G.IsNClique 4 v.support)
    (hrows : ∀ j : Fin 4, j ≠ 3 → G.Adj p.leaf (v j) ∧ G.Adj p.center (v j) ∧ G.Adj (q 0) (v j))
    (hbad : G.Adj (if second then q 1 else p.vertices 3) (v 3)) :
    Nonempty (BlockPartition G ((p.support ∪ q.support) ∪ v.support)) := by
  let e := twoBlockLabeling p q hd v hv
  have hne (i j : Fin 12) (hij : i ≠ j) : e i ≠ e j := fun he ↦ hij (e.injective he)
  have hvc (i j : Fin 4) (hij : i ≠ j) : G.Adj (v i) (v j) :=
    hcl.isClique ((v.mem_support _).mpr ⟨i, rfl⟩) ((v.mem_support _).mpr ⟨j, rfl⟩)
      (fun he ↦ hij (v.injective he))
  have hquad (i : Fin 3) : QuadOn G ((denseFactorSets second i).image e) := by
    cases second
    · fin_cases i
      · change QuadOn G (({3, 1, 8, 11} : Finset (Fin 12)).image e)
        simp only [image_insert, image_singleton]
        apply QuadOn.of_vertices (hne 3 8 (by decide)) (hne 1 11 (by decide))
        · exact p.edge13.symm
        · exact (hrows 0 (by decide)).2.1
        · exact hvc 0 3 (by decide)
        · exact hbad.symm
      · change QuadOn G (({0, 4, 9, 10} : Finset (Fin 12)).image e)
        simp only [image_insert, image_singleton]
        apply QuadOn.of_vertices (hne 0 9 (by decide)) (hne 4 10 (by decide))
        · exact (h.2.1 0).mpr (by decide)
        · exact (hrows 1 (by decide)).2.2
        · exact hvc 1 2 (by decide)
        · exact ((hrows 2 (by decide)).1).symm
      · change QuadOn G (({2, 5, 6, 7} : Finset (Fin 12)).image e)
        simp only [image_insert, image_singleton]
        apply QuadOn.of_vertices (hne 2 6 (by decide)) (hne 5 7 (by decide))
        · exact (h.2.2.1 1).mpr (by decide)
        · exact q.adjacent 1
        · exact q.adjacent 2
        · exact ((h.2.2.1 3).mpr (by decide)).symm
    · fin_cases i
      · change QuadOn G (({5, 4, 8, 11} : Finset (Fin 12)).image e)
        simp only [image_insert, image_singleton]
        apply QuadOn.of_vertices (hne 5 8 (by decide)) (hne 4 11 (by decide))
        · exact (q.adjacent 0).symm
        · exact (hrows 0 (by decide)).2.2
        · exact hvc 0 3 (by decide)
        · exact hbad.symm
      · change QuadOn G (({1, 0, 9, 10} : Finset (Fin 12)).image e)
        simp only [image_insert, image_singleton]
        apply QuadOn.of_vertices (hne 1 9 (by decide)) (hne 0 10 (by decide))
        · exact p.pendant.symm
        · exact (hrows 1 (by decide)).1
        · exact hvc 1 2 (by decide)
        · exact ((hrows 2 (by decide)).2.1).symm
      · change QuadOn G (({2, 3, 6, 7} : Finset (Fin 12)).image e)
        simp only [image_insert, image_singleton]
        apply QuadOn.of_vertices (hne 2 6 (by decide)) (hne 3 7 (by decide))
        · exact p.edge23
        · exact (h.2.2.2 2).mpr (by decide)
        · exact q.adjacent 2
        · exact ((h.2.2.1 3).mpr (by decide)).symm
  let part := BlockPartition.threeImages e (denseFactorSets second 0) (denseFactorSets second 1)
    (denseFactorSets second 2) univ (by cases second <;> decide +kernel)
    (by cases second <;> decide +kernel) (by cases second <;> decide +kernel)
    (hquad 0) (hquad 1) (hquad 2)
  exact ⟨twoBlockLabeling_image p q hd v hv ▸ part⟩

variable [Fintype V]

lemma no_dense_exception {c : TriangleChain G} {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern15 p q)
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b) (v : Quadrilateral G) (hv : v.support = a)
    (hcl : G.IsNClique 4 v.support)
    (hrows : ∀ j : Fin 4, j ≠ 3 → G.Adj p.leaf (v j) ∧ G.Adj p.center (v j) ∧ G.Adj (q 0) (v j))
    (second : Bool) : ¬G.Adj (if second then q 1 else p.vertices 3) (v 3) := by
  intro hbad
  have hdis : Disjoint (p.support ∪ q.support) v.support := by
    rw [hp, hq, hv, disjoint_union_left]
    refine ⟨?_, c.property.blocks_disjoint hb ha hab.symm⟩
    apply disjoint_left.mpr
    intro w hw hwa
    exact (mem_sdiff.mp (c.complementPartition.block_subset ha hwa)).2 hw
  obtain ⟨part⟩ := dense_exception_partition second p q hd h v hdis hcl hrows hbad
  rw [hp, hq, hv] at part
  have hbs : ({b, a} : Finset (Finset V)) ⊆ c.blocks := by
    intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · exact hb
    · exact mem_singleton.mp hx ▸ ha
  have he : c.remainder ∪ ({b, a} : Finset (Finset V)).biUnion id =
      (c.remainder ∪ b) ∪ a := by
    simp only [biUnion_insert, singleton_biUnion, id_eq, union_assoc]
  exact hn (c.complementPartition.hasPacking_of_selected_factor hcard {b, a} hbs (he.symm ▸ part))

end Erdos577.WeightedFifteen
