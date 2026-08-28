import ErdosProblems.Erdos577.WeightedThirteenThirdModel
import ErdosProblems.Erdos577.ThreeCrossQuad
import ErdosProblems.Erdos577.FourPartitionImages

/-! The mixed four-cycle factor when the first low meets both adjacent leaf neighbors. -/

namespace Erdos577.WeightedThirteen

open Finset

def adjacentFactorSets : Fin 4 → Finset (Fin 16) :=
  ![{0, 12, 5, 13}, {9, 10, 14, 15}, {2, 4, 7, 6}, {1, 3, 11, 8}]

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma adjacent_leaf_factor (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern13 p q)
    (v : Quadrilateral G) (hv : Disjoint (p.support ∪ q.support) v.support)
    (hcl : G.IsNClique 4 v.support) (hrows : DenseRows p q v)
    (w : Quadrilateral G) (hw : Disjoint ((p.support ∪ q.support) ∪ v.support) w.support)
    (hx0 : G.Adj p.leaf (w 0)) (hx1 : G.Adj p.leaf (w 1))
    (hq0 : G.Adj (q 1) (w 0)) (hq1 : G.Adj (q 1) (w 1))
    (hmiss1 : ¬G.Adj (v 1) (w 0) ∧ ¬G.Adj (v 1) (w 1))
    (hmiss2 : ¬G.Adj (v 2) (w 0) ∧ ¬G.Adj (v 2) (w 1))
    (hthree : 3 ≤ degreeIn G (v 1) w.support + degreeIn G (v 2) w.support) :
    Nonempty (BlockPartition G (((p.support ∪ q.support) ∪ v.support) ∪ w.support)) := by
  let e := ThirdModel.labeling p q hd v hv w hw
  let f := DenseModel.copy p q hd h v hv hcl hrows
  have hne (i j : Fin 16) (hij : i ≠ j) : e i ≠ e j := fun he ↦ hij (e.injective he)
  have hquads (tag : Fin 4) : QuadOn G ((adjacentFactorSets tag).image e) := by
    fin_cases tag
    · change QuadOn G (({0, 12, 5, 13} : Finset (Fin 16)).image e)
      simp only [image_insert, image_singleton]
      exact QuadOn.of_vertices (hne 0 5 (by decide)) (hne 12 13 (by decide))
        hx0 hq0.symm hq1 hx1.symm
    · let r : Fin 4 ↪ V := (⟨![9, 10, 14, 15], by decide +kernel⟩ : Fin 4 ↪ Fin 16).trans e
      have h12 : G.Adj (v 1) (v 2) := v.adjacent 1
      have hh := QuadOn.of_three_cross r h12 (w.adjacent 2) (by
        rw [w.degree_last_pair (v 1) hmiss1.1 hmiss1.2,
          w.degree_last_pair (v 2) hmiss2.1 hmiss2.2] at hthree
        change 3 ≤ (if G.Adj (v 1) (w 2) then 1 else 0) +
          (if G.Adj (v 1) (w 3) then 1 else 0) + (if G.Adj (v 2) (w 2) then 1 else 0) +
          (if G.Adj (v 2) (w 3) then 1 else 0)
        omega)
      change QuadOn G (({9, 10, 14, 15} : Finset (Fin 16)).image e)
      simp only [image_insert, image_singleton]
      exact hh
    · have hh : QuadOn DenseModel.graph ({2, 4, 7, 6} : Finset (Fin 12)) :=
        QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
      have hi := hh.image f
      change QuadOn G (({2, 4, 7, 6} : Finset (Fin 16)).image e)
      simp only [image_insert, image_singleton] at hi ⊢
      change QuadOn G {p.vertices 2, q 0, q 3, q 2} at hi ⊢
      exact hi
    · have hh : QuadOn DenseModel.graph ({1, 3, 11, 8} : Finset (Fin 12)) :=
        QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
      have hi := hh.image f
      change QuadOn G (({1, 3, 11, 8} : Finset (Fin 16)).image e)
      simp only [image_insert, image_singleton] at hi ⊢
      change QuadOn G {p.vertices 1, p.vertices 3, v 3, v 0} at hi ⊢
      exact hi
  let part := BlockPartition.fourImages e (adjacentFactorSets 0) (adjacentFactorSets 1)
    (adjacentFactorSets 2) (adjacentFactorSets 3) univ
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (hquads 0) (hquads 1) (hquads 2) (hquads 3)
  exact ⟨ThirdModel.labeling_image p q hd v hv w hw ▸ part⟩

end Erdos577.WeightedThirteen
