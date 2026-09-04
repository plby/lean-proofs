import ErdosProblems.Erdos73.BrickFaceOverlap
import ErdosProblems.Erdos73.RobustSupportFamilies

/-! The rectangular array of brick faces has deletion-one-connected actual union. -/

namespace Erdos73
noncomputable section
open scoped Classical

open SimpleGraph Finset

variable {V : Type*} {G : SimpleGraph V} {c r : ℕ}

def brickFaceColumn (a j : ℕ) : ℕ := 2 * j + (a + 1) % 2

def brickFaceRegion (S : GraphSubdivisionModel (elementaryWall c r) G)
    (i : Fin (r - 1) × Fin (c - 1)) : Finset V :=
  brickFaceSupport S i.1.val (brickFaceColumn i.1.val i.2.val)
    (by have hi := i.1.isLt; omega)
    (by have hi := i.2.isLt; unfold brickFaceColumn; omega)
    (by unfold brickFaceColumn; omega)

theorem brickFaceRegion_robust (S : GraphSubdivisionModel (elementaryWall c r) G)
    (i : Fin (r - 1) × Fin (c - 1)) : DeletionOneConnected G (brickFaceRegion S i) :=
  brickFaceSupport_deletionOneConnected S _ _ _ _ _

theorem brickFaceRegion_horizontal_overlap (S : GraphSubdivisionModel (elementaryWall c r) G)
    (a : Fin (r - 1)) (i j : Fin (c - 1)) (hij : i.val + 1 = j.val) :
    2 ≤ (brickFaceRegion S (a, i) ∩ brickFaceRegion S (a, j)).card := by
  apply brickFaceSupport_horizontal_overlap_of_eq S a.val (brickFaceColumn a.val i.val)
    (brickFaceColumn a.val j.val) _ _ _ _ _
  unfold brickFaceColumn
  omega

theorem brickFaceRegion_vertical_overlap (S : GraphSubdivisionModel (elementaryWall c r) G)
    (a b : Fin (r - 1)) (j : Fin (c - 1)) (hab : a.val + 1 = b.val) :
    2 ≤ (brickFaceRegion S (a, j) ∩ brickFaceRegion S (b, j)).card := by
  apply brickFaceSupport_vertical_overlap_of_eq S a.val b.val (brickFaceColumn a.val j.val)
    (brickFaceColumn b.val j.val) _ _ _ _ _ _ hab
  unfold brickFaceColumn
  omega

theorem brickFaceRegion_adj_overlap (S : GraphSubdivisionModel (elementaryWall c r) G)
    (i j : Fin (r - 1) × Fin (c - 1))
    (hij : (pathGraph (r - 1) □ pathGraph (c - 1)).Adj i j) :
    2 ≤ (brickFaceRegion S i ∩ brickFaceRegion S j).card := by
  rcases i with ⟨a, b⟩
  rcases j with ⟨a', b'⟩
  rcases hij with ⟨ha, hb⟩ | ⟨hb, ha⟩
  · change b = b' at hb
    subst b'
    rcases pathGraph_adj.mp ha with ha | ha
    · exact brickFaceRegion_vertical_overlap S a a' b ha
    · rw [Finset.inter_comm]
      exact brickFaceRegion_vertical_overlap S a' a b ha
  · change a = a' at ha
    subst a'
    rcases pathGraph_adj.mp hb with hb | hb
    · exact brickFaceRegion_horizontal_overlap S a b b' hb
    · rw [Finset.inter_comm]
      exact brickFaceRegion_horizontal_overlap S a b' b hb

theorem brickFaceRegion_union_robust (S : GraphSubdivisionModel (elementaryWall c r) G)
    (hr : 2 ≤ r) (hc : 2 ≤ c) :
    DeletionOneConnected G (Finset.univ.biUnion (brickFaceRegion S)) := by
  have : NeZero (r - 1) := ⟨by omega⟩
  have : NeZero (c - 1) := ⟨by omega⟩
  have hconn : (pathGraph (r - 1) □ pathGraph (c - 1)).Connected :=
    (show (pathGraph (r - 1)).Connected from ⟨pathGraph_preconnected _⟩).boxProd
      (show (pathGraph (c - 1)).Connected from ⟨pathGraph_preconnected _⟩)
  exact deletionOneConnected_biUnion (brickFaceRegion S) (brickFaceRegion_robust S)
    hconn (brickFaceRegion_adj_overlap S)

end
end Erdos73
