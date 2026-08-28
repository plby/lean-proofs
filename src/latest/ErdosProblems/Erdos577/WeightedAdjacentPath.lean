import ErdosProblems.Erdos577.WeightedAdjacentUpper
import ErdosProblems.Erdos577.PairReplacements

/-! The explicit exposed path and complementary complete block in patterns (18) and (20). -/

namespace Erdos577.WeightedAdjacent

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

def path (twenty : Bool) (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (h : Rows twenty p q) : FourPath G where
  vertices := (⟨![5, 0, 1, 3], by decide +kernel⟩ : Fin 4 ↪ Fin 8).trans
    (PawEncoding.labeling p q hd)
  adjacent := by
    intro i
    fin_cases i
    · exact ((h.2.1 1).mpr (by decide)).symm
    · exact p.pendant
    · exact p.edge13

lemma path_support (twenty : Bool) (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (h : Rows twenty p q) :
    (path twenty p q hd h).support = {q 1, p.vertices 0, p.vertices 1, p.vertices 3} := by
  have hu : (univ : Finset (Fin 4)) = {0, 1, 2, 3} := by decide
  rw [FourPath.support, hu]
  simp only [image_insert, image_singleton]
  rfl

lemma path_support_image (twenty : Bool) (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (h : Rows twenty p q) :
    (path twenty p q hd h).support = pathSet.image (PawEncoding.labeling p q hd) := by
  rw [path_support]
  simp only [pathSet, image_insert, image_singleton]
  rfl

lemma path_subset (twenty : Bool) (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (h : Rows twenty p q) :
    (path twenty p q hd h).support ⊆ p.support ∪ q.support := by
  rw [path_support_image, ← PawEncoding.labeling_image p q hd]
  exact image_subset_image (subset_univ _)

def newQuad (twenty : Bool) (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (h : Rows twenty p q) : Quadrilateral G :=
  Quadrilateral.ofEdges
    ((⟨![2, 4, 6, 7], by decide +kernel⟩ : Fin 4 ↪ Fin 8).trans
      (PawEncoding.labeling p q hd)) (by
    intro i
    fin_cases i
    · exact (h.2.2.1 0).mpr (by cases twenty <;> decide)
    · exact h.1.1
    · exact q.adjacent 2
    · exact ((h.2.2.1 3).mpr (by cases twenty <;> decide)).symm)

lemma newQuad_support (twenty : Bool) (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (h : Rows twenty p q) :
    (newQuad twenty p q hd h).support = {p.vertices 2, q 0, q 2, q 3} := by
  have hu : (univ : Finset (Fin 4)) = {0, 1, 2, 3} := by decide
  rw [Quadrilateral.support, hu]
  simp only [image_insert, image_singleton]
  rfl

lemma complement_eq_newQuad (twenty : Bool) (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (h : Rows twenty p q) :
    (p.support ∪ q.support) \ (path twenty p q hd h).support =
      (newQuad twenty p q hd h).support := by
  let e := PawEncoding.labeling p q hd
  have hinj : Function.Injective (e : Fin 8 → V) := e.injective
  rw [path_support_image, ← PawEncoding.labeling_image p q hd]
  change univ.image e \ pathSet.image e = _
  rw [← image_sdiff _ _ hinj]
  have he : (univ : Finset (Fin 8)) \ pathSet = {2, 4, 6, 7} := by decide
  rw [he, newQuad_support]
  simp only [image_insert, image_singleton]
  rfl

lemma newQuad_clique (twenty : Bool) (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (h : Rows twenty p q) :
    G.IsNClique 4 (newQuad twenty p q hd h).support := by
  apply Quadrilateral.clique_of_diagonals
  · exact (h.2.2.1 2).mpr (by cases twenty <;> decide)
  · exact (q.adjacent 3).symm

variable [DecidableRel G.Adj]

lemma Rows.old_score (twenty : Bool) (p : Paw G) (q : Quadrilateral G)
    (h : Rows twenty p q) : edgeCount G q.support = 5 := by
  have hdiag : Unattached.diagonal q = 1 := by
    simp [Unattached.diagonal, h.1.1, h.1.2]
  rw [← Unattached.oldEdges_diagonal q, hdiag]
  decide +kernel

lemma path_gain (twenty : Bool) (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (h : Rows twenty p q) :
    edgeCount G q.support <
      edgeCount G ((p.support ∪ q.support) \ (path twenty p q hd h).support) := by
  rw [complement_eq_newQuad, h.old_score twenty p q,
    edgeCount_clique (newQuad_clique twenty p q hd h).isClique, Quadrilateral.card_support]
  decide +kernel

end Erdos577.WeightedAdjacent
