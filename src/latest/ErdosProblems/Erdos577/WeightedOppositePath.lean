import ErdosProblems.Erdos577.WeightedOppositeUpper
import ErdosProblems.Erdos577.PairReplacements
import ErdosProblems.Erdos577.WeightedRows

/-! The exposed path and complementary block in patterns (16) and (17). -/

namespace Erdos577.WeightedOpposite

open Finset

def pathSet : Finset (Fin 8) := {0, 1, 3, 5}

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

def path (seventeen : Bool) (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (h : Rows seventeen p q) : FourPath G where
  vertices := (⟨![0, 1, 3, 5], by decide +kernel⟩ : Fin 4 ↪ Fin 8).trans
    (PawEncoding.labeling p q hd)
  adjacent := by
    intro i
    fin_cases i
    · exact p.pendant
    · exact p.edge13
    · exact (h.2.2.2 1).mpr (by cases seventeen <;> decide)

lemma path_support (seventeen : Bool) (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (h : Rows seventeen p q) :
    (path seventeen p q hd h).support = {p.vertices 0, p.vertices 1, p.vertices 3, q 1} := by
  have hu : (univ : Finset (Fin 4)) = {0, 1, 2, 3} := by decide
  rw [FourPath.support, hu]
  simp only [image_insert, image_singleton]
  rfl

lemma path_support_image (seventeen : Bool) (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (h : Rows seventeen p q) :
    (path seventeen p q hd h).support = pathSet.image (PawEncoding.labeling p q hd) := by
  rw [path_support]
  simp only [pathSet, image_insert, image_singleton]
  rfl

lemma path_subset (seventeen : Bool) (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (h : Rows seventeen p q) :
    (path seventeen p q hd h).support ⊆ p.support ∪ q.support := by
  rw [path_support_image, ← PawEncoding.labeling_image p q hd]
  exact image_subset_image (subset_univ _)

def newQuad (seventeen : Bool) (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (h : Rows seventeen p q) : Quadrilateral G :=
  Quadrilateral.ofEdges
    ((⟨![2, 4, 7, 6], by decide +kernel⟩ : Fin 4 ↪ Fin 8).trans
      (PawEncoding.labeling p q hd)) (by
    intro i
    fin_cases i
    · exact (h.2.2.1 0).mpr (by cases seventeen <;> decide)
    · exact (q.adjacent 3).symm
    · exact (q.adjacent 2).symm
    · exact ((h.2.2.1 2).mpr (by decide)).symm)

lemma newQuad_support (seventeen : Bool) (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (h : Rows seventeen p q) :
    (newQuad seventeen p q hd h).support = {p.vertices 2, q 0, q 3, q 2} := by
  have hu : (univ : Finset (Fin 4)) = {0, 1, 2, 3} := by decide
  rw [Quadrilateral.support, hu]
  simp only [image_insert, image_singleton]
  rfl

lemma complement_eq_newQuad (seventeen : Bool) (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (h : Rows seventeen p q) :
    (p.support ∪ q.support) \ (path seventeen p q hd h).support =
      (newQuad seventeen p q hd h).support := by
  let e := PawEncoding.labeling p q hd
  have hinj : Function.Injective (e : Fin 8 → V) := e.injective
  rw [path_support_image, ← PawEncoding.labeling_image p q hd]
  change univ.image e \ pathSet.image e = _
  rw [← image_sdiff _ _ hinj]
  have he : (univ : Finset (Fin 8)) \ pathSet = {2, 4, 7, 6} := by decide
  rw [he, newQuad_support]
  simp only [image_insert, image_singleton]
  rfl

lemma newQuad_support_insert (seventeen : Bool) (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (h : Rows seventeen p q) :
    (newQuad seventeen p q hd h).support = insert (p.vertices 2) (q.support.erase (q 1)) := by
  have hinj : Function.Injective (q : Fin 4 → V) := q.injective
  rw [newQuad_support, Quadrilateral.support, ← image_erase hinj]
  have he : (univ : Finset (Fin 4)).erase 1 = {0, 3, 2} := by decide
  rw [he]
  simp only [image_insert, image_singleton]

variable [DecidableRel G.Adj]

lemma Rows.old_low_degree (seventeen : Bool) (p : Paw G) (q : Quadrilateral G)
    (h : Rows seventeen p q) : degreeIn G (q 1) q.support = 2 := by
  rw [q.degreeIn_eq]
  change 2 + (if G.Adj (q 1) (q 3) then 1 else 0) = 2
  rw [if_neg h.1]

lemma Rows.new_row_degree (seventeen : Bool) (p : Paw G) (q : Quadrilateral G)
    (h : Rows seventeen p q) : degreeIn G (p.vertices 2) (q.support.erase (q 1)) = 3 := by
  have hrow := h.2.2.1.degree p q 2 13
  have hsum : (∑ j : Fin 4, ((13 : ℕ).testBit j.val).toNat) = 3 := by decide +kernel
  rw [hsum] at hrow
  have hn : ¬G.Adj (p.vertices 2) (q 1) := by
    intro he
    exact (by decide : ((13 : ℕ).testBit 1 = true) → False) ((h.2.2.1 1).mp he)
  have hid := degreeIn_erase_add G (p.vertices 2) (q 1) ((q.mem_support _).mpr ⟨1, rfl⟩)
  rw [if_neg hn, hrow] at hid
  omega

lemma path_gain (seventeen : Bool) (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (h : Rows seventeen p q) :
    edgeCount G q.support <
      edgeCount G ((p.support ∪ q.support) \ (path seventeen p q hd h).support) := by
  have hout : p.vertices 2 ∉ q.support := by
    intro he
    exact disjoint_left.mp hd ((mem_tupleSupport p.vertices _).mpr ⟨2, rfl⟩) he
  have hid := edgeCount_replace G (q 1) (p.vertices 2) ((q.mem_support _).mpr ⟨1, rfl⟩) hout
  rw [h.old_low_degree seventeen p q, h.new_row_degree seventeen p q] at hid
  rw [complement_eq_newQuad, newQuad_support_insert]
  omega

end Erdos577.WeightedOpposite
