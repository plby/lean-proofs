import ErdosProblems.Erdos577.TripleCoreSourcePatterns

/-! Actual copies of the twelve source graphs, with exact block diagonals and fixed paw labels. -/

namespace Erdos577.TripleCorePatterns

open Finset

lemma cross_adj (tag : Fin 12) (i j : Fin 4) :
    (graph tag).Adj (Fin.castAdd 4 i) (Fin.natAdd 4 j) ↔ (rows tag i).testBit j.val = true := by
  have hall : ∀ tag : Fin 12, ∀ i j : Fin 4,
      (graph tag).Adj (Fin.castAdd 4 i) (Fin.natAdd 4 j) ↔ (rows tag i).testBit j.val = true := by
    decide +kernel
  exact hall tag i j

lemma right_adj (tag : Fin 12) (i j : Fin 4) :
    (graph tag).Adj (Fin.natAdd 4 i) (Fin.natAdd 4 j) ↔
      (PawModel.graph (diagonal tag) 0).Adj (Fin.natAdd 4 i) (Fin.natAdd 4 j) := by
  have hall : ∀ tag : Fin 12, ∀ i j : Fin 4,
      (graph tag).Adj (Fin.natAdd 4 i) (Fin.natAdd 4 j) ↔
        (PawModel.graph (diagonal tag) 0).Adj (Fin.natAdd 4 i) (Fin.natAdd 4 j) := by
    decide +kernel
  exact hall tag i j

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableEq V] in
lemma SourcePattern.diagonal_eq {tag : Fin 12} {p : Paw G} {q : Quadrilateral G}
    (h : SourcePattern tag p q) : Unattached.diagonal q = diagonal tag := by
  have h0 := (Unattached.diagonal_first q).trans h.1
  have h1 := (Unattached.diagonal_second q).trans h.2.1
  have hall : ∀ d e : Fin 4,
      (d.val.testBit 0 = true ↔ e.val.testBit 0 = true) →
      (d.val.testBit 1 = true ↔ e.val.testBit 1 = true) → d = e := by decide +kernel
  exact hall _ _ h0 h1

def SourcePattern.copy {tag : Fin 12} {p : Paw G} {q : Quadrilateral G}
    (h : SourcePattern tag p q) (hd : Disjoint p.support q.support) : (graph tag).Copy G :=
  PawEncoding.copyWithDiagonalOfRows p q hd (diagonal tag)
    (by rw [h.diagonal_eq]; exact Nat.and_self _)
    ⟨mask tag, by fin_cases tag <;> decide +kernel⟩ (by
      intro i j hij
      rw [mask_bit] at hij
      by_cases hi : i = 0
      · subst i
        change (0 : ℕ).testBit j.val = true at hij
        simp at hij
      · exact (h.2.2 i j hi).mpr hij)

lemma SourcePattern.copy_apply {tag : Fin 12} {p : Paw G} {q : Quadrilateral G}
    (h : SourcePattern tag p q) (hd : Disjoint p.support q.support) (i : Fin 8) :
    h.copy hd i = PawEncoding.labeling p q hd i := rfl

lemma SourcePattern.copy_block {tag : Fin 12} {p : Paw G} {q : Quadrilateral G}
    (h : SourcePattern tag p q) (hd : Disjoint p.support q.support) :
    block.image (h.copy hd) = q.support := by
  have he : block = (univ : Finset (Fin 4)).image (Fin.natAdd 4) := by decide +kernel
  rw [he, image_image]
  simp only [Function.comp_def, h.copy_apply, PawEncoding.labeling_right]
  rfl

lemma SourcePattern.copy_core {tag : Fin 12} {p : Paw G} {q : Quadrilateral G}
    (h : SourcePattern tag p q) (hd : Disjoint p.support q.support) :
    core.image (h.copy hd) = p.triangle ∪ q.support := by
  have he : core = (univ : Finset (Fin 8)).erase 0 := by decide +kernel
  have hx : p.leaf ∉ p.triangle ∪ q.support := by
    rw [mem_union, not_or]
    exact ⟨p.leaf_not_mem_triangle,
      fun hh ↦ disjoint_left.mp hd (p.support_eq ▸ mem_insert_self _ _) hh⟩
  rw [he]
  change (univ.erase 0).image (PawEncoding.labeling p q hd) = _
  rw [image_erase (PawEncoding.labeling p q hd).injective]
  change (univ.image (PawEncoding.labeling p q hd)).erase p.leaf = _
  rw [PawEncoding.labeling_image, p.support_eq, insert_union, erase_insert hx]

lemma SourcePattern.copy_paw {tag : Fin 12} {p : Paw G} {q : Quadrilateral G}
    (h : SourcePattern tag p q) (hd : Disjoint p.support q.support) :
    (paw tag).image (h.copy hd) = p := by
  have he : ((paw tag).image (h.copy hd)).vertices = p.vertices := by
    ext i
    fin_cases i <;> rfl
  cases hp : (paw tag).image (h.copy hd) with
  | mk vertices pendant edge12 edge13 edge23 =>
    rw [hp] at he
    cases p
    cases he
    rfl

lemma SourcePattern.copy_block_score {tag : Fin 12} {p : Paw G} {q : Quadrilateral G}
    (h : SourcePattern tag p q) (hd : Disjoint p.support q.support) :
    edgeCount G (block.image (h.copy hd)) = edgeCount (graph tag) block := by
  rw [h.copy_block, old_score, ← Unattached.oldEdges_diagonal, h.diagonal_eq]

end Erdos577.TripleCorePatterns
