import ErdosProblems.Erdos577.WeightedOppositePath
import ErdosProblems.Erdos577.TerminalReplacements

/-! Re-expose the opposite old vertex while preserving both feasible-chain scores. -/

namespace Erdos577.WeightedOpposite

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

def terminalQuad (seventeen : Bool) (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (h : Rows seventeen p q) : Quadrilateral G :=
  Quadrilateral.ofEdges
    ((⟨![0, 4, 5, 6], by decide +kernel⟩ : Fin 4 ↪ Fin 8).trans
      (PawEncoding.labeling p q hd)) (by
    intro i
    fin_cases i
    · exact (h.2.1 0).mpr (by decide)
    · exact q.adjacent 0
    · exact q.adjacent 1
    · exact ((h.2.1 2).mpr (by decide)).symm)

lemma terminalQuad_support_image (seventeen : Bool) (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (h : Rows seventeen p q) :
    (terminalQuad seventeen p q hd h).support =
      ({0, 4, 5, 6} : Finset (Fin 8)).image (PawEncoding.labeling p q hd) := by
  have hu : (univ : Finset (Fin 4)) = {0, 1, 2, 3} := by decide
  rw [Quadrilateral.support, hu]
  simp only [image_insert, image_singleton]
  rfl

lemma terminal_remainder_image (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) :
    insert (q 3) p.triangle =
      ({7, 1, 2, 3} : Finset (Fin 8)).image (PawEncoding.labeling p q hd) := by
  simp only [Paw.triangle, image_insert, image_singleton]
  rfl

lemma terminalQuad_support_insert (seventeen : Bool) (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (h : Rows seventeen p q) :
    (terminalQuad seventeen p q hd h).support = insert p.leaf (q.support.erase (q 3)) := by
  have hinj : Function.Injective (q : Fin 4 → V) := q.injective
  rw [terminalQuad_support_image, Quadrilateral.support, ← image_erase hinj]
  have he : (univ : Finset (Fin 4)).erase 3 = {0, 1, 2} := by decide
  rw [he]
  simp only [image_insert, image_singleton]
  rfl

def terminalLocalChain (seventeen : Bool) (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (h : Rows seventeen p q) :
    LocalChain G (p.support ∪ q.support) where
  terminal := q 3
  triangle := p.triangle
  block := (terminalQuad seventeen p q hd h).support
  triangle_clique := p.triangle_clique
  terminal_not_mem := by
    intro ht
    have hp : q 3 ∈ p.support := by rw [p.support_eq]; exact mem_insert_of_mem ht
    exact disjoint_left.mp hd hp ((q.mem_support _).mpr ⟨3, rfl⟩)
  quad := ⟨terminalQuad seventeen p q hd h, rfl⟩
  disjoint := by
    rw [terminal_remainder_image p q hd, terminalQuad_support_image]
    have hinj : Function.Injective (PawEncoding.labeling p q hd : Fin 8 → V) :=
      (PawEncoding.labeling p q hd).injective
    rw [disjoint_image hinj]
    decide +kernel
  cover := by
    rw [terminal_remainder_image p q hd, terminalQuad_support_image, ← image_union]
    have he : ({7, 1, 2, 3} ∪ {0, 4, 5, 6} : Finset (Fin 8)) = univ := by decide
    rw [he, PawEncoding.labeling_image]

variable [DecidableRel G.Adj]

lemma terminalLocalChain_score (seventeen : Bool) (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (h : Rows seventeen p q) :
    edgeCount G (terminalLocalChain seventeen p q hd h).block = edgeCount G q.support := by
  have hout : p.leaf ∉ q.support := by
    intro he
    exact disjoint_left.mp hd ((mem_tupleSupport p.vertices _).mpr ⟨0, rfl⟩) he
  have hlow : degreeIn G (q 3) q.support = 2 := by
    rw [q.degreeIn_eq]
    change 2 + (if G.Adj (q 3) (q 1) then 1 else 0) = 2
    rw [if_neg (fun he ↦ h.1 he.symm)]
  have hrow := h.2.1.degree p q 0 5
  have hsum : (∑ j : Fin 4, ((5 : ℕ).testBit j.val).toNat) = 2 := by decide +kernel
  rw [hsum] at hrow
  have hnon : ¬G.Adj p.leaf (q 3) := by
    intro he
    exact (by decide : ((5 : ℕ).testBit 3 = true) → False) ((h.2.1 3).mp he)
  have herase := degreeIn_erase_add G p.leaf (q 3) ((q.mem_support _).mpr ⟨3, rfl⟩)
  rw [if_neg hnon] at herase
  have hid := edgeCount_replace G (q 3) p.leaf ((q.mem_support _).mpr ⟨3, rfl⟩) hout
  rw [hlow] at hid
  change edgeCount G (terminalQuad seventeen p q hd h).support = _
  rw [terminalQuad_support_insert]
  change degreeIn G p.leaf q.support = 2 at hrow
  omega

end Erdos577.WeightedOpposite
