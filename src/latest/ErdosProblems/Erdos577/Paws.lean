import ErdosProblems.Erdos577.FourTuples
import ErdosProblems.Erdos577.Attachment

/-! Ordered paws and their realization by the remainder of a strong chain. -/

namespace Erdos577

open Finset

variable {V : Type*} {G : SimpleGraph V}

/-- Positive paw edges; additional edges are allowed. Label 0 is the leaf,
label 1 is the center, and labels 1,2,3 form the triangle. -/
structure Paw (G : SimpleGraph V) where
  vertices : Fin 4 ↪ V
  pendant : G.Adj (vertices 0) (vertices 1)
  edge12 : G.Adj (vertices 1) (vertices 2)
  edge13 : G.Adj (vertices 1) (vertices 3)
  edge23 : G.Adj (vertices 2) (vertices 3)

namespace Paw

def leaf (p : Paw G) : V := p.vertices 0

def center (p : Paw G) : V := p.vertices 1

variable [DecidableEq V]

def triangle (p : Paw G) : Finset V := {p.vertices 1, p.vertices 2, p.vertices 3}

def support (p : Paw G) : Finset V := tupleSupport p.vertices

lemma triangle_clique (p : Paw G) : G.IsNClique 3 p.triangle :=
  SimpleGraph.is3Clique_triple_iff.mpr ⟨p.edge12, p.edge13, p.edge23⟩

lemma leaf_not_mem_triangle (p : Paw G) : p.leaf ∉ p.triangle := by
  simp only [leaf, triangle, mem_insert, mem_singleton, p.vertices.injective.eq_iff]
  decide

lemma support_eq (p : Paw G) : p.support = insert p.leaf p.triangle := by
  ext v
  simp only [support, mem_tupleSupport, leaf, triangle, mem_insert, mem_singleton]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩

lemma card_support (p : Paw G) : p.support.card = 4 := card_tupleSupport p.vertices

lemma center_mem_triangle (p : Paw G) : p.center ∈ p.triangle := by
  simp [center, triangle]

lemma leaf_triangle_degree [DecidableRel G.Adj] (p : Paw G) :
    degreeIn G p.leaf p.triangle = 1 +
      (if G.Adj p.leaf (p.vertices 2) then 1 else 0) +
      (if G.Adj p.leaf (p.vertices 3) then 1 else 0) := by
  have h1 : p.vertices 1 ∉ ({p.vertices 2, p.vertices 3} : Finset V) := by
    simp only [mem_insert, mem_singleton, p.vertices.injective.eq_iff]
    decide
  have h2 : p.vertices 2 ∉ ({p.vertices 3} : Finset V) := by
    simp only [mem_singleton, p.vertices.injective.eq_iff]
    decide
  rw [triangle, degreeIn_insert G _ _ h1, degreeIn_insert G _ _ h2, degreeIn_singleton]
  simp only [leaf, p.pendant, if_true, Nat.add_assoc]

lemma leaf_nonadjacent_of_degree_le_one [DecidableRel G.Adj] (p : Paw G)
    (h : degreeIn G p.leaf p.triangle ≤ 1) :
    ¬G.Adj p.leaf (p.vertices 2) ∧ ¬G.Adj p.leaf (p.vertices 3) := by
  rw [p.leaf_triangle_degree] at h
  constructor <;> intro he <;> simp only [he, if_true] at h <;> omega

omit [DecidableEq V] in
def ofVertices (x a b c : V) (hxa : x ≠ a) (hxb : x ≠ b) (hxc : x ≠ c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (exa : G.Adj x a) (eab : G.Adj a b) (eac : G.Adj a c) (ebc : G.Adj b c) : Paw G where
  vertices := fourTuple x a b c hxa hxb hxc hab hac hbc
  pendant := exa
  edge12 := eab
  edge13 := eac
  edge23 := ebc

lemma exists_of_triangle [DecidableRel G.Adj] {x : V} {t : Finset V}
    (ht : G.IsNClique 3 t) (hx : x ∉ t) (hpos : 0 < degreeIn G x t) :
    ∃ p : Paw G, p.leaf = x ∧ p.triangle = t := by
  obtain ⟨a, ha⟩ := card_pos.mp hpos
  obtain ⟨hat, exa⟩ := mem_filter.mp ha
  have hcard : (t.erase a).card = 2 := by rw [card_erase_of_mem hat, ht.card_eq]
  obtain ⟨b, c, hbc, he⟩ := card_eq_two.mp hcard
  have hb : b ∈ t.erase a := by rw [he]; simp
  have hc : c ∈ t.erase a := by rw [he]; simp
  obtain ⟨hba, hbt⟩ := mem_erase.mp hb
  obtain ⟨hca, hct⟩ := mem_erase.mp hc
  have henum : t = {a, b, c} := by rw [← insert_erase hat, he]
  let p := ofVertices x a b c (fun h ↦ hx (h.symm ▸ hat))
    (fun h ↦ hx (h.symm ▸ hbt)) (fun h ↦ hx (h.symm ▸ hct))
    hba.symm hca.symm hbc exa (ht.isClique hat hbt hba.symm)
    (ht.isClique hat hct hca.symm) (ht.isClique hbt hct hbc)
  exact ⟨p, rfl, henum.symm⟩

end Paw

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

theorem TriangleChain.Strong.exists_paw {c : TriangleChain G} (hc : c.Strong) :
    ∃ p : Paw G, p.leaf = c.terminal ∧ p.triangle = c.triangle ∧ p.support = c.remainder := by
  have hpos : 0 < degreeIn G c.terminal c.triangle := by
    change 0 < c.attachmentScore
    rw [hc.attached]
    decide
  obtain ⟨p, hx, ht⟩ := Paw.exists_of_triangle c.property.triangle_clique
    c.property.terminal_not_mem hpos
  refine ⟨p, hx, ht, ?_⟩
  rw [p.support_eq, hx, ht]
  rfl

end Erdos577
