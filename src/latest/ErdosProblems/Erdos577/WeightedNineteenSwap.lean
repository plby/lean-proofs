import ErdosProblems.Erdos577.WeightedNineteenPaths
import ErdosProblems.Erdos577.LocalChainSupport

/-! A genuine local change of presentation interchanges the two paths in pattern (19). -/

namespace Erdos577.WeightedNineteen

open Finset

def coreSwappedChain : LocalChain graph univ where
  terminal := 1
  triangle := {0, 4, 5}
  block := {2, 3, 7, 6}
  triangle_clique := by decide +kernel
  terminal_not_mem := by decide +kernel
  quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  disjoint := by decide +kernel
  cover := by decide +kernel

lemma coreSwappedChain_score : edgeCount graph coreSwappedChain.block = 4 := by decide +kernel

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

def swappedPaw (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (h : WeightedPawBlock.Pattern19 p q) : Paw G where
  vertices := (⟨![1, 0, 4, 5], by decide +kernel⟩ : Fin 4 ↪ Fin 8).trans
    (PawEncoding.labeling p q hd)
  pendant := by
    change G.Adj (p.vertices 1) (p.vertices 0)
    exact p.pendant.symm
  edge12 := by
    change G.Adj (p.vertices 0) (q 0)
    exact (h.2.2.1 0).mpr (by decide)
  edge13 := by
    change G.Adj (p.vertices 0) (q 1)
    exact (h.2.2.1 1).mpr (by decide)
  edge23 := by
    change G.Adj (q 0) (q 1)
    exact q.adjacent 0

def swappedQuad (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (h : WeightedPawBlock.Pattern19 p q) : Quadrilateral G :=
  (coreCopy p q hd h).comp (Quadrilateral.ofEdges
    (⟨![2, 3, 7, 6], by decide +kernel⟩ : Fin 4 ↪ Fin 8) (by decide +kernel))

def swappedChain (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (h : WeightedPawBlock.Pattern19 p q) : LocalChain G (p.support ∪ q.support) :=
  (coreSwappedChain.image (coreCopy p q hd h)).withSupport (coreCopy_image p q hd h)

omit [DecidableRel G.Adj] in
lemma swappedPaw_support (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (h : WeightedPawBlock.Pattern19 p q) :
    (swappedPaw p q hd h).support = {p.vertices 1, p.vertices 0, q 0, q 1} := by
  have hu : (univ : Finset (Fin 4)) = {0, 1, 2, 3} := by decide
  rw [Paw.support, tupleSupport, hu]
  simp only [image_insert, image_singleton]
  rfl

lemma swappedQuad_support (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (h : WeightedPawBlock.Pattern19 p q) :
    (swappedQuad p q hd h).support = {p.vertices 2, p.vertices 3, q 3, q 2} := by
  have hu : (univ : Finset (Fin 4)) = {0, 1, 2, 3} := by decide
  rw [Quadrilateral.support, hu]
  simp only [image_insert, image_singleton]
  rfl

lemma swappedPaw_remainder (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (h : WeightedPawBlock.Pattern19 p q) :
    (swappedPaw p q hd h).support = (swappedChain p q hd h).remainder := by
  rw [swappedPaw_support]
  change _ = insert (coreCopy p q hd h 1) (({0, 4, 5} : Finset (Fin 8)).image (coreCopy p q hd h))
  simp only [image_insert, image_singleton]
  rfl

lemma swappedQuad_block (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (h : WeightedPawBlock.Pattern19 p q) :
    (swappedQuad p q hd h).support = (swappedChain p q hd h).block := by
  rw [swappedQuad_support]
  change _ = ({2, 3, 7, 6} : Finset (Fin 8)).image (coreCopy p q hd h)
  simp only [image_insert, image_singleton]
  rfl

lemma swapped_disjoint (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (h : WeightedPawBlock.Pattern19 p q) :
    Disjoint (swappedPaw p q hd h).support (swappedQuad p q hd h).support := by
  rw [swappedPaw_remainder, swappedQuad_block]
  exact (swappedChain p q hd h).disjoint

lemma swapped_score (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (h : WeightedPawBlock.Pattern19 p q)
    (hleaf : ¬G.Adj p.leaf (p.vertices 2) ∧ ¬G.Adj p.leaf (p.vertices 3))
    (hcenter : ∀ j : Fin 4, ¬G.Adj p.center (q j)) :
    edgeCount G (swappedChain p q hd h).block = edgeCount G q.support := by
  change edgeCount G (coreSwappedChain.block.image (coreCopy p q hd h)) = _
  rw [edgeCount_image_eq_of_adj G graph (coreCopy p q hd h) (coreCopy p q hd h).injective
    coreSwappedChain.block (fun i _ j _ ↦ adj_iff p q hd h hleaf hcenter i j),
    coreSwappedChain_score, old_edgeCount p q h]

lemma swapped_rows (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (h : WeightedPawBlock.Pattern19 p q)
    (hleaf : ¬G.Adj p.leaf (p.vertices 2) ∧ ¬G.Adj p.leaf (p.vertices 3))
    (hcenter : ∀ j : Fin 4, ¬G.Adj p.center (q j)) :
    WeightedPawBlock.Pattern19 (swappedPaw p q hd h) (swappedQuad p q hd h) := by
  let e := PawEncoding.labeling p q hd
  have he := adj_iff p q hd h hleaf hcenter
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change ¬G.Adj (e 2) (e 7)
    intro hh
    exact (by decide +kernel : ¬graph.Adj 2 7) ((he 2 7).mp hh)
  · change ¬G.Adj (e 3) (e 6)
    intro hh
    exact (by decide +kernel : ¬graph.Adj 3 6) ((he 3 6).mp hh)
  · intro j
    change G.Adj (e 1) (e ((![2, 3, 7, 6] : Fin 4 → Fin 8) j)) ↔ _
    rw [he]
    have hf : ∀ j : Fin 4, graph.Adj 1 ((![2, 3, 7, 6] : Fin 4 → Fin 8) j) ↔
        (3 : ℕ).testBit j.val = true := by decide +kernel
    exact hf j
  · intro j
    change G.Adj (e 4) (e ((![2, 3, 7, 6] : Fin 4 → Fin 8) j)) ↔ _
    rw [he]
    have hf : ∀ j : Fin 4, graph.Adj 4 ((![2, 3, 7, 6] : Fin 4 → Fin 8) j) ↔
        (7 : ℕ).testBit j.val = true := by decide +kernel
    exact hf j
  · intro j
    change G.Adj (e 5) (e ((![2, 3, 7, 6] : Fin 4 → Fin 8) j)) ↔ _
    rw [he]
    have hf : ∀ j : Fin 4, graph.Adj 5 ((![2, 3, 7, 6] : Fin 4 → Fin 8) j) ↔
        (9 : ℕ).testBit j.val = true := by decide +kernel
    exact hf j

lemma swapped_path_support (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern19 p q)
    (hleaf : ¬G.Adj p.leaf (p.vertices 2) ∧ ¬G.Adj p.leaf (p.vertices 3))
    (hcenter : ∀ j : Fin 4, ¬G.Adj p.center (q j)) (second : Bool) :
    (path second (swappedPaw p q hd h) (swappedQuad p q hd h)
      (swapped_disjoint p q hd h) (swapped_rows p q hd h hleaf hcenter)).support =
        (path (!second) p q hd h).support := by
  cases second <;> rw [FourPath.support_eq, FourPath.support_eq] <;> rfl

variable [Fintype V]

def newChain (c : TriangleChain G) (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern19 p q) : TriangleChain G :=
  c.replaceBlock b hb ((swappedChain p q hd h).withSupport (by rw [hp, hq]))

lemma newChain_feasible {c : TriangleChain G} (hc : c.Feasible)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern19 p q)
    (hleaf : ¬G.Adj p.leaf (p.vertices 2) ∧ ¬G.Adj p.leaf (p.vertices 3))
    (hcenter : ∀ j : Fin 4, ¬G.Adj p.center (q j)) :
    (newChain c p hp hb q hq hd h).Feasible := by
  apply hc.replaceBlock_feasible hb
  change edgeCount G (swappedChain p q hd h).block = edgeCount G b
  rw [swapped_score p q hd h hleaf hcenter, hq]

lemma newChain_paw_support (c : TriangleChain G) (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern19 p q) :
    (swappedPaw p q hd h).support = (newChain c p hp hb q hq hd h).remainder :=
  swappedPaw_remainder p q hd h

lemma newChain_quad_mem (c : TriangleChain G) (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern19 p q) :
    (swappedQuad p q hd h).support ∈ (newChain c p hp hb q hq hd h).blocks :=
  mem_union_right _ (mem_singleton.mpr (swappedQuad_block p q hd h))

lemma newChain_keeps (c : TriangleChain G) (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern19 p q)
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b) :
    a ∈ (newChain c p hp hb q hq hd h).blocks :=
  mem_union_left _ (mem_erase.mpr ⟨hab, ha⟩)

end Erdos577.WeightedNineteen
