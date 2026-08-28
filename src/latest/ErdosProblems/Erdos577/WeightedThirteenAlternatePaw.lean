import ErdosProblems.Erdos577.WeightedThirteenDenseModel
import ErdosProblems.Erdos577.PawTerminalExchange
import ErdosProblems.Erdos577.LocalChainSupport

/-! The alternate strong paw exchanges one complete block while retaining all other blocks. -/

namespace Erdos577.WeightedThirteen

open Finset

namespace DenseModel

def alternateSet : Finset (Fin 12) := {0, 1, 2, 3, 8, 9, 10, 11}

def alternateLocal : LocalChain graph alternateSet where
  terminal := 0
  triangle := {1, 9, 10}
  block := {2, 3, 8, 11}
  triangle_clique := by decide +kernel
  terminal_not_mem := by decide +kernel
  quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  disjoint := by decide +kernel
  cover := by decide +kernel

lemma alternate_block_edges : edgeCount graph alternateLocal.block = 6 := by decide +kernel

end DenseModel

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

def alternatePaw (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (h : WeightedPawBlock.Pattern13 p q) (v : Quadrilateral G)
    (hv : Disjoint (p.support ∪ q.support) v.support)
    (hcl : G.IsNClique 4 v.support) (hrows : DenseRows p q v) : Paw G where
  vertices := (⟨![0, 1, 9, 10], by decide +kernel⟩ : Fin 4 ↪ Fin 12).trans
    (DenseModel.copy p q hd h v hv hcl hrows).toEmbedding
  pendant := by
    change G.Adj (p.vertices 0) (p.vertices 1)
    exact p.pendant
  edge12 := by
    change G.Adj p.center (v 1)
    exact (hrows.2.2.2.2.1 1).mpr (by decide)
  edge13 := by
    change G.Adj p.center (v 2)
    exact (hrows.2.2.2.2.1 2).mpr (by decide)
  edge23 := by
    change G.Adj (v 1) (v 2)
    exact v.adjacent 1

lemma alternateSet_image (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (h : WeightedPawBlock.Pattern13 p q) (v : Quadrilateral G)
    (hv : Disjoint (p.support ∪ q.support) v.support)
    (hcl : G.IsNClique 4 v.support) (hrows : DenseRows p q v) :
    DenseModel.alternateSet.image (DenseModel.copy p q hd h v hv hcl hrows) =
      p.support ∪ v.support := by
  have hu : (univ : Finset (Fin 4)) = {0, 1, 2, 3} := by decide
  rw [Paw.support, tupleSupport, Quadrilateral.support, hu]
  simp only [DenseModel.alternateSet, image_insert, image_singleton]
  change {p.vertices 0, p.vertices 1, p.vertices 2, p.vertices 3, v 0, v 1, v 2, v 3} =
    {p.vertices 0, p.vertices 1, p.vertices 2, p.vertices 3} ∪ {v 0, v 1, v 2, v 3}
  ext u
  simp only [mem_insert, mem_singleton, mem_union]
  tauto

lemma alternatePaw_remainder (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern13 p q)
    (v : Quadrilateral G) (hv : Disjoint (p.support ∪ q.support) v.support)
    (hcl : G.IsNClique 4 v.support) (hrows : DenseRows p q v) :
    (alternatePaw p q hd h v hv hcl hrows).support =
      (DenseModel.alternateLocal.image (DenseModel.copy p q hd h v hv hcl hrows)).remainder := by
  rw [Paw.support_eq]
  simp only [LocalChain.remainder, LocalChain.image, DenseModel.alternateLocal,
    image_insert, image_singleton]
  rfl

lemma alternate_block_score (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern13 p q)
    (v : Quadrilateral G) (hv : Disjoint (p.support ∪ q.support) v.support)
    (hcl : G.IsNClique 4 v.support) (hrows : DenseRows p q v) :
    edgeCount G (DenseModel.alternateLocal.image
      (DenseModel.copy p q hd h v hv hcl hrows)).block = edgeCount G v.support := by
  let d := DenseModel.alternateLocal.image (DenseModel.copy p q hd h v hv hcl hrows)
  have hl := DenseModel.alternateLocal.image_edgeCount_le
    (DenseModel.copy p q hd h v hv hcl hrows)
  rw [DenseModel.alternate_block_edges] at hl
  have hu := edgeCount_le_six G d.quad.card
  have hv6 : edgeCount G v.support = 6 := by
    rw [edgeCount_clique hcl.isClique, hcl.card_eq]
    decide +kernel
  change edgeCount G d.block = edgeCount G v.support
  change 6 ≤ edgeCount G d.block at hl
  omega

variable [Fintype V]

theorem exists_alternate_strong_chain {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (h : WeightedPawBlock.Pattern13 p q)
    {a : Finset V} (ha : a ∈ c.blocks) (v : Quadrilateral G) (hv : v.support = a)
    (hdis : Disjoint (p.support ∪ q.support) v.support)
    (hcl : G.IsNClique 4 v.support) (hrows : DenseRows p q v) :
    ∃ d : TriangleChain G, d.Strong ∧
      (alternatePaw p q hd h v hdis hcl hrows).support = d.remainder ∧
      ∀ t ∈ c.blocks, t ≠ a → t ∈ d.blocks := by
  let p' := alternatePaw p q hd h v hdis hcl hrows
  let d₀ := DenseModel.alternateLocal.image (DenseModel.copy p q hd h v hdis hcl hrows)
  let l := d₀.withSupport (show _ = c.remainder ∪ a by
    rw [alternateSet_image, hp, hv])
  let d := c.replaceBlock a ha l
  have hdF : d.Feasible := hc.replaceBlock_feasible ha l (by
    change edgeCount G d₀.block = edgeCount G a
    rw [← hv]
    exact alternate_block_score p q hd h v hdis hcl hrows)
  have hp' : p'.support = d.remainder := alternatePaw_remainder p q hd h v hdis hcl hrows
  refine ⟨d.presentPaw p' hp', hdF.presentPaw_strong hcard hn p' hp', p'.support_eq, ?_⟩
  intro t ht hta
  exact mem_union_left _ (mem_erase.mpr ⟨hta, ht⟩)

end Erdos577.WeightedThirteen
