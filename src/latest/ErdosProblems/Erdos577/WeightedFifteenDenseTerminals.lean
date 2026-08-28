import ErdosProblems.Erdos577.WeightedFifteenDenseTables
import ErdosProblems.Erdos577.SelectedChainExchange
import ErdosProblems.Erdos577.TerminalReplacements

/-! Both specified vertices are terminals of feasible chains keeping every outside block. -/

namespace Erdos577.WeightedFifteen

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma dense_terminal_score (second complete : Bool)
    (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (h : WeightedPawBlock.Pattern15 p q) (v : Quadrilateral G)
    (hv : Disjoint (p.support ∪ q.support) v.support)
    (hcl : G.IsNClique 4 v.support) (hrows : DenseRows p q v)
    (hleaf : ¬G.Adj p.leaf (p.vertices 2) ∧ ¬G.Adj p.leaf (p.vertices 3))
    (hcenter : ∀ j : Fin 4, j ≠ 2 → ¬G.Adj p.center (q j)) :
    edgeCount G ((DenseModel.terminalBlock second complete).image
      (DenseModel.copy p q hd h v hv hcl hrows)) = if complete then 6 else 5 := by
  let f := DenseModel.copy p q hd h v hv hcl hrows
  rw [edgeCount_image_eq_of_adj G DenseModel.graph f f.injective
    (DenseModel.terminalBlock second complete) ?_, DenseModel.terminal_block_score]
  intro i hi j hj
  constructor
  · intro he
    exact (DenseModel.terminal_block_adj second complete i hi j hj).mp
      (DenseModel.adj_upper p q hd h v hv hrows hleaf hcenter i j he)
  · exact f.toHom.map_rel'

variable [Fintype V]

theorem exists_dense_terminal_chain {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k) (second : Bool)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern15 p q)
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b) (v : Quadrilateral G) (hv : v.support = a)
    (hcl : G.IsNClique 4 v.support) (hrows : DenseRows p q v) :
    ∃ d : TriangleChain G, d.Feasible ∧ d.terminal = (if second then q 3 else v 0) ∧
      ∀ t ∈ c.blocks, t ≠ b → t ≠ a → t ∈ d.blocks := by
  have hdis : Disjoint (p.support ∪ q.support) v.support := by
    rw [hp, hq, hv, disjoint_union_left]
    refine ⟨?_, c.property.blocks_disjoint hb ha hab.symm⟩
    apply disjoint_left.mpr
    intro w hw hwa
    exact (mem_sdiff.mp (c.complementPartition.block_subset ha hwa)).2 hw
  let f := DenseModel.copy p q hd h v hdis hcl hrows
  have hinj : Function.Injective (f : Fin 12 → V) := f.injective
  let B (complete : Bool) := (DenseModel.terminalBlock second complete).image f
  have hB (complete : Bool) : QuadOn G (B complete) :=
    (DenseModel.terminal_block_quad second complete).image f
  have hBB : Disjoint (B false) (B true) := by
    exact (disjoint_image hinj).mpr (DenseModel.terminal_blocks_disjoint second)
  let part := (BlockPartition.single (hB false)).union (BlockPartition.single (hB true)) hBB
  have hscore (complete : Bool) : edgeCount G (B complete) = if complete then 6 else 5 :=
    dense_terminal_score second complete p q hd h v hdis hcl hrows
      (c.paw_nonadjacent hcard hn p hp) (center_absent hc hcard hn p hp hb q hq hd h)
  have hE : part.weightSum (edgeCount G) = 11 := by
    rw [BlockPartition.weightSum_union, BlockPartition.weightSum_single,
      BlockPartition.weightSum_single, hscore false, hscore true]
    decide +kernel
  have hF : part.weightSum (fun s ↦ if edgeCount G s = 6 then 1 else 0) = 1 := by
    rw [BlockPartition.weightSum_union, BlockPartition.weightSum_single,
      BlockPartition.weightSum_single, hscore false, hscore true]
    decide +kernel
  have hbs : ({b, a} : Finset (Finset V)) ⊆ c.blocks := by
    intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · exact hb
    · exact mem_singleton.mp hx ▸ ha
  have he : c.remainder ∪ ({b, a} : Finset (Finset V)).biUnion id = univ.image f := by
    change _ = univ.image (twoBlockLabeling p q hd v hdis)
    rw [twoBlockLabeling_image, hp, hq, hv]
    simp only [biUnion_insert, singleton_biUnion, id_eq, union_assoc]
  have hu : B false ∪ B true ⊆ c.remainder ∪ ({b, a} : Finset (Finset V)).biUnion id := by
    rw [he]
    change (DenseModel.terminalBlock second false).image f ∪
      (DenseModel.terminalBlock second true).image f ⊆ _
    rw [← image_union]
    exact image_subset_image (subset_univ _)
  let t := (DenseModel.terminalTriangle second).image f
  let x := f (DenseModel.terminal second)
  have ht : G.IsNClique 3 t := by
    refine ⟨?_, ?_⟩
    · intro u hu w hw huw
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hu
      obtain ⟨j, hj, rfl⟩ := mem_image.mp hw
      exact f.toHom.map_rel' ((DenseModel.terminal_triangle_clique second).isClique hi hj
        (fun he ↦ huw (congrArg f he)))
    · rw [card_image_of_injective _ hinj, (DenseModel.terminal_triangle_clique second).card_eq]
  have hx : x ∉ t := by
    rintro hh
    obtain ⟨i, hi, heq⟩ := mem_image.mp hh
    exact DenseModel.terminal_not_mem second (f.injective heq ▸ hi)
  have hr : (c.remainder ∪ ({b, a} : Finset (Finset V)).biUnion id) \ (B false ∪ B true) =
      insert x t := by
    rw [he]
    change univ.image f \ ((DenseModel.terminalBlock second false).image f ∪
      (DenseModel.terminalBlock second true).image f) = _
    rw [← image_union, ← image_sdiff _ _ hinj, DenseModel.terminal_remainder, image_insert]
  have ha6 : edgeCount G a = 6 := by
    rw [← hv, edgeCount_clique hcl.isClique, hcl.card_eq]
    decide +kernel
  have hb5 : edgeCount G b = 5 := hq ▸ old_edgeCount p q h
  have hOldE : (c.complementPartition.select {b, a} hbs).weightSum (edgeCount G) = 11 := by
    change ∑ s ∈ ({b, a} : Finset (Finset V)), edgeCount G s = 11
    rw [sum_pair hab.symm, hb5, ha6]
  have hOldF : (c.complementPartition.select {b, a} hbs).weightSum
      (fun s ↦ if edgeCount G s = 6 then 1 else 0) = 1 := by
    change ∑ s ∈ ({b, a} : Finset (Finset V)), (if edgeCount G s = 6 then 1 else 0) = 1
    rw [sum_pair hab.symm, hb5, ha6]
    decide +kernel
  let d := c.replaceSelected {b, a} hbs part hu x ht hx hr
  refine ⟨d, hc.replaceSelected_feasible {b, a} hbs part hu x ht hx hr
    (hE.trans hOldE.symm) (hF.trans hOldF.symm), ?_, ?_⟩
  · cases second <;> rfl
  · intro z hz hzb hza
    apply c.replaceSelected_keeps {b, a} hbs part hu x ht hx hr hz
    simp only [mem_insert, mem_singleton, not_or]
    exact ⟨hzb, hza⟩

theorem dense_terminal_universal {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k) (second : Bool)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern15 p q)
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b) (v : Quadrilateral G) (hv : v.support = a)
    (hcl : G.IsNClique 4 v.support) (hrows : DenseRows p q v)
    {t : Finset V} (ht : t ∈ c.blocks) (htb : t ≠ b) (hta : t ≠ a)
    (h3 : 3 ≤ degreeIn G (if second then q 3 else v 0) t) (u : V) (hu : u ∈ t) :
    QuadOn G (insert (if second then q 3 else v 0) (t.erase u)) := by
  obtain ⟨d, hdF, hdx, hkeep⟩ := exists_dense_terminal_chain hc hcard hn second p hp hb q hq
    hd h ha hab v hv hcl hrows
  rw [← hdx] at h3 ⊢
  exact hdF.terminal_universal_replace (hkeep t ht htb hta) h3 hu

end Erdos577.WeightedFifteen
