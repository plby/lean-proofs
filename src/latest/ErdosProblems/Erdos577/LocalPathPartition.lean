import ErdosProblems.Erdos577.ReplacementFactors
import ErdosProblems.Erdos577.TriangleAssembly

/-! A singleton, a three-vertex path, and a quadrilateral give explicit replacement factors. -/

namespace Erdos577

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

lemma tupleSupport_trans {W : Type*} [DecidableEq W] {n : ℕ}
    (a : Fin n ↪ V) (f : V ↪ W) : tupleSupport (a.trans f) = (tupleSupport a).image f := by
  rw [tupleSupport, tupleSupport, image_image]
  rfl

structure LocalPathPartition (G : SimpleGraph V) (s : Finset V) where
  terminal : V
  triple : Fin 3 ↪ V
  edge01 : G.Adj (triple 0) (triple 1)
  edge12 : G.Adj (triple 1) (triple 2)
  terminal_not_mem : terminal ∉ tupleSupport triple
  block : Finset V
  quad : QuadOn G block
  disjoint : Disjoint (insert terminal (tupleSupport triple)) block
  cover : insert terminal (tupleSupport triple) ∪ block = s

namespace LocalPathPartition

variable {s t : Finset V}

def remainder (d : LocalPathPartition G s) : Finset V := insert d.terminal (tupleSupport d.triple)

lemma remainder_subset (d : LocalPathPartition G s) : d.remainder ⊆ s :=
  subset_union_left.trans (le_of_eq d.cover)

lemma block_subset (d : LocalPathPartition G s) : d.block ⊆ s :=
  subset_union_right.trans (le_of_eq d.cover)

lemma triple_subset (d : LocalPathPartition G s) : tupleSupport d.triple ⊆ s :=
  (subset_insert _ _).trans d.remainder_subset

lemma card_remainder (d : LocalPathPartition G s) : d.remainder.card = 4 := by
  simp only [remainder, card_insert_of_notMem d.terminal_not_mem, card_tupleSupport]

lemma card (d : LocalPathPartition G s) : s.card = 8 := by
  rw [← d.cover, card_union_of_disjoint d.disjoint, d.quad.card]
  have h := d.card_remainder
  change (insert d.terminal (tupleSupport d.triple)).card = 4 at h
  omega

def withSupport (d : LocalPathPartition G s) (h : s = t) : LocalPathPartition G t where
  terminal := d.terminal
  triple := d.triple
  edge01 := d.edge01
  edge12 := d.edge12
  terminal_not_mem := d.terminal_not_mem
  block := d.block
  quad := d.quad
  disjoint := d.disjoint
  cover := d.cover.trans h

variable {W : Type*} [DecidableEq W] {H : SimpleGraph W}

def image (d : LocalPathPartition G s) (f : G.Copy H) : LocalPathPartition H (s.image f) where
  terminal := f d.terminal
  triple := d.triple.trans f.toEmbedding
  edge01 := f.toHom.map_rel' d.edge01
  edge12 := f.toHom.map_rel' d.edge12
  terminal_not_mem := by
    rw [tupleSupport_trans]
    intro h
    obtain ⟨u, hu, he⟩ := mem_image.mp h
    exact d.terminal_not_mem (f.injective he ▸ hu)
  block := d.block.image f
  quad := d.quad.image f
  disjoint := by
    rw [tupleSupport_trans]
    have hinj : Function.Injective (f : V → W) := f.injective
    change Disjoint (insert (f d.terminal) ((tupleSupport d.triple).image f)) (d.block.image f)
    rw [← image_insert, disjoint_image hinj]
    exact d.disjoint
  cover := by
    rw [tupleSupport_trans]
    change insert (f d.terminal) ((tupleSupport d.triple).image f) ∪ d.block.image f = s.image f
    simpa only [image_union, image_insert] using congrArg (fun u : Finset V ↦ u.image f) d.cover

lemma common_partition (d : LocalPathPartition G s) (a : Finset V) (hd : Disjoint s a)
    (h : CommonReplacement G (d.triple 0) (d.triple 2) d.terminal a) :
    Nonempty (BlockPartition G (s ∪ a)) := by
  obtain ⟨u, hu, h0u, h2u, hrep⟩ := h
  have hz : d.terminal ∉ tupleSupport d.triple ∪ a := by
    intro hz
    rcases mem_union.mp hz with hz | hz
    · exact d.terminal_not_mem hz
    · exact disjoint_left.mp hd (d.remainder_subset (mem_insert_self _ _)) hz
  have ht : tupleSupport d.triple = {d.triple 0, d.triple 1, d.triple 2} := by
    have he : (univ : Finset (Fin 3)) = {0, 1, 2} := by decide
    rw [tupleSupport, he]
    simp only [image_insert, image_singleton]
  have hqu := QuadOn.of_vertices (G := G)
    (a := d.triple 0) (b := d.triple 1) (c := d.triple 2) (d := u)
    (fun he ↦ (by decide : (0 : Fin 3) ≠ 2) (d.triple.injective he))
    (fun he ↦ disjoint_left.mp hd
      (d.triple_subset ((mem_tupleSupport d.triple _).mpr ⟨1, rfl⟩)) (he ▸ hu))
    d.edge01 d.edge12 h2u h0u.symm
  have hquad : QuadOn G (insert u (tupleSupport d.triple)) := by
    rw [ht]
    convert hqu using 1
    ext v
    simp only [mem_insert, mem_singleton]
    tauto
  have hf := LocalFactor.of_replacement (hd.mono_left d.triple_subset) hz hu hquad hrep
  have hf' : LocalFactor G (d.remainder ∪ a) := by
    simpa only [remainder, insert_union] using hf
  obtain ⟨part⟩ := hf'.partition
  have hdis : Disjoint d.block (d.remainder ∪ a) := by
    rw [disjoint_union_right]
    exact ⟨d.disjoint.symm, hd.mono_left d.block_subset⟩
  have he : d.block ∪ (d.remainder ∪ a) = s ∪ a := by
    rw [← union_assoc, union_comm d.block d.remainder]
    exact congrArg (fun x ↦ x ∪ a) d.cover
  exact ⟨he ▸ (BlockPartition.single d.quad).union part hdis⟩

end LocalPathPartition

variable [Fintype V]

lemma TriangleChain.no_common_replacement {k : ℕ} (c : TriangleChain G)
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {b a : Finset V} (hb : b ∈ c.blocks) (ha : a ∈ c.blocks) (hab : a ≠ b)
    (d : LocalPathPartition G (c.remainder ∪ b)) :
    ¬CommonReplacement G (d.triple 0) (d.triple 2) d.terminal a := by
  intro h
  have hd : Disjoint (c.remainder ∪ b) a := by
    rw [disjoint_union_left]
    refine ⟨?_, c.property.blocks_disjoint hb ha hab.symm⟩
    apply disjoint_left.mpr
    intro v hv hva
    exact (mem_sdiff.mp (c.complementPartition.block_subset ha hva)).2 hv
  obtain ⟨part⟩ := d.common_partition a hd h
  have hbs : ({b, a} : Finset (Finset V)) ⊆ c.blocks := by
    intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · exact hb
    · exact mem_singleton.mp hx ▸ ha
  have he : c.remainder ∪ ({b, a} : Finset (Finset V)).biUnion id =
      (c.remainder ∪ b) ∪ a := by
    simp only [biUnion_insert, singleton_biUnion, id_eq, union_assoc]
  exact hn (c.complementPartition.hasPacking_of_selected_factor hcard {b, a} hbs (he.symm ▸ part))

end Erdos577
