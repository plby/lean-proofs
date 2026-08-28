import ErdosProblems.Erdos577.WeightedNineteenCore
import ErdosProblems.Erdos577.OutsideCoreCount
import ErdosProblems.Erdos577.PawInduced

/-! The two improved paths in pattern (19), with exact inside contact sums. -/

namespace Erdos577.WeightedNineteen

open Finset
open scoped BigOperators

def pathVertices (second : Bool) : Fin 4 → Fin 8 :=
  if second then ![6, 5, 0, 1] else ![7, 3, 1, 0]

def corePath (second : Bool) : FourPath graph where
  vertices := ⟨pathVertices second, by cases second <;> decide +kernel⟩
  adjacent := by cases second <;> decide +kernel

lemma corePath_inside (second : Bool) : contacts graph (corePath second).support univ = 13 := by
  cases second <;> decide +kernel

lemma corePath_quad (second : Bool) : QuadOn graph (univ \ (corePath second).support) :=
  QuadOn.of_degreeIn (by cases second <;> decide +kernel) (by cases second <;> decide +kernel)

lemma corePath_edges (second : Bool) : edgeCount graph (univ \ (corePath second).support) = 5 := by
  cases second <;> decide +kernel

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

def path (second : Bool) (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (h : WeightedPawBlock.Pattern19 p q) : FourPath G := (corePath second).image (coreCopy p q hd h)

lemma path_support (second : Bool) (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern19 p q) :
    (path second p q hd h).support =
      (corePath second).support.image (PawEncoding.labeling p q hd) :=
  (corePath second).image_support (coreCopy p q hd h)

lemma path_subset (second : Bool) (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern19 p q) :
    (path second p q hd h).support ⊆ p.support ∪ q.support := by
  rw [path_support, ← PawEncoding.labeling_image p q hd]
  exact image_subset_image (subset_univ _)

lemma complement_image (second : Bool) (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern19 p q) :
    (p.support ∪ q.support) \ (path second p q hd h).support =
      (univ \ (corePath second).support).image (coreCopy p q hd h) := by
  have hinj : Function.Injective (coreCopy p q hd h : Fin 8 → V) := (coreCopy p q hd h).injective
  rw [image_sdiff _ _ hinj, coreCopy_image]
  rw [path_support]
  rfl

lemma path_complement_quad (second : Bool) (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern19 p q) :
    QuadOn G ((p.support ∪ q.support) \ (path second p q hd h).support) := by
  rw [complement_image]
  exact (corePath_quad second).image (coreCopy p q hd h)

lemma path_gain (second : Bool) (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern19 p q) :
    edgeCount G q.support <
      edgeCount G ((p.support ∪ q.support) \ (path second p q hd h).support) := by
  rw [complement_image, old_edgeCount p q h]
  have he := edgeCount_image_le (coreCopy p q hd h) (univ \ (corePath second).support)
  rw [corePath_edges] at he
  omega

lemma path_inside (second : Bool) (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern19 p q)
    (hleaf : ¬G.Adj p.leaf (p.vertices 2) ∧ ¬G.Adj p.leaf (p.vertices 3))
    (hcenter : ∀ j : Fin 4, ¬G.Adj p.center (q j)) :
    contacts G (path second p q hd h).support (p.support ∪ q.support) = 13 := by
  rw [path_support, ← PawEncoding.labeling_image p q hd]
  rw [contacts_image_eq_of_adj G graph (PawEncoding.labeling p q hd)
    (PawEncoding.labeling p q hd).injective (corePath second).support univ
    (fun i _ j _ ↦ adj_iff p q hd h hleaf hcenter i j)]
  exact corePath_inside second

end WeightedNineteen

namespace TriangleChain

open Finset
open scoped BigOperators

lemma exists_paired_heavy_outside_core {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (c : TriangleChain G) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v)
    {b : Finset V} (hb : b ∈ c.blocks) (s t : Finset V) (hs : s.card = 4) (ht : t.card = 4)
    (hinside : contacts G s (c.remainder ∪ b) + contacts G t (c.remainder ∪ b) ≤ 31) :
    ∃ a ∈ c.blocks, a ≠ b ∧ 17 ≤ contacts G s a + contacts G t a := by
  have htotalS := minimum_degree_sum G s (2 * k) (fun v _ ↦ hdeg v)
  have htotalT := minimum_degree_sum G t (2 * k) (fun v _ ↦ hdeg v)
  have hidS := c.contacts_core_add_outside hb s
  have hidT := c.contacts_core_add_outside hb t
  have hblocks := c.card_vertices
  have herase := card_erase_of_mem hb
  have hpos : 0 < c.blocks.card := card_pos.mpr ⟨b, hb⟩
  by_contra! hn
  have hbound : (∑ a ∈ c.blocks.erase b, (contacts G s a + contacts G t a)) ≤
      (c.blocks.erase b).card * 16 := by
    calc
      _ ≤ ∑ _ ∈ c.blocks.erase b, 16 := sum_le_sum fun a ha ↦ by
        have hh := hn a (mem_erase.mp ha).2 (mem_erase.mp ha).1
        omega
      _ = _ := by simp
  rw [sum_add_distrib] at hbound
  rw [hs] at htotalS
  rw [ht] at htotalT
  omega

end TriangleChain

namespace WeightedNineteen

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem heavy_block {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern19 p q) :
    ∃ a ∈ c.blocks, a ≠ b ∧
      17 ≤ contacts G (path false p q hd h).support a +
        contacts G (path true p q hd h).support a := by
  have hleaf := c.paw_nonadjacent hcard hn p hp
  have hcenter := center_absent hc hcard hn p hp hb q hq hd h
  have hfirst := path_inside false p q hd h hleaf hcenter
  have hsecond := path_inside true p q hd h hleaf hcenter
  rw [hp, hq] at hfirst hsecond
  exact c.exists_paired_heavy_outside_core hcard hdeg hb
    (path false p q hd h).support (path true p q hd h).support
    (path false p q hd h).card_support (path true p q hd h).card_support (by omega)

end WeightedNineteen

end Erdos577
