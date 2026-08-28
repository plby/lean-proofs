import ErdosProblems.Erdos577.WeightedThirteenDenseConsequences

/-! Four further insertion rows for the final exclusion of pattern (13). -/

namespace Erdos577.WeightedThirteen.DenseModel.ExtraTable

open Finset

def terminal : Fin 4 → Fin 12 := ![9, 10, 9, 10]

def triple : Fin 4 → Fin 3 → Fin 12 := ![![5, 6, 7], ![5, 6, 7], ![0, 4, 5], ![0, 4, 5]]

def firstBlock : Fin 4 → Finset (Fin 12) :=
  ![{0, 1, 2, 4}, {0, 1, 2, 4}, {2, 3, 6, 7}, {2, 3, 6, 7}]

def secondBlock : Fin 4 → Finset (Fin 12) :=
  ![{3, 8, 11, 10}, {3, 8, 11, 9}, {1, 8, 11, 10}, {1, 8, 11, 9}]

def partition (tag : Fin 4) : LocalPathPartition graph (univ \ secondBlock tag) where
  terminal := terminal tag
  triple := ⟨triple tag, by fin_cases tag <;> decide +kernel⟩
  edge01 := by fin_cases tag <;> decide +kernel
  edge12 := by fin_cases tag <;> decide +kernel
  terminal_not_mem := by fin_cases tag <;> decide +kernel
  block := firstBlock tag
  quad := QuadOn.of_degreeIn (by fin_cases tag <;> decide +kernel)
    (by fin_cases tag <;> decide +kernel)
  disjoint := by fin_cases tag <;> decide +kernel
  cover := by fin_cases tag <;> decide +kernel

lemma second_quad (tag : Fin 4) : QuadOn graph (secondBlock tag) :=
  QuadOn.of_degreeIn (by fin_cases tag <;> decide +kernel) (by fin_cases tag <;> decide +kernel)

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

lemma common_factor (f : graph.Copy G) (tag : Fin 4) (a : Finset V)
    (hd : Disjoint (univ.image f) a)
    (h : CommonReplacement G (f (triple tag 0)) (f (triple tag 2))
      (f (terminal tag)) a) : Nonempty (BlockPartition G (univ.image f ∪ a)) := by
  have hinj : Function.Injective (f : Fin 12 → V) := f.injective
  have hs : (univ \ secondBlock tag).image f ⊆ univ.image f :=
    image_subset_image sdiff_subset
  obtain ⟨part⟩ := ((partition tag).image f).common_partition a (hd.mono_left hs) h
  have hdis : Disjoint ((secondBlock tag).image f)
      ((univ \ secondBlock tag).image f ∪ a) := by
    rw [disjoint_union_right]
    refine ⟨?_, hd.mono_left (image_subset_image (subset_univ _))⟩
    rw [disjoint_image hinj]
    exact disjoint_sdiff_self_right
  have he : (secondBlock tag).image f ∪
      ((univ \ secondBlock tag).image f ∪ a) = univ.image f ∪ a := by
    rw [← union_assoc, ← image_union, union_sdiff_of_subset (subset_univ _)]
  exact ⟨he ▸ (BlockPartition.single ((second_quad tag).image f)).union part hdis⟩

end Erdos577.WeightedThirteen.DenseModel.ExtraTable

namespace Erdos577.WeightedThirteen

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

lemma no_extra_common {c : TriangleChain G} {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern13 p q)
    {a : Finset V} (ha : a ∈ c.blocks) (v : Quadrilateral G) (hv : v.support = a)
    (hdis : Disjoint (p.support ∪ q.support) v.support)
    (hcl : G.IsNClique 4 v.support) (hrows : DenseRows p q v)
    {t : Finset V} (ht : t ∈ c.blocks) (htb : t ≠ b) (hta : t ≠ a) (tag : Fin 4) :
    ¬CommonReplacement G
      (WeightedFifteen.twoBlockLabeling p q hd v hdis (DenseModel.ExtraTable.triple tag 0))
      (WeightedFifteen.twoBlockLabeling p q hd v hdis (DenseModel.ExtraTable.triple tag 2))
      (WeightedFifteen.twoBlockLabeling p q hd v hdis (DenseModel.ExtraTable.terminal tag)) t := by
  classical
  intro hh
  let f := DenseModel.copy p q hd h v hdis hcl hrows
  have he : univ.image f = (p.support ∪ q.support) ∪ v.support :=
    WeightedFifteen.twoBlockLabeling_image p q hd v hdis
  have hdt : Disjoint (univ.image f) t := by
    rw [he]
    exact dense_core_disjoint p hp hb q hq ha v hv ht htb hta
  have hf := DenseModel.ExtraTable.common_factor f tag t hdt hh
  rw [he] at hf
  exact no_dense_factor hcard hn p hp hb q hq ha v hv ht hf

end Erdos577.WeightedThirteen
