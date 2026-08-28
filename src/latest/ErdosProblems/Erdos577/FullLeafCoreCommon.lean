import ErdosProblems.Erdos577.FullLeafCoreSecond

/-! Both center versions of the common-neighbor replacement prohibition. -/

namespace Erdos577.FullLeafCore

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {s a : Finset V} {y : V}
variable (h : Configuration c p s a y)

include h

lemma Configuration.core_disjoint_block {j : Finset V} (hj : j ∈ c.blocks) (hja : j ≠ a) :
    Disjoint (p.triangle ∪ a) j := disjoint_union_left.mpr
  ⟨(h.paw_disjoint hj).mono_left (p.support_eq ▸ subset_insert _ _),
    c.property.blocks_disjoint h.core hj hja.symm⟩

lemma Configuration.five_disjoint_block {j : Finset V} (hj : j ∈ c.blocks) (hjs : j ≠ s) :
    Disjoint (insert p.leaf s) j := disjoint_insert_left.mpr
  ⟨fun hh ↦ disjoint_left.mp (h.paw_disjoint hj) (p.support_eq ▸ mem_insert_self _ _) hh,
    c.property.blocks_disjoint h.first hj hjs.symm⟩

theorem Configuration.no_common_replacement {k : ℕ} (hcard : Fintype.card V = 4 * k)
    (hn : ¬HasPacking G k) {x : V} (hx : x ∈ insert p.leaf s)
    {w u v : V} (hw : w ∈ p.triangle ∪ a) (hu : u ∈ p.triangle ∪ a)
    (hv : v ∈ p.triangle ∪ a) (huw : u ≠ w) (hvw : v ≠ w) (huv : u ≠ v)
    (hxw : G.Adj x w) (hwv : G.Adj w v)
    {j : Finset V} (hj : j ∈ c.blocks) (hjs : j ≠ s) (hja : j ≠ a) :
    ¬CommonReplacement G x v u j := by
  intro hr
  have hKJ := h.core_disjoint_block hj hja
  have hZJ := h.five_disjoint_block hj hjs
  have hxv : x ≠ v := fun he ↦ disjoint_left.mp h.five_disjoint_core hx (he ▸ hv)
  have hux : u ≠ x := fun he ↦ disjoint_left.mp h.five_disjoint_core hx (he ▸ hu)
  have hd : Disjoint ({x, w, v} : Finset V) j := disjoint_insert_left.mpr
    ⟨fun hh ↦ disjoint_left.mp hZJ hx hh,
      disjoint_insert_left.mpr ⟨fun hh ↦ disjoint_left.mp hKJ hw hh,
        disjoint_singleton_left.mpr (fun hh ↦ disjoint_left.mp hKJ hv hh)⟩⟩
  have hout : u ∉ ({x, w, v} : Finset V) ∪ j := by
    simp only [mem_union, mem_insert, mem_singleton, not_or]
    exact ⟨⟨hux, huw, huv⟩, fun hh ↦ disjoint_left.mp hKJ hu hh⟩
  have hf := LocalFactor.of_common_path x w v u hxv hxw hwv hd hout hr
  have hsub : ({w, v, u} : Finset V) ⊆ p.triangle ∪ a :=
    insert_subset hw (insert_subset hv (singleton_subset_iff.mpr hu))
  have hc3 : ({w, v, u} : Finset V).card = 3 :=
    card_triple_eq_three_iff.mpr ⟨hvw.symm, huw.symm, huv.symm⟩
  have he : insert u (({x, w, v} : Finset V) ∪ j) = insert x ({w, v, u} ∪ j) := by
    ext z
    simp only [mem_insert, mem_union, mem_singleton]
    tauto
  exact h.first_no_factor hcard hn hx hj hjs hja hsub hc3 (he ▸ hf)

theorem Configuration.center_common_forbidden {k : ℕ} (hcard : Fintype.card V = 4 * k)
    (hn : ¬HasPacking G k) {u v : V} (hu : u ∈ insert (p.vertices 3) a)
    (hv : v ∈ insert (p.vertices 3) a) (huv : u ≠ v) (hvr : G.Adj v p.center)
    {j : Finset V} (hj : j ∈ c.blocks) (hjs : j ≠ s) (hja : j ≠ a) :
    ¬CommonReplacement G p.leaf v u j :=
  h.no_common_replacement hcard hn (mem_insert_self _ _)
    (mem_union_left _ p.center_mem_triangle) (h.second_five_subset hu) (h.second_five_subset hv)
    (h.second_avoids hu).2.1 (h.second_avoids hv).2.1 huv p.pendant hvr.symm hj hjs hja

theorem Configuration.second_common_forbidden {k : ℕ} (hcard : Fintype.card V = 4 * k)
    (hn : ¬HasPacking G k) {u v : V} (hu : u ∈ insert (p.vertices 3) a)
    (hv : v ∈ insert (p.vertices 3) a) (huv : u ≠ v) (hvb : G.Adj v (p.vertices 2))
    {j : Finset V} (hj : j ∈ c.blocks) (hjs : j ≠ s) (hja : j ≠ a) :
    ¬CommonReplacement G y v u j :=
  h.no_common_replacement hcard hn (mem_insert_of_mem h.exposed)
    (mem_union_left _ (by simp [Paw.triangle])) (h.second_five_subset hu) (h.second_five_subset hv)
    (h.second_avoids hu).2.2 (h.second_avoids hv).2.2 huv h.attached.symm hvb.symm hj hjs hja

end Erdos577.FullLeafCore
