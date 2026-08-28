import ErdosProblems.Erdos577.TripleForbiddenLocal

/-! All three common-insertion prohibitions for each of the two changed paws. -/

namespace Erdos577.UniversalTriple

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {q : Quadrilateral G} {a : Finset V} {w u v : V}

lemma HighCore.leaf_exposed_ne (h : HighCore c p q a w) : p.leaf ≠ q 3 := by
  have hout : p.leaf ∉ q.support := h.toConfiguration.paw_outside 0
  exact fun he ↦ hout (he.symm ▸ (q.mem_support _).mpr ⟨3, rfl⟩)

lemma HighCore.leaf_outside_block (h : HighCore c p q a w)
    {j : Finset V} (hj : j ∈ c.blocks) : p.leaf ∉ j :=
  fun hh ↦ disjoint_left.mp (h.toConfiguration.paw_disjoint_block hj)
    (p.support_eq ▸ mem_insert_self _ _) hh

lemma HighCore.exposed_outside_block (h : HighCore c p q a w)
    {j : Finset V} (hj : j ∈ c.blocks) (hjQ : j ≠ q.support) : q 3 ∉ j :=
  fun hh ↦ disjoint_left.mp (c.property.blocks_disjoint h.block hj hjQ.symm)
    ((q.mem_support _).mpr ⟨3, rfl⟩) hh

lemma HighCore.second_ne_marked (h : HighCore c p q a w) : p.vertices 2 ≠ w :=
  fun he ↦ disjoint_left.mp (h.toConfiguration.paw_disjoint_block h.core_block)
    (by simp [Paw.support_eq, Paw.triangle]) (he.symm ▸ h.marked)

theorem HighCore.no_exposed_bridge (h : HighCore c p q a w) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {j : Finset V} (hj : j ∈ c.blocks) (hjQ : j ≠ q.support) (hja : j ≠ a)
    {z : V} (hzK : z ∈ p.triangle ∪ a) (hzb : z ≠ p.vertices 2)
    (hwz : G.Adj w z) (hr : QuadOn G ((p.triangle ∪ a) \ {p.vertices 2, w, z})) :
    ¬CommonReplacement G (q 3) z p.leaf j := by
  intro hcommon
  have hKJ := h.core_disjoint_block hj hja
  have hwK : w ∈ p.triangle ∪ a := mem_union_right _ h.marked
  have hYJ := h.exposed_outside_block hj hjQ
  have hXJ := h.leaf_outside_block hj
  have hzJ : z ∉ j := fun hh ↦ disjoint_left.mp hKJ hzK hh
  have hwJ : w ∉ j := fun hh ↦ disjoint_left.mp hKJ hwK hh
  have hYz : q 3 ≠ z := fun he ↦ h.exposed_outside_core (he.symm ▸ hzK)
  have hXw : p.leaf ≠ w := fun he ↦ h.leaf_outside_core (he.symm ▸ hwK)
  have hXz : p.leaf ≠ z := fun he ↦ h.leaf_outside_core (he.symm ▸ hzK)
  have hd : Disjoint ({q 3, w, z} : Finset V) j := by
    simp only [disjoint_insert_left, disjoint_singleton_left]
    exact ⟨hYJ, hwJ, hzJ⟩
  have hout : p.leaf ∉ ({q 3, w, z} : Finset V) ∪ j := by
    simp only [mem_union, mem_insert, mem_singleton, not_or]
    exact ⟨⟨h.leaf_exposed_ne, hXw, hXz⟩, hXJ⟩
  have hf := LocalFactor.of_three_path_common (q 3) w z p.leaf hYz
    ((h.exposed_row w h.marked).mpr rfl) hwz hd hout hcommon
  have he : insert p.leaf (({q 3, w, z} : Finset V) ∪ j) =
      insert (q 3) (insert p.leaf (({w, z} : Finset V) ∪ j)) := by
    simp only [insert_union, insert_comm]
  apply h.no_bridge_factor hcard hn hj hjQ hja
    (insert_subset hwK (singleton_subset_iff.mpr hzK))
    (by simpa only [mem_insert, mem_singleton, not_or] using
      And.intro h.second_ne_marked hzb.symm) hr
  exact he ▸ hf

theorem HighCore.no_leaf_bridge (h : HighCore c p q a w) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {j : Finset V} (hj : j ∈ c.blocks) (hjQ : j ≠ q.support) (hja : j ≠ a)
    {z : V} (hzK : z ∈ p.triangle ∪ a) (hzb : z ≠ p.vertices 2)
    (hrz : G.Adj p.center z)
    (hr : QuadOn G ((p.triangle ∪ a) \ {p.vertices 2, p.center, z})) :
    ¬CommonReplacement G p.leaf z (q 3) j := by
  intro hcommon
  have hKJ := h.core_disjoint_block hj hja
  have hrK : p.center ∈ p.triangle ∪ a := mem_union_left _ p.center_mem_triangle
  have hYJ := h.exposed_outside_block hj hjQ
  have hXJ := h.leaf_outside_block hj
  have hzJ : z ∉ j := fun hh ↦ disjoint_left.mp hKJ hzK hh
  have hrJ : p.center ∉ j := fun hh ↦ disjoint_left.mp hKJ hrK hh
  have hXz : p.leaf ≠ z := fun he ↦ h.leaf_outside_core (he.symm ▸ hzK)
  have hYr : q 3 ≠ p.center := fun he ↦ h.exposed_outside_core (he.symm ▸ hrK)
  have hYz : q 3 ≠ z := fun he ↦ h.exposed_outside_core (he.symm ▸ hzK)
  have hd : Disjoint ({p.leaf, p.center, z} : Finset V) j := by
    simp only [disjoint_insert_left, disjoint_singleton_left]
    exact ⟨hXJ, hrJ, hzJ⟩
  have hout : q 3 ∉ ({p.leaf, p.center, z} : Finset V) ∪ j := by
    simp only [mem_union, mem_insert, mem_singleton, not_or]
    exact ⟨⟨h.leaf_exposed_ne.symm, hYr, hYz⟩, hYJ⟩
  have hf := LocalFactor.of_three_path_common p.leaf p.center z (q 3) hXz
    p.pendant hrz hd hout hcommon
  have hbr : p.vertices 2 ≠ p.center := p.vertices.injective.ne (by decide : (2 : Fin 4) ≠ 1)
  apply h.no_bridge_factor hcard hn hj hjQ hja
    (insert_subset hrK (singleton_subset_iff.mpr hzK))
    (by simpa only [mem_insert, mem_singleton, not_or] using And.intro hbr hzb.symm) hr
  simpa only [insert_union] using hf

theorem UCase.no_common_pairs (s : UCase p a w u v) (h : HighCore c p q a w)
    {k : ℕ} (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {j : Finset V} (hj : j ∈ c.blocks) (hjQ : j ≠ q.support) (hja : j ≠ a) :
    ¬CommonReplacement G (q 3) u p.leaf j ∧
      ¬CommonReplacement G (q 3) v p.leaf j ∧ ¬CommonReplacement G u v p.leaf j := by
  obtain ⟨hu, hv, huv, _, hub, _, hvb⟩ := s.rows_data
  have he := SimpleGraph.is3Clique_triple_iff.mp s.triangle
  refine ⟨h.no_exposed_bridge hcard hn hj hjQ hja hu hub he.1 s.left_quad,
    h.no_exposed_bridge hcard hn hj hjQ hja hv hvb he.2.1 s.right_quad, ?_⟩
  intro hcommon
  have ht : ({w, u, v} : Finset V) ⊆ p.triangle ∪ a :=
    fun z hz ↦ (mem_sdiff.mp (s.subset hz)).1
  have hd := (h.core_disjoint_block hj hja).mono_left ht
  have hout : p.leaf ∉ ({w, u, v} : Finset V) ∪ j :=
    fun hh ↦ (mem_union.mp hh).elim (fun hh ↦ h.leaf_outside_core (ht hh))
      (h.leaf_outside_block hj)
  have hf := LocalFactor.of_triangle_common s.triangle hd p.leaf hout
    (by simp : u ∈ ({w, u, v} : Finset V)) (by simp : v ∈ ({w, u, v} : Finset V))
    huv hcommon
  exact hn (JointCore.hasPacking_of_partial_core hcard p h.paw h.core_block hj hja.symm
    ht s.complement_quad hf.partition)

theorem VCase.no_common_pairs (s : VCase p a w u v) (h : HighCore c p q a w)
    (hc : c.Feasible) {k : ℕ} (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {j : Finset V} (hj : j ∈ c.blocks) (hjQ : j ≠ q.support) (hja : j ≠ a) :
    ¬CommonReplacement G p.leaf u (q 3) j ∧
      ¬CommonReplacement G p.leaf v (q 3) j ∧ ¬CommonReplacement G u v (q 3) j := by
  obtain ⟨hu, hv, huv, _, hub, _, hvb⟩ := s.rows_data
  have he := SimpleGraph.is3Clique_triple_iff.mp s.triangle
  refine ⟨h.no_leaf_bridge hcard hn hj hjQ hja hu hub he.1 s.left_quad,
    h.no_leaf_bridge hcard hn hj hjQ hja hv hvb he.2.1 s.right_quad, ?_⟩
  intro hcommon
  have ht : ({p.center, u, v} : Finset V) ⊆ p.triangle ∪ a :=
    fun z hz ↦ (mem_sdiff.mp (s.subset hz)).1
  have hd := (h.core_disjoint_block hj hja).mono_left ht
  have hout : q 3 ∉ ({p.center, u, v} : Finset V) ∪ j :=
    fun hh ↦ (mem_union.mp hh).elim (fun hh ↦ h.exposed_outside_core (ht hh))
      (h.exposed_outside_block hj hjQ)
  have hf := LocalFactor.of_triangle_common s.triangle hd (q 3) hout
    (by simp : u ∈ ({p.center, u, v} : Finset V))
    (by simp : v ∈ ({p.center, u, v} : Finset V)) huv hcommon
  exact h.no_exposed_partial_factor hc hcard hn hj hjQ hja ht s.complement_quad hf

end Erdos577.UniversalTriple
