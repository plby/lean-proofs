import ErdosProblems.Erdos577.JointFinalFactors

/-! The two insertion prohibitions P1 and P2 for every outside block. -/

namespace Erdos577.JointFinal

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

def spokes (p : Paw G) (d : Quadrilateral G) : Finset V := {p.leaf, d 2, d 3}

lemma Core.spokes_card {c : TriangleChain G} {p : Paw G} {q d : Quadrilateral G} {a : Finset V}
    (h : Core c p q d a) : (spokes p d).card = 3 := by
  obtain ⟨_, hx1, hx2, _, _, h12⟩ := JointCore.four_distinct h.arms_card
  exact card_triple_eq_three_iff.mpr ⟨hx1, hx2, h12⟩

lemma Core.spokes_center {c : TriangleChain G} {p : Paw G} {q d : Quadrilateral G} {a : Finset V}
    (h : Core c p q d a) : ∀ u ∈ spokes p d, G.Adj p.center u := by
  intro u hu
  simp only [spokes, mem_insert, mem_singleton] at hu
  rcases hu with rfl | rfl | rfl
  · exact p.pendant.symm
  · exact h.center_first
  · exact h.center_second

lemma Core.spokes_disjoint {c : TriangleChain G} {p : Paw G} {q d : Quadrilateral G}
    {a j : Finset V} (h : Core c p q d a) (hj : j ∈ c.blocks) (hja : j ≠ a) :
    Disjoint (spokes p d) j := by
  have hFJ := h.paw_disjoint hj
  have hAJ := c.property.blocks_disjoint h.config.2.2.1 hj hja.symm
  exact disjoint_insert_left.mpr
    ⟨fun hh ↦ disjoint_left.mp hFJ (p.support_eq ▸ mem_insert_self _ _) hh,
      disjoint_insert_left.mpr ⟨fun hh ↦ disjoint_left.mp hAJ (h.mem 2) hh,
        disjoint_singleton_left.mpr (fun hh ↦ disjoint_left.mp hAJ (h.mem 3) hh)⟩⟩

theorem Core.no_leaf_common {c : TriangleChain G} {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {p : Paw G} {q d : Quadrilateral G} {a j : Finset V} (h : Core c p q d a)
    (hj : j ∈ c.blocks) (hja : j ≠ a)
    {u v w : V} (hu : u ∈ spokes p d) (hv : v ∈ spokes p d) (hw : w ∈ spokes p d)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) : ¬CommonReplacement G u v w j := by
  have hrj : p.center ∉ j := fun hh ↦ disjoint_left.mp (h.paw_disjoint hj)
    ((mem_tupleSupport p.vertices _).mpr ⟨1, rfl⟩) hh
  have hno (s : Finset V) (hs : s ⊆ spokes p d) (hthree : s.card = 3) :
      ¬LocalFactor G (insert p.center s ∪ j) := by
    have he : s = spokes p d := eq_of_subset_of_card_le hs (by rw [h.spokes_card, hthree])
    rw [he]
    have hset : insert p.center (spokes p d) ∪ j =
        insert p.leaf ({p.center, d 2, d 3} ∪ j) := by
      simp only [spokes, insert_union, singleton_union]
      rw [insert_comm p.center p.leaf]
    rw [hset]
    exact h.old_triple_no_factor hcard hn hj hja
  exact no_common_of_star_triples (h.spokes_disjoint hj hja) hrj h.spokes_center hno
    hu hv hw huv huw hvw

theorem Core.no_exposed_common {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {p : Paw G} {q d : Quadrilateral G} {a j : Finset V} (h : Core c p q d a)
    (hj : j ∈ c.blocks) (hjq : j ≠ q.support) (hja : j ≠ a)
    {u v : V} (hu : u ∈ spokes p d) (hv : v ∈ spokes p d) (huv : u ≠ v) :
    ¬CommonReplacement G u v (q 3) j := by
  have mixed {z : V} (hz : z ∈ a)
      (hr : QuadOn G ((p.triangle ∪ a) \ {z, p.center, p.vertices 2})) :
      ¬LocalFactor G (insert (q 3) (insert p.center ({p.leaf, z} ∪ j))) := by
    have he : insert p.center ({p.leaf, z} ∪ j) = insert p.leaf ({z, p.center} ∪ j) := by
      ext w
      simp only [mem_insert, mem_union, mem_singleton]
      tauto
    rw [he]
    exact h.mixed_triple_no_factor hc hcard hn hj hjq hja hz hr
  have hm1 := mixed (h.mem 2) h.secondary_first
  have hm2 := mixed (h.mem 3) h.secondary_second
  have hp : ¬LocalFactor G (insert (q 3) (insert p.center ({d 2, d 3} ∪ j))) := by
    simpa only [insert_union] using h.exposed_triple_no_factor hc hcard hn hj hjq hja
  have hno : ¬LocalFactor G (insert (q 3) (insert p.center ({u, v} ∪ j))) := by
    have hu' := hu
    have hv' := hv
    simp only [spokes, mem_insert, mem_singleton] at hu' hv'
    rcases hu' with rfl | rfl | rfl <;> rcases hv' with rfl | rfl | rfl
    · exact False.elim (huv rfl)
    · exact hm1
    · exact hm2
    · rw [pair_comm (d 2) p.leaf]
      exact hm1
    · exact False.elim (huv rfl)
    · exact hp
    · rw [pair_comm (d 3) p.leaf]
      exact hm2
    · rw [pair_comm (d 3) (d 2)]
      exact hp
    · exact False.elim (huv rfl)
  have hSJ := h.spokes_disjoint hj hja
  have hrj : p.center ∉ j := fun hh ↦ disjoint_left.mp (h.paw_disjoint hj)
    ((mem_tupleSupport p.vertices _).mpr ⟨1, rfl⟩) hh
  have hdis : Disjoint ({u, p.center, v} : Finset V) j :=
    disjoint_insert_left.mpr ⟨fun hh ↦ disjoint_left.mp hSJ hu hh,
      disjoint_insert_left.mpr ⟨hrj,
        disjoint_singleton_left.mpr (fun hh ↦ disjoint_left.mp hSJ hv hh)⟩⟩
  obtain ⟨hxy, _, _, hy1, hy2, _⟩ := JointCore.four_distinct h.arms_card
  have hyS : q 3 ∉ spokes p d := by
    simpa only [spokes, mem_insert, mem_singleton, not_or] using And.intro hxy.symm ⟨hy1, hy2⟩
  have hyQ : q 3 ∈ q.support := (q.mem_support _).mpr ⟨3, rfl⟩
  have hyr : q 3 ≠ p.center := by
    intro he
    have hrQ : p.center ∈ q.support := he ▸ hyQ
    exact disjoint_left.mp (h.paw_disjoint h.config.2.1)
      ((mem_tupleSupport p.vertices _).mpr ⟨1, rfl⟩) hrQ
  have hyj : q 3 ∉ j := fun hh ↦
    disjoint_left.mp (c.property.blocks_disjoint h.config.2.1 hj hjq.symm) hyQ hh
  have hyout : q 3 ∉ ({u, p.center, v} : Finset V) ∪ j := by
    simp only [mem_union, mem_insert, mem_singleton, not_or]
    exact ⟨⟨fun he ↦ hyS (he.symm ▸ hu), hyr, fun he ↦ hyS (he.symm ▸ hv)⟩, hyj⟩
  intro hh
  have hf := star_factor_of_common huv (h.spokes_center u hu) (h.spokes_center v hv) hdis hyout hh
  have he : insert p.center ({u, v, q 3} ∪ j) =
      insert (q 3) (insert p.center ({u, v} ∪ j)) := by
    ext w
    simp only [mem_insert, mem_union, mem_singleton]
    tauto
  exact hno (he ▸ hf)

end Erdos577.JointFinal
