import ErdosProblems.Erdos577.DensePairFactors

/-! The exposed vertex cannot replace a common neighbor of any two of the three spokes. -/

namespace Erdos577.DenseObstruction

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma PairConfig.spokes_center {c : TriangleChain G} {p : Paw G} {d : Quadrilateral G}
    {s : Finset V} {z : V}
    (h : PairConfig c p d s z) : ∀ u ∈ JointFinal.spokes p d, G.Adj p.center u := by
  intro u hu
  simp only [JointFinal.spokes, mem_insert, mem_singleton] at hu
  rcases hu with rfl | rfl | rfl
  · exact p.pendant.symm
  · exact h.pair.center_first
  · exact h.pair.center_second

lemma PairConfig.spokes_disjoint {c : TriangleChain G} {p : Paw G} {d : Quadrilateral G}
    {s : Finset V} {z : V}
    (h : PairConfig c p d s z) {j : Finset V} (hj : j ∈ c.blocks) (hjd : j ≠ d.support) :
    Disjoint (JointFinal.spokes p d) j := by
  have hFJ := h.paw_disjoint hj
  have hDJ : Disjoint d.support j := c.property.blocks_disjoint h.core hj hjd.symm
  exact disjoint_insert_left.mpr
    ⟨fun hh ↦ disjoint_left.mp hFJ (p.support_eq ▸ mem_insert_self _ _) hh,
      disjoint_insert_left.mpr
        ⟨fun hh ↦ disjoint_left.mp hDJ ((d.mem_support _).mpr ⟨2, rfl⟩) hh,
          disjoint_singleton_left.mpr
            (fun hh ↦ disjoint_left.mp hDJ ((d.mem_support _).mpr ⟨3, rfl⟩) hh)⟩⟩

theorem PairConfig.pair_no_factor {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {p : Paw G} {d : Quadrilateral G} {s : Finset V} {z : V} (h : PairConfig c p d s z)
    {j : Finset V} (hj : j ∈ c.blocks) (hjs : j ≠ s) (hjd : j ≠ d.support)
    {u v : V} (hu : u ∈ JointFinal.spokes p d) (hv : v ∈ JointFinal.spokes p d) (huv : u ≠ v) :
    ¬LocalFactor G (insert z (insert p.center ({u, v} ∪ j))) := by
  have mixed (i : Fin 4) (hi : i = 2 ∨ i = 3) :
      ¬LocalFactor G (insert z (insert p.center ({p.leaf, d i} ∪ j))) := by
    have he : insert p.center ({p.leaf, d i} ∪ j) =
        insert p.leaf ({d i, p.center} ∪ j) := by
      simp only [insert_union, singleton_union]
      rw [insert_comm p.center p.leaf, insert_comm p.center (d i)]
    rw [he]
    exact h.mixed_pair_no_factor hcard hn hj hjs hjd i hi
  have hm1 := mixed 2 (Or.inl rfl)
  have hm2 := mixed 3 (Or.inr rfl)
  have hp : ¬LocalFactor G (insert z (insert p.center ({d 2, d 3} ∪ j))) := by
    simpa only [insert_union] using h.exposed_pair_no_factor hc hcard hn hj hjs hjd
  simp only [JointFinal.spokes, mem_insert, mem_singleton] at hu hv
  rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
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

theorem PairConfig.no_exposed_common {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {p : Paw G} {d : Quadrilateral G} {s : Finset V} {z : V} (h : PairConfig c p d s z)
    {j : Finset V} (hj : j ∈ c.blocks) (hjs : j ≠ s) (hjd : j ≠ d.support)
    {u v : V} (hu : u ∈ JointFinal.spokes p d) (hv : v ∈ JointFinal.spokes p d) (huv : u ≠ v) :
    ¬CommonReplacement G u v z j := by
  have hno := h.pair_no_factor hc hcard hn hj hjs hjd hu hv huv
  have hSJ := h.spokes_disjoint hj hjd
  have hrj : p.center ∉ j := fun hh ↦ disjoint_left.mp (h.paw_disjoint hj)
    ((mem_tupleSupport p.vertices _).mpr ⟨1, rfl⟩) hh
  have hdis : Disjoint ({u, p.center, v} : Finset V) j :=
    disjoint_insert_left.mpr ⟨fun hh ↦ disjoint_left.mp hSJ hu hh,
      disjoint_insert_left.mpr ⟨hrj,
        disjoint_singleton_left.mpr (fun hh ↦ disjoint_left.mp hSJ hv hh)⟩⟩
  obtain ⟨hxy, _, _, hy1, hy2, _⟩ := JointCore.four_distinct h.arms_card
  have hyS : z ∉ JointFinal.spokes p d := by
    simpa only [JointFinal.spokes, mem_insert, mem_singleton, not_or] using
      And.intro hxy.symm ⟨hy1, hy2⟩
  have hym : z ∈ s := h.exposed
  have hrF : p.center ∈ p.support := (mem_tupleSupport p.vertices _).mpr ⟨1, rfl⟩
  have hyr : z ≠ p.center := fun he ↦
    disjoint_left.mp (h.paw_disjoint h.first) hrF (he ▸ hym)
  have hyj : z ∉ j := fun hh ↦
    disjoint_left.mp (c.property.blocks_disjoint h.first hj hjs.symm) hym hh
  have hyout : z ∉ ({u, p.center, v} : Finset V) ∪ j := by
    simp only [mem_union, mem_insert, mem_singleton, not_or]
    exact ⟨⟨fun he ↦ hyS (he.symm ▸ hu), hyr, fun he ↦ hyS (he.symm ▸ hv)⟩, hyj⟩
  intro hh
  have hf := star_factor_of_common huv (h.spokes_center u hu) (h.spokes_center v hv) hdis hyout hh
  have he : insert p.center ({u, v, z} ∪ j) =
      insert z (insert p.center ({u, v} ∪ j)) := by
    simp only [insert_union, singleton_union]
    rw [insert_comm v z, insert_comm u z, insert_comm p.center z]
  exact hno (he ▸ hf)

end Erdos577.DenseObstruction
