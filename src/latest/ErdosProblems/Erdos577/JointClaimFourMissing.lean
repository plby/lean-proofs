import ErdosProblems.Erdos577.JointLocalClassification

/-! The common distinguished triple forces the other triangle vertex to miss both core arms. -/

namespace Erdos577.JointFinal

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem Core.exposed_noncentral_pair_no_factor {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {p : Paw G} {q d : Quadrilateral G} {a j : Finset V} (h : Core c p q d a)
    (hj : j ∈ c.blocks) (hjq : j ≠ q.support) (hja : j ≠ a) :
    ¬LocalFactor G (insert (q 3) ({p.vertices 2, d 2, d 3} ∪ j)) := by
  intro hf
  obtain ⟨hp, hs, ha, has, hcase, _, _⟩ := h.config
  have hFQ := h.paw_disjoint hs
  obtain ⟨e, _, _, _, hp', _, _, _, hkeep⟩ :=
    JointClaims.exists_exposed_chain hc hcard hn p hp hs q rfl hFQ (Or.inr hcase)
  let p' := JointClaims.exposedPaw p q hFQ (Or.inr hcase)
  have htri : p'.triangle = p.triangle :=
    JointClaims.exposedPaw_triangle p q hFQ (Or.inr hcase)
  have hu : ({p.vertices 2, d 2, d 3} : Finset V) ⊆ p'.triangle ∪ a := by
    rw [htri]
    exact insert_subset (mem_union_left _ (by simp [Paw.triangle]))
      (insert_subset (mem_union_right _ (h.mem 2))
        (singleton_subset_iff.mpr (mem_union_right _ (h.mem 3))))
  have hr : QuadOn G ((p'.triangle ∪ a) \ {p.vertices 2, d 2, d 3}) := by
    have he : ({p.vertices 2, d 2, d 3} : Finset V) = {d 2, d 3, p.vertices 2} := by
      rw [insert_comm (p.vertices 2) (d 2), pair_comm (p.vertices 2) (d 3)]
    rw [htri, he]
    exact h.tertiary
  exact hn (JointCore.hasPacking_of_partial_core hcard p' hp' (hkeep a ha has)
    (hkeep j hj hjq) hja.symm hu hr hf.partition)

theorem Core.classified_pair_nonadjacent {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {p : Paw G} {q d : Quadrilateral G} {a j : Finset V} (h : Core c p q d a)
    (hj : j ∈ c.blocks) (hjq : j ≠ q.support) (hja : j ≠ a)
    (hcon : Conclusion p q d j) :
    ¬G.Adj (p.vertices 2) (d 2) ∧ ¬G.Adj (p.vertices 2) (d 3) := by
  obtain ⟨_, v, hv, hrows, hY⟩ := hcon
  have hm (i : Fin 4) : p.vertices i ∈ p.support := (mem_tupleSupport p.vertices _).mpr ⟨i, rfl⟩
  have hAQ := c.property.blocks_disjoint h.config.2.2.1 h.config.2.1 h.config.2.2.2.1
  have hAJ := c.property.blocks_disjoint h.config.2.2.1 hj hja.symm
  have hyout : q 3 ∉ j := fun hh ↦
    disjoint_left.mp (c.property.blocks_disjoint h.config.2.1 hj hjq.symm)
      ((q.mem_support _).mpr ⟨3, rfl⟩) hh
  have hbout : p.vertices 2 ∉ j := fun hh ↦ disjoint_left.mp (h.paw_disjoint hj) (hm 2) hh
  have hYb := (JointClaims.first_rows p q (Or.inr h.config.2.2.2.2.1)).2.symm
  have exclude (z w : V) (hz : z ∈ a) (hw : w ∈ a) (hzw : z ≠ w)
      (hpair : ({z, w} : Finset V) = {d 2, d 3})
      (hzrow : ∀ i : Fin 4, i ≠ 0 → G.Adj z (v i))
      (hwrow : G.Adj w (v 2)) : ¬G.Adj (p.vertices 2) w := by
    intro hbw
    have hzout : z ∉ v.support := by
      rw [hv]
      exact fun hh ↦ disjoint_left.mp hAJ hz hh
    have hwout : w ∉ j := fun hh ↦ disjoint_left.mp hAJ hw hh
    have hyw : q 3 ≠ w := fun he ↦ disjoint_left.mp hAQ hw
      (he ▸ ((q.mem_support _).mpr ⟨3, rfl⟩))
    have hzy : z ≠ q 3 := fun he ↦ disjoint_left.mp hAQ hz
      (he.symm ▸ ((q.mem_support _).mpr ⟨3, rfl⟩))
    have hzb : z ≠ p.vertices 2 := fun he ↦
      disjoint_left.mp (h.paw_disjoint h.config.2.2.1) (hm 2) (he ▸ hz)
    have hd : Disjoint {q 3, p.vertices 2, w} j :=
      disjoint_insert_left.mpr ⟨hyout, disjoint_insert_left.mpr
        ⟨hbout, disjoint_singleton_left.mpr hwout⟩⟩
    have hzall : z ∉ ({q 3, p.vertices 2, w} : Finset V) ∪ j := by
      simp only [mem_union, mem_insert, mem_singleton, not_or]
      exact ⟨⟨hzy, hzb, hzw⟩, fun hh ↦ hzout (hv.symm ▸ hh)⟩
    have hrep := low_pair_replace v z hzout (hzrow 1 (by decide))
      (hzrow 3 (by decide)) 2 (Or.inr rfl)
    rw [hv] at hrep
    have hfactor := LocalFactor.of_common_path (q 3) (p.vertices 2) w z hyw hYb hbw hd hzall
      ⟨v 2, hv ▸ (v.mem_support _).mpr ⟨2, rfl⟩, hY, hwrow, hrep⟩
    have he : insert z ({q 3, p.vertices 2, w} ∪ j) =
        insert (q 3) ({p.vertices 2, d 2, d 3} ∪ j) := by
      calc
        insert z ({q 3, p.vertices 2, w} ∪ j) =
            insert (q 3) (insert (p.vertices 2) ({z, w} ∪ j)) := by
          simp only [insert_union, singleton_union]
          rw [insert_comm z (q 3), insert_comm z (p.vertices 2)]
        _ = insert (q 3) ({p.vertices 2, d 2, d 3} ∪ j) := by
          rw [hpair]
          simp only [insert_union]
    exact h.exposed_noncentral_pair_no_factor hc hcard hn hj hjq hja (he ▸ hfactor)
  exact ⟨exclude (d 3) (d 2) (h.mem 3) (h.mem 2) (d.injective.ne (by decide))
      (pair_comm _ _) (fun i hi ↦ (hrows i hi).2) (hrows 2 (by decide)).1,
    exclude (d 2) (d 3) (h.mem 2) (h.mem 3) (d.injective.ne (by decide))
      rfl (fun i hi ↦ (hrows i hi).1) (hrows 2 (by decide)).2⟩

end Erdos577.JointFinal
