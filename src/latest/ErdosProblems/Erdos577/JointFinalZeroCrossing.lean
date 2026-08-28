import ErdosProblems.Erdos577.JointFinalZeroRows

/-! The crossing clique gain uses the actual exposed chain and retains its replaced first block. -/

namespace Erdos577.JointFinal

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem Core.exposed_crossing_false {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {p : Paw G} {q d : Quadrilateral G} {a : Finset V} (h : Core c p q d a)
    (j : Quadrilateral G) (hj : j.support ∈ c.blocks) (hjq : j.support ≠ q.support)
    (hja : j.support ≠ a) (hje : edgeCount G j.support = 4)
    (h10 : G.Adj (d 2) (j 0)) (h11 : G.Adj (d 2) (j 1))
    (h20 : G.Adj (d 3) (j 0)) (h21 : G.Adj (d 3) (j 1))
    (hy2 : G.Adj (q 3) (j 2)) (hy3 : G.Adj (q 3) (j 3)) : False := by
  obtain ⟨hp, hs, ha, has, hcase, _, _⟩ := h.config
  obtain ⟨e, he, ht, hT, _, _, _, _, hkeep⟩ := JointClaims.exists_exposed_chain hc hcard hn
    p hp hs q rfl (h.paw_disjoint hs) (Or.inr hcase)
  have h1out : d 2 ∉ (p.triangle ∪ a) \ {p.center, d 2, d 3} := by
    intro hh
    exact (mem_sdiff.mp hh).2 (by simp)
  have h2out : d 3 ∉ (p.triangle ∪ a) \ {p.center, d 2, d 3} := by
    intro hh
    exact (mem_sdiff.mp hh).2 (by simp)
  apply JointFirst.strict_crossing_gain he.toFeasible (hkeep a ha has) (j.rotate 3)
    (by rw [j.rotate_support]; exact hkeep j.support hj hjq)
    (by rw [j.rotate_support]; exact hja.symm) (by rwa [j.rotate_support])
    ((p.triangle ∪ a) \ {p.center, d 2, d 3}) h.primary
    (by rw [hT]; exact sdiff_subset) h.primary_edges (h.mem 2) (h.mem 3) h1out h2out h.pair_edge
  · exact h10
  · exact h11
  · exact h20
  · exact h21
  · rw [ht]
    exact hy3
  · rw [ht]
    exact hy2

theorem Core.first_pair_not_common {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {p : Paw G} {q d : Quadrilateral G} {a : Finset V} (h : Core c p q d a)
    (j : Quadrilateral G) (hj : j.support ∈ c.blocks) (hjq : j.support ≠ q.support)
    (hja : j.support ≠ a) (hy2 : G.Adj (q 3) (j 2)) (hy3 : G.Adj (q 3) (j 3)) :
    ¬((G.Adj (d 2) (j 0) ∧ G.Adj (d 3) (j 0)) ∧
      (G.Adj (d 2) (j 1) ∧ G.Adj (d 3) (j 1))) := by
  rintro ⟨⟨h10, h20⟩, ⟨h11, h21⟩⟩
  have hne : edgeCount G j.support ≠ 4 := fun he ↦
    h.exposed_crossing_false hc hcard hn j hj hjq hja he h10 h11 h20 h21 hy2 hy3
  have hdiag : G.Adj (j 0) (j 2) ∨ G.Adj (j 1) (j 3) := by
    by_contra! hh
    have he := j.edgeCount_eq
    rw [if_neg hh.1, if_neg hh.2] at he
    exact hne (by omega)
  have hyout : q 3 ∉ j.support := fun hh ↦
    disjoint_left.mp (c.property.blocks_disjoint h.config.2.1 hj hjq.symm)
      ((q.mem_support _).mpr ⟨3, rfl⟩) hh
  have hno := h.no_exposed_common hc hcard hn hj hjq hja
    (u := d 2) (v := d 3) (by simp [spokes]) (by simp [spokes])
    (d.injective.ne (by decide))
  rcases hdiag with h02 | h13
  · have hrep := j.replace_using_path (q 3) hyout 1 2 0 3 (by decide) (by decide)
      hy2 h02.symm (j.adjacent 3).symm hy3
    exact hno ⟨j 1, (j.mem_support _).mpr ⟨1, rfl⟩, h11, h21, hrep⟩
  · have hrep := j.replace_using_path (q 3) hyout 0 2 1 3 (by decide) (by decide)
      hy2 (j.adjacent 1).symm h13 hy3
    exact hno ⟨j 0, (j.mem_support _).mpr ⟨0, rfl⟩, h10, h20, hrep⟩

end Erdos577.JointFinal
