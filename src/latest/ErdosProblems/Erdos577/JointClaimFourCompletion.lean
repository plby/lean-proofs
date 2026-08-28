import ErdosProblems.Erdos577.JointClaimFourPartition

/-! The common-triple factor completes with the actual core complement and exposed first block. -/

namespace Erdos577.JointFinal

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

lemma last_three_core_complement (p : Paw G) (d : Quadrilateral G)
    (hd : Disjoint p.triangle d.support) :
    (p.triangle ∪ d.support) \ {d 1, d 2, d 3} = insert (d 0) p.triangle := by
  have hm (i : Fin 4) : d i ∈ d.support := (d.mem_support _).mpr ⟨i, rfl⟩
  have hsub : ({d 1, d 2, d 3} : Finset V) ⊆ d.support :=
    insert_subset (hm 1) (insert_subset (hm 2) (singleton_subset_iff.mpr (hm 3)))
  have hleft : d.support \ {d 1, d 2, d 3} = {d 0} := by
    ext u
    constructor
    · intro hu
      obtain ⟨hu, hn⟩ := mem_sdiff.mp hu
      obtain ⟨i, rfl⟩ := (d.mem_support u).mp hu
      fin_cases i
      · exact mem_singleton_self _
      · exact False.elim (hn (by simp))
      · exact False.elim (hn (by simp))
      · exact False.elim (hn (by simp))
    · intro hu
      obtain rfl := mem_singleton.mp hu
      refine mem_sdiff.mpr ⟨hm 0, ?_⟩
      simp only [mem_insert, mem_singleton, not_or]
      exact ⟨d.injective.ne (by decide : (0 : Fin 4) ≠ 1),
        d.injective.ne (by decide : (0 : Fin 4) ≠ 2),
        d.injective.ne (by decide : (0 : Fin 4) ≠ 3)⟩
  rw [union_sdiff_distrib, sdiff_eq_left.mpr (hd.mono_right hsub), hleft, union_singleton]

variable [Fintype V] [DecidableRel G.Adj]

theorem Core.two_classified_false {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {p : Paw G} {q d : Quadrilateral G} {a j b : Finset V} (h : Core c p q d a)
    (hmiss : ¬G.Adj (p.vertices 2) (d 2) ∧ ¬G.Adj (p.vertices 2) (d 3))
    (hj : j ∈ c.blocks) (hjq : j ≠ q.support) (hja : j ≠ a)
    (hb : b ∈ c.blocks) (hbq : b ≠ q.support) (hba : b ≠ a) (hbj : b ≠ j)
    (hfirst : Conclusion p q d j) (hsecond : Conclusion p q d.reverse b) : False := by
  obtain ⟨_, v, hv, hrows1, hy1⟩ := hfirst
  obtain ⟨_, w, hw, hrows2, hy2⟩ := hsecond
  change ∀ i : Fin 4, i ≠ 0 → G.Adj (d 2) (w i) ∧ G.Adj (d 1) (w i) at hrows2
  obtain ⟨hp, hq, ha, haq, hcase, _, _⟩ := h.config
  have hyout (s : Finset V) (hs : s ∈ c.blocks) (hsq : s ≠ q.support) : q 3 ∉ s :=
    fun hh ↦ disjoint_left.mp (c.property.blocks_disjoint hq hs hsq.symm)
      ((q.mem_support _).mpr ⟨3, rfl⟩) hh
  have parts := two_classified_partition d v w (q 3)
    (by rw [h.labels, hv]; exact c.property.blocks_disjoint ha hj hja.symm)
    (by rw [h.labels, hw]; exact c.property.blocks_disjoint ha hb hba.symm)
    (by rw [hv, hw]; exact c.property.blocks_disjoint hj hb hbj.symm)
    (by rw [h.labels]; exact hyout a ha haq)
    (by rw [hv]; exact hyout j hj hjq) (by rw [hw]; exact hyout b hb hbq)
    hrows1 hrows2 hy1 hy2
  have hFQ := h.paw_disjoint hq
  obtain ⟨e, _, _, _, hp', _, _, _, hkeep⟩ :=
    JointClaims.exists_exposed_chain hc hcard hn p hp hq q rfl hFQ (Or.inr hcase)
  let p' := JointClaims.exposedPaw p q hFQ (Or.inr hcase)
  have htri : p'.triangle = p.triangle :=
    JointClaims.exposedPaw_triangle p q hFQ (Or.inr hcase)
  have hTA : Disjoint p.triangle d.support := by
    rw [h.labels]
    exact (h.paw_disjoint ha).mono_left (p.support_eq ▸ subset_insert _ _)
  obtain ⟨_, tag, htag, hpat⟩ := h.missing_pair_source hmiss
  have hcl := early_source_triangle_clique tag p d htag hpat.1
  have hrem : QuadOn G ((p'.triangle ∪ a) \ {d 1, d 2, d 3}) := by
    rw [htri, ← h.labels, last_three_core_complement p d hTA]
    exact QuadOn.of_clique hcl.card_eq hcl.isClique
  have hused : ({d 1, d 2, d 3} : Finset V) ⊆ p'.triangle ∪ a :=
    insert_subset (mem_union_right _ (h.mem 1)) (insert_subset (mem_union_right _ (h.mem 2))
      (singleton_subset_iff.mpr (mem_union_right _ (h.mem 3))))
  have hbs : ({j, b} : Finset (Finset V)) ⊆ e.blocks :=
    insert_subset (hkeep j hj hjq) (singleton_subset_iff.mpr (hkeep b hb hbq))
  have hna : a ∉ ({j, b} : Finset (Finset V)) := by
    simpa only [mem_insert, mem_singleton, not_or] using And.intro hja.symm hba.symm
  have hf : Nonempty (BlockPartition G
      (insert p'.leaf ({d 1, d 2, d 3} ∪ ({j, b} : Finset (Finset V)).biUnion id))) := by
    simpa only [p', JointClaims.exposedPaw_leaf, hv, hw, biUnion_insert,
      singleton_biUnion, id_eq, union_assoc] using parts
  exact hn (JointFirst.hasPacking_of_selected_core hcard p' hp' (hkeep a ha haq)
    {j, b} hbs hna hused hrem hf)

end Erdos577.JointFinal
