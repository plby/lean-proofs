import ErdosProblems.Erdos577.JointEightTerminal

/-! The two explicit outside quadrilaterals, completed by the first block's center replacement. -/

namespace Erdos577.JointClaims

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

lemma split_third_partition (p : Paw G) (v : Quadrilateral G) (t : V)
    (hd : Disjoint p.support v.support) (ht : t ∉ p.support ∪ v.support)
    (hfirst : QuadOn G {p.center, p.vertices 3, v 3, v 2})
    (hsecond : QuadOn G {p.leaf, v 0, t, v 1}) :
    Nonempty (BlockPartition G (insert t (FullRow.pathTriple p.swapNoncentral ∪ v.support))) := by
  have hpm (i : Fin 4) : p.vertices i ∈ p.support :=
    (mem_tupleSupport p.vertices _).mpr ⟨i, rfl⟩
  have hvm (i : Fin 4) : v i ∈ v.support := (v.mem_support _).mpr ⟨i, rfl⟩
  have hpv (i j : Fin 4) : p.vertices i ≠ v j :=
    fun he ↦ disjoint_left.mp hd (hpm i) (he.symm ▸ hvm j)
  have hvp (i j : Fin 4) : v i ≠ p.vertices j := (hpv j i).symm
  have hpt (i : Fin 4) : p.vertices i ≠ t :=
    fun he ↦ ht (mem_union_left _ (he ▸ hpm i))
  have hvt (i : Fin 4) : v i ≠ t :=
    fun he ↦ ht (mem_union_right _ (he ▸ hvm i))
  have htp (i : Fin 4) : t ≠ p.vertices i := (hpt i).symm
  have htv (i : Fin 4) : t ≠ v i := (hvt i).symm
  have hinj : Function.Injective (v : Fin 4 → V) := v.injective
  have hdis : Disjoint ({p.center, p.vertices 3, v 3, v 2} : Finset V)
      {p.leaf, v 0, t, v 1} := by
    simp [Paw.center, Paw.leaf, hpv, hvp, htp, htv,
      p.vertices.injective.eq_iff, hinj.eq_iff]
  have he : ({p.center, p.vertices 3, v 3, v 2} : Finset V) ∪ {p.leaf, v 0, t, v 1} =
      insert t (FullRow.pathTriple p.swapNoncentral ∪ v.support) := by
    rw [v.support_four]
    change _ = insert t ({p.leaf, p.center, p.vertices 3} ∪ {v 0, v 1, v 2, v 3})
    ext u
    simp only [mem_union, mem_insert, mem_singleton]
    tauto
  exact ⟨he ▸ (BlockPartition.single hfirst).union (BlockPartition.single hsecond) hdis⟩

variable [Fintype V] [DecidableRel G.Adj]

theorem case_two_split_factor_false {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {s a : Finset V} (hs : s ∈ c.blocks) (ha : a ∈ c.blocks) (has : a ≠ s)
    (q : Quadrilateral G) (hq : q.support = s) (hcase : CaseTwo p q)
    (v : Quadrilateral G) (hv : v.support = a)
    (hfirst : QuadOn G {p.center, p.vertices 3, v 3, v 2})
    (hsecond : QuadOn G {p.leaf, v 0, q 3, v 1}) : False := by
  have hd : Disjoint p.support v.support := by
    rw [hp, hv]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset ha)
  have hFQ : Disjoint p.support q.support := by
    rw [hp, hq]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hs)
  have hQA : Disjoint q.support v.support := by
    rw [hq, hv]
    exact c.property.blocks_disjoint hs ha has.symm
  have htm : q 3 ∈ q.support := (q.mem_support _).mpr ⟨3, rfl⟩
  have ht : q 3 ∉ p.support ∪ v.support := by
    intro hh
    exact (mem_union.mp hh).elim (fun hh ↦ disjoint_left.mp hFQ hh htm)
      (fun hh ↦ disjoint_left.mp hQA htm hh)
  have hp' : p.swapNoncentral.support = c.remainder := by rw [Paw.swapNoncentral_support, hp]
  apply hn
  apply FullRow.hasPacking_of_distinguished_other hcard p.swapNoncentral hp' {a}
    (singleton_subset_iff.mpr ha) hs (by simpa only [mem_singleton] using has.symm)
    (hq ▸ htm)
  · change QuadOn G (insert (p.vertices 2) (s.erase (q 3)))
    rw [← hq]
    exact case_two_universal hc p hp hs q hq hcase (q 3) htm
  · simpa only [singleton_biUnion, id_eq, ← hv] using
      split_third_partition p v (q 3) hd ht hfirst hsecond

end Erdos577.JointClaims
