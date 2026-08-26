import ErdosProblems.Erdos547.TreeCore
import ErdosProblems.Erdos547.HighDegreeCore

/-!
# Trees with a small bipartition class

A small core fits greedily into the high-global-degree core of one colour.
All remaining leaves can then be restored. This proves the Ramsey conclusion
for the very unbalanced trees without using either large-order embedding input.
-/

namespace Erdos547

open Finset SimpleGraph
open scoped SimpleGraph

open scoped Classical in
/-- Embed the nonleaf subtree into a host set, then restore all leaves using
the global degrees of its images. -/
theorem isContained_of_treeCore_host {U V : Type*} [Fintype U] [Fintype V]
    (T : SimpleGraph U) (G : SimpleGraph V) [DecidableRel T.Adj] [DecidableRel G.Adj]
    (hT : T.IsTree) (hcard : 3 ≤ Fintype.card U) (Q : Finset V) (hQ : Q.Nonempty)
    (hlocal : ∀ v ∈ Q, Fintype.card (treeCore T) - 1 ≤ degreeIn G Q v)
    (hglobal : ∀ v ∈ Q, Fintype.card U - 1 ≤ G.degree v) : T ⊑ G := by
  classical
  obtain ⟨z, hz⟩ := hQ
  let : Nonempty (Q : Set V) := ⟨⟨z, hz⟩⟩
  have hd : Fintype.card (treeCore T) - 1 ≤ (G.induce (Q : Set V)).minDegree := by
    apply SimpleGraph.le_minDegree_of_forall_le_degree
    intro v
    rw [← degreeIn_eq_induce_degree G Q v]
    exact hlocal v.val v.property
  obtain ⟨e⟩ := isContained_of_isTree_of_minDegree (isTree_treeCore T hT hcard) hd
  let e' : (T.induce (treeCore T)).Copy G := (SimpleGraph.Copy.induce G (Q : Set V)).comp e
  obtain ⟨parent, hp⟩ := exists_treeCore_parent T hT hcard
  obtain ⟨f, _⟩ := extend_copy_of_leaf_parent_degree (treeCore T) parent hp e' (by
    intro x
    exact hglobal (e (parent x)).val (e (parent x)).property)
  exact ⟨f⟩

open scoped Classical in
/-- The full Ramsey conclusion for a tree whose core has at most `m/5`
vertices. This is a proved subcase, not an assumption in the final theorem. -/
theorem ramseyAt_of_small_treeCore {m : ℕ} (hm : 2 ≤ m)
    (T : SimpleGraph (Fin (m + 1))) (hT : T.IsTree)
    (hcore : 5 * Fintype.card (treeCore T) ≤ m) : RamseyAt T (2 * m) := by
  classical
  intro R
  have hTcard : 3 ≤ Fintype.card (Fin (m + 1)) := by simp only [Fintype.card_fin]; omega
  have hsmall : (Fintype.card (treeCore T) : ℝ) ≤ (m : ℝ) / 5 := by
    have hc : 5 * (Fintype.card (treeCore T) : ℝ) ≤ m := by exact_mod_cast hcore
    linarith
  have hlocal (G : SimpleGraph (Fin (2 * m))) [DecidableRel G.Adj]
      (Q : Finset (Fin (2 * m)))
      (hQ : ∀ v ∈ Q, (m : ℝ) / 5 < (degreeIn G Q v : ℝ)) :
      ∀ v ∈ Q, Fintype.card (treeCore T) - 1 ≤ degreeIn G Q v := by
    intro v hv
    have h : (Fintype.card (treeCore T) : ℝ) < degreeIn G Q v :=
      hsmall.trans_lt (hQ v hv)
    have hn : Fintype.card (treeCore T) < degreeIn G Q v := by exact_mod_cast h
    omega
  rcases exists_high_degree_colour_core (by omega : 0 < m) R with hr | hb
  · obtain ⟨Q, hQ, hglobal, hdeg⟩ := hr
    left
    apply isContained_of_treeCore_host T R hT hTcard Q hQ (hlocal R Q hdeg)
    simpa only [Fintype.card_fin, Nat.add_sub_cancel] using hglobal
  · obtain ⟨Q, hQ, hglobal, hdeg⟩ := hb
    right
    apply isContained_of_treeCore_host T Rᶜ hT hTcard Q hQ (hlocal Rᶜ Q hdeg)
    simpa only [Fintype.card_fin, Nat.add_sub_cancel] using hglobal

open scoped Classical in
/-- Every tree with a bipartition class of size at most `m/10` occurs in a
single colour of every red/blue `K_(2*m)`. -/
theorem ramseyAt_of_small_bipartition {m : ℕ} (hm : 2 ≤ m)
    (T : SimpleGraph (Fin (m + 1))) (hT : T.IsTree)
    (s t : Finset (Fin (m + 1)))
    (hpart : T.IsBipartiteWith (s : Set (Fin (m + 1))) (t : Set (Fin (m + 1))))
    (hcover : s ∪ t = Finset.univ) (hsmall : 10 * s.card ≤ m) : RamseyAt T (2 * m) := by
  classical
  let : Nontrivial (Fin (m + 1)) := Fintype.one_lt_card_iff_nontrivial.mp (by
    simp only [Fintype.card_fin]
    omega)
  have hcore := card_treeCore_add_one_le T hT s t hpart
    (by simpa only [Finset.ext_iff, Finset.mem_union] using hcover)
  apply ramseyAt_of_small_treeCore hm T hT
  omega

end Erdos547

#print axioms Erdos547.isContained_of_treeCore_host
#print axioms Erdos547.ramseyAt_of_small_bipartition
