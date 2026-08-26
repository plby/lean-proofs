import ErdosProblems.Erdos556.TwoColourInitialCores
import ErdosProblems.Erdos556.JoinedCoreBuckets
import ErdosProblems.Erdos556.JoinedCoreCrossEdges
import ErdosProblems.Erdos556.SmallBucketBoundary

/-!
# The two-colour structural theorem

Near twice the forbidden odd-cycle order, deleting at most one vertex
leaves two cliques in one colour, with every cross edge in the other colour.
The half-cycle core boundary is handled before asserting a size bound.
-/

namespace Erdos556

open SimpleGraph Finset

def TwoCliquePartition {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (r : ℕ) : Prop :=
  ∃ S T Z : Finset V, Z.card ≤ 1 ∧ Disjoint S T ∧ S ∪ T = univ \ Z ∧
    G.IsClique (S : Set V) ∧ G.IsClique (T : Set V) ∧
    (∀ s ∈ S, ∀ t ∈ T, Gᶜ.Adj s t) ∧ S.card ≤ 2 * r ∧ T.card ≤ 2 * r

theorem clique_card_le_of_forbidden_odd_cycle {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) (r : ℕ) (hr : 1 ≤ r)
    (hclique : G.IsClique (S : Set V)) (hno : ¬ cycleGraph (2 * r + 1) ⊑ G) :
    S.card ≤ 2 * r := by
  classical
  by_contra h
  exact hno ((cycleGraph_isContained_iff (by omega : 2 < 2 * r + 1)).mpr
    (exists_odd_cycle_in_large_joined_bucket G S S r hr Subset.rfl (by omega) (by omega)
      (fun _ ha _ hb hab => hclique ha hb hab)))

theorem joined_bucket_clique_after_single_deletion {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (A S T Z : Finset V) (r : ℕ) (hr : 1 ≤ r)
    (hAS : A ⊆ S) (hA : r ≤ A.card)
    (hjoin : ∀ a ∈ A, ∀ s ∈ S, a ≠ s → G.Adj a s)
    (hdis : Disjoint S T) (hZ : Z.card ≤ 1) (hT : r ≤ (T \ Z).card)
    (hcross : ∀ s ∈ S \ Z, ∀ t ∈ T \ Z, Gᶜ.Adj s t)
    (hnoc : ¬ cycleGraph (2 * r + 1) ⊑ Gᶜ) : G.IsClique ((S \ Z : Finset V) : Set V) := by
  by_cases hlarge : r + 1 ≤ (S \ Z).card
  · exact isClique_of_complete_complement_cross G (S \ Z) (T \ Z) r hr
      (hdis.mono sdiff_subset sdiff_subset) hlarge hT hcross hnoc
  · have hcount := card_sdiff_add_card_inter S Z
    have hinter : (S ∩ Z).card ≤ 1 := (card_le_card inter_subset_right).trans hZ
    have hsize : S.card ≤ A.card + 1 := by omega
    have hclique := joined_bucket_isClique_of_one_outside G A S hAS hsize hjoin
    intro u hu v hv huv
    exact hclique (mem_sdiff.mp hu).1 (mem_sdiff.mp hv).1 huv

theorem two_clique_partition_of_core_pair {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (r : ℕ) (hr : 4 ≤ r) (hN : 3 * r + 2 ≤ Fintype.card V)
    (hcore : TwoCliqueCorePair G r)
    (hno : ¬ cycleGraph (2 * r + 1) ⊑ G) (hnoc : ¬ cycleGraph (2 * r + 1) ⊑ Gᶜ) :
    TwoCliquePartition G r := by
  classical
  obtain ⟨A, B, hAB, hAc, hBc, hA, hB, hcrossAB⟩ := hcore
  obtain ⟨S, T, hdis, hunion, hAS, hBT, hjoinA, hjoinB⟩ :=
    exists_joined_core_buckets G A B r (by omega) hAB hAc hBc hA hB hcrossAB hnoc
  obtain ⟨Z, hZ, hcover⟩ := exists_single_vertex_bucket_cross_cover G A B S T r hr
    hAS hBT hAc hBc hjoinA hjoinB hdis hunion (by omega) hno
  have hcross := complete_complement_cross_of_cover G S T Z hdis hcover
  have hcross' : ∀ t ∈ T \ Z, ∀ s ∈ S \ Z, Gᶜ.Adj t s :=
    fun t ht s hs => (hcross s hs t ht).symm
  have hTlarge := bucket_card_after_single_deletion G A S T Z r (by omega)
    hAS hAc (hBc.trans (card_le_card hBT)) hjoinA hdis hunion hN hZ hcross hno hnoc
  have hunion' : T ∪ S = univ := by simpa only [union_comm] using hunion
  have hSlarge := bucket_card_after_single_deletion G B T S Z r (by omega)
    hBT hBc (hAc.trans (card_le_card hAS)) hjoinB hdis.symm hunion' hN hZ hcross' hno hnoc
  have hSclique := joined_bucket_clique_after_single_deletion G A S T Z r (by omega)
    hAS hAc hjoinA hdis hZ hTlarge hcross hnoc
  have hTclique := joined_bucket_clique_after_single_deletion G B T S Z r (by omega)
    hBT hBc hjoinB hdis.symm hZ hSlarge hcross' hnoc
  refine ⟨S \ Z, T \ Z, Z, hZ, hdis.mono sdiff_subset sdiff_subset, ?_, hSclique, hTclique,
    hcross, clique_card_le_of_forbidden_odd_cycle G (S \ Z) r (by omega) hSclique hno,
    clique_card_le_of_forbidden_odd_cycle G (T \ Z) r (by omega) hTclique hno⟩
  rw [← union_sdiff_distrib, hunion]

theorem exists_uniform_two_colour_structure :
    ∃ N₀ : ℕ, ∀ {V : Type*} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ),
      N₀ ≤ r → 4 * (r + 1) - (r + 1) / 100000 ≤ Fintype.card V →
      (¬ cycleGraph (2 * r + 1) ⊑ G) → (¬ cycleGraph (2 * r + 1) ⊑ Gᶜ) →
      TwoCliquePartition G r ∨ TwoCliquePartition Gᶜ r := by
  obtain ⟨N₁, hN₁⟩ := exists_uniform_two_colour_initial_cores
  refine ⟨max N₁ 4, ?_⟩
  intro V _ _ G _ r hr hN hno hnoc
  have hN' : 3 * r + 2 ≤ Fintype.card V := by
    have hdiv := Nat.div_le_self (r + 1) 100000
    omega
  rcases hN₁ G r (by omega) hN hno hnoc with h | h
  · exact Or.inl (two_clique_partition_of_core_pair G r (by omega) hN' h hno hnoc)
  · right
    apply two_clique_partition_of_core_pair Gᶜ r (by omega) hN' h hnoc
    simpa only [compl_compl] using hno

#print axioms exists_uniform_two_colour_structure

end Erdos556
