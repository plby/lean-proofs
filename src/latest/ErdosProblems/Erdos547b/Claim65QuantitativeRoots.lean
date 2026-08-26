/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.LargeClusterReservoir
import ErdosProblems.Erdos547b.EvenReducedPadding
import ErdosProblems.Erdos547b.Section6Dichotomy

/-!
# Quantitative root reservoirs for Zhao Lemma 6.5

Claim 6.1 constructs its Claim-6.7 certificate on the even padding of the
reduced graph.  Lemma 6.5, however, uses two actual subsets `A₀` and `B₀`
of the original adjacent large clusters.  This file crosses that boundary:
it removes the dummy padding vertices and selects the two canonical
high-degree reservoirs.  No embedding or continuation property occurs in
the statements.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos547b.ZhaoLemma65QuantitativeRoots

open Finset SimpleGraph
open Erdos547b.ZhaoStability
open Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoQuantitativeLargeClusters

universe u v

@[simp] theorem largeVertexReservoir_padAssignment_inl
    {V : Type u} {I : Type v}
    [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]
    (P : ClusterAssignment V I)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (threshold : ℕ) (i : I) :
    largeVertexReservoir (padAssignment P) G threshold (Sum.inl i) =
      largeVertexReservoir P G threshold i := by
  simp [largeVertexReservoir]

@[simp] theorem largeVertexReservoir_padAssignment_inr
    {V : Type u} {I : Type v}
    [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]
    (P : ClusterAssignment V I)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (threshold : ℕ) (d : Fin (paddedCard I - Fintype.card I)) :
    largeVertexReservoir (padAssignment P) G threshold (Sum.inr d) = ∅ := by
  simp [largeVertexReservoir]

/-- Quantitative largeness commutes exactly with even padding when the
reservoir quota is positive.  In particular, no empty dummy cluster can be
mistaken for a large cluster. -/
theorem largeClustersAtLeast_padAssignment
    {V : Type u} {I : Type v}
    [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]
    (P : ClusterAssignment V I)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (threshold quota : ℕ) (hquota : 0 < quota) :
    largeClustersAtLeast (padAssignment P) G threshold quota =
      padFinset (largeClustersAtLeast P G threshold quota) := by
  ext x
  cases x with
  | inl i => simp [mem_largeClustersAtLeast]
  | inr d => simp [mem_largeClustersAtLeast, hquota.ne']

/-- The two actual root reservoirs selected by the adjacent-large edge in a
padded Claim-6.7 certificate.  The returned cluster indices are original
indices, not padding vertices. -/
theorem exists_adjacent_original_quantitative_root_reservoirs
    {V : Type u} {I : Type v}
    [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]
    (P : ClusterAssignment V I)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : SimpleGraph I) [DecidableRel R.Adj]
    (threshold quota miss : ℕ)
    (C : Claim67Certificate (padGraph R)
      (padFinset (largeClustersAtLeast P G threshold quota)) miss) :
    ∃ A B : I,
      A ∈ largeClustersAtLeast P G threshold quota ∧
      B ∈ largeClustersAtLeast P G threshold quota ∧
      R.Adj A B ∧
      largeVertexReservoir P G threshold A ⊆ clusterVertices P A ∧
      quota ≤ (largeVertexReservoir P G threshold A).card ∧
      (∀ z ∈ largeVertexReservoir P G threshold A,
        threshold ≤ G.degree z) ∧
      largeVertexReservoir P G threshold B ⊆ clusterVertices P B ∧
      quota ≤ (largeVertexReservoir P G threshold B).card ∧
      (∀ z ∈ largeVertexReservoir P G threshold B,
        threshold ≤ G.degree z) ∧
      Disjoint (largeVertexReservoir P G threshold A)
        (largeVertexReservoir P G threshold B) := by
  classical
  obtain ⟨A', hA', B', hB', hAB⟩ := C.adjacentLarge
  have hApad : A' ∈ padFinset
      (largeClustersAtLeast P G threshold quota) :=
    (Finset.mem_inter.mp hA').1
  have hBpad : B' ∈ padFinset
      (largeClustersAtLeast P G threshold quota) :=
    (Finset.mem_inter.mp hB').1
  obtain ⟨A, hAL, hAeq⟩ := Finset.mem_map.mp hApad
  obtain ⟨B, hBL, hBeq⟩ := Finset.mem_map.mp hBpad
  subst A'
  subst B'
  have hAB' : R.Adj A B := by
    simpa using hAB
  have hAspec := reservoir_spec_of_mem_largeClustersAtLeast
    P G threshold quota hAL
  have hBspec := reservoir_spec_of_mem_largeClustersAtLeast
    P G threshold quota hBL
  have hdisjoint : Disjoint (largeVertexReservoir P G threshold A)
      (largeVertexReservoir P G threshold B) :=
    (Erdos547b.ZhaoSection6Dichotomy.clusterVertices_disjoint P hAB'.ne).mono
      hAspec.1 hBspec.1
  exact ⟨A, B, hAL, hBL, hAB', hAspec.1, hAspec.2.1,
    hAspec.2.2, hBspec.1, hBspec.2.1, hBspec.2.2, hdisjoint⟩

end Erdos547b.ZhaoLemma65QuantitativeRoots

#print axioms Erdos547b.ZhaoLemma65QuantitativeRoots.largeClustersAtLeast_padAssignment
#print axioms Erdos547b.ZhaoLemma65QuantitativeRoots.exists_adjacent_original_quantitative_root_reservoirs
