/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ReserveStrongWellDistributed
import ErdosProblems.Erdos207.SimultaneousLinkCoverLaw

/-!
# Reserve-edge accounting for the simultaneous link cover

Every link triangle has one vertex outside the next vortex set and two
vertices inside it.  Hence exactly two of its three graph edges are crossing
edges.  For a packing these two-edge blocks are pairwise disjoint, so a
prescribed family of `t` link triangles forces exactly `2 * t` of the reserve
bits exposed earlier in the master iteration.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- The crossing graph edges belonging to one triple. -/
noncomputable def tripleCrossingEdges
    {V : Type*} [DecidableEq V] (U : Finset V) (T : TripleOn V) :
    Finset (Sym2 V) := by
  classical
  exact (tripleEdgeFinset T).filter (IsCrossingEdge U)

/-- All crossing graph edges belonging to a family of triples. -/
def familyCrossingEdges
    {V : Type*} [DecidableEq V] (U : Finset V)
    (Q : TripleSystemOn V) : Finset (Sym2 V) :=
  Q.biUnion (tripleCrossingEdges U)

@[simp]
lemma isCrossingEdge_mk_iff
    {V : Type*} [DecidableEq V] {U : Finset V} {u v : V} :
    IsCrossingEdge U s(u, v) ↔
      (u ∈ U ∧ v ∉ U) ∨ (v ∈ U ∧ u ∉ U) := by
  rw [IsCrossingEdge, Sym2.toFinset_mk_eq]
  simp only [Finset.Nonempty]
  aesop

lemma tripleCrossingEdges_linkMatchingTriple
    {A B V : Type*} [Fintype V] [DecidableEq V]
    {U : Finset V} {center : V} {left : A ↪ V} {right : B ↪ V}
    {hcenterLeft : ∀ a, center ≠ left a}
    {hcenterRight : ∀ b, center ≠ right b}
    {hleftRight : ∀ a b, left a ≠ right b}
    (hout : center ∉ U) (a : A) (b : B)
    (hleft : left a ∈ U) (hright : right b ∈ U) :
    tripleCrossingEdges U
        (linkMatchingTriple center left right hcenterLeft hcenterRight
          hleftRight a b) =
      {s(center, left a), s(center, right b)} := by
  classical
  ext e
  induction e using Sym2.ind with
  | h x y =>
      simp only [tripleCrossingEdges, mem_filter,
        mk_mem_tripleEdgeFinset_iff, mem_insert, mem_singleton]
      simp only [mem_linkMatchingTriple_iff]
      rw [isCrossingEdge_mk_iff]
      aesop

lemma card_tripleCrossingEdges_linkMatchingTriple
    {A B V : Type*} [Fintype V] [DecidableEq V]
    {U : Finset V} {center : V} {left : A ↪ V} {right : B ↪ V}
    {hcenterLeft : ∀ a, center ≠ left a}
    {hcenterRight : ∀ b, center ≠ right b}
    {hleftRight : ∀ a b, left a ≠ right b}
    (hout : center ∉ U) (a : A) (b : B)
    (hleft : left a ∈ U) (hright : right b ∈ U) :
    (tripleCrossingEdges U
        (linkMatchingTriple center left right hcenterLeft hcenterRight
          hleftRight a b)).card = 2 := by
  rw [tripleCrossingEdges_linkMatchingTriple hout a b hleft hright]
  rw [card_insert_of_notMem]
  · simp
  · simp only [mem_singleton, Sym2.eq_iff]
    aesop

/-- A triple family consists only of triples from the indicated collection
of bipartite links. -/
def IsSimultaneousLinkFamily
    {O V : Type*} [DecidableEq V] (K : O → BipartiteLink V)
    (M : TripleSystemOn V) : Prop :=
  ∀ T ∈ M, ∃ x : SimultaneousLinkPair O V K,
    T = simultaneousLinkPairTriple K x

lemma simultaneousLinkReservoir_isSimultaneousLinkFamily
    {O V : Type*} [Fintype O] [DecidableEq O]
    [Fintype V] [DecidableEq V]
    (U : Finset V) (center : O ↪ V) (K : O → BipartiteLink V)
    (hcenter : ∀ o, (K o).center = center o)
    (hout : ∀ o, center o ∉ U)
    (hleft : ∀ o, (K o).left ⊆ U)
    (hright : ∀ o, (K o).right ⊆ U)
    (omega : SimultaneousLinkPair O V K → Bool) :
    IsSimultaneousLinkFamily K
      (simultaneousLinkReservoir U center K hcenter hout hleft hright
        omega) := by
  intro T hT
  rw [simultaneousLinkReservoir, encodedReservoir, mem_map] at hT
  obtain ⟨x, _hx, rfl⟩ := hT
  exact ⟨x, rfl⟩

/-- Conditioning a simultaneous reservoir on any positive good event and
selecting a valid cover produces a law which remembers both cover validity
and the fact that every output triangle is a genuine link triangle. -/
theorem exists_simultaneousLinkCoverFamilyLaw_of_good_reservoir_pow
    {O V : Type*} [Fintype O] [DecidableEq O]
    [Fintype V] [DecidableEq V]
    (U : Finset V) (center : O ↪ V) (K : O → BipartiteLink V)
    (hcenter : ∀ o, (K o).center = center o)
    (hout : ∀ o, center o ∉ U)
    (hleft : ∀ o, (K o).left ⊆ U)
    (hright : ∀ o, (K o).right ⊆ U)
    (F : ForbiddenFamilyOn V) (available P : TripleSystemOn V)
    (sigma : ℝ≥0) (hsigma : sigma ≤ 1)
    (Good : (SimultaneousLinkPair O V K → Bool) → Prop)
    (hGood : 0 < (FiniteLaw.independentBits
      (fun _ : SimultaneousLinkPair O V K ↦ sigma)
      (fun _ ↦ hsigma)).probability Good)
    (hcover : ∀ omega, Good omega → ∃ M : TripleSystemOn V,
      M ⊆ simultaneousLinkReservoir U center K hcenter hout hleft hright
        omega ∧
      IsSimultaneousLinkCover F available P K M) :
    ∃ law : FiniteLaw (TripleSystemOn V),
      law.SupportedOn (fun M ↦
        IsSimultaneousLinkCover F available P K M ∧
          IsSimultaneousLinkFamily K M) ∧
      ∀ Q : TripleSystemOn V,
        law.probability (fun M ↦ Q ⊆ M) ≤
          (sigma /
            (FiniteLaw.independentBits
              (fun _ : SimultaneousLinkPair O V K ↦ sigma)
              (fun _ ↦ hsigma)).probability Good) ^ Q.card := by
  apply exists_conditioned_encodedSelectionLaw_pow sigma hsigma
    (simultaneousLinkPairEmbedding U center K hcenter hout hleft hright)
      Good hGood
      (fun M ↦ IsSimultaneousLinkCover F available P K M ∧
        IsSimultaneousLinkFamily K M)
  intro omega homega
  obtain ⟨M, hMsub, hMcover⟩ := hcover omega homega
  refine ⟨M, hMsub, hMcover, ?_⟩
  intro T hTM
  exact simultaneousLinkReservoir_isSimultaneousLinkFamily
    U center K hcenter hout hleft hright omega T (hMsub hTM)

lemma IsSimultaneousLinkFamily.mono
    {O V : Type*} [DecidableEq V] {K : O → BipartiteLink V}
    {M Q : TripleSystemOn V} (hM : IsSimultaneousLinkFamily K M)
    (hQM : Q ⊆ M) : IsSimultaneousLinkFamily K Q := by
  intro T hT
  exact hM T (hQM hT)

lemma IsSimultaneousLinkFamily.card_tripleCrossingEdges
    {O V : Type*} [Fintype V] [DecidableEq V]
    {U : Finset V} {center : O ↪ V} {K : O → BipartiteLink V}
    (hcenter : ∀ o, (K o).center = center o)
    (hout : ∀ o, center o ∉ U)
    (hleft : ∀ o, (K o).left ⊆ U)
    (hright : ∀ o, (K o).right ⊆ U)
    {M : TripleSystemOn V} (hM : IsSimultaneousLinkFamily K M)
    {T : TripleOn V} (hT : T ∈ M) :
    (tripleCrossingEdges U T).card = 2 := by
  obtain ⟨⟨o, a, b⟩, rfl⟩ := hM T hT
  apply card_tripleCrossingEdges_linkMatchingTriple
    (a := a) (b := b)
  · simpa only [hcenter o] using hout o
  · exact hleft o a.2
  · exact hright o b.2

lemma IsPackingOn.pairwiseDisjoint_tripleCrossingEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    {U : Finset V} {Q : TripleSystemOn V} (hQ : IsPackingOn Q) :
    (Q : Set (TripleOn V)).PairwiseDisjoint (tripleCrossingEdges U) := by
  classical
  intro T hT S hS hTS
  change Disjoint (tripleCrossingEdges U T) (tripleCrossingEdges U S)
  rw [Finset.disjoint_left]
  intro e heT heS
  have hpair := hQ.isTriangleDecomposition.pairwiseDisjoint_tripleEdgeFinset
    hT hS hTS
  exact Finset.disjoint_left.mp hpair
    (mem_filter.mp heT).1 (mem_filter.mp heS).1

/-- The outcome-independent structural predicate needed for reserve
accounting: the family is a packing and every one of its triples has exactly
two crossing edges. -/
def IsTwoCrossingPacking
    {V : Type*} [Fintype V] [DecidableEq V]
    (U : Finset V) (Q : TripleSystemOn V) : Prop :=
  IsPackingOn Q ∧ ∀ T ∈ Q, (tripleCrossingEdges U T).card = 2

lemma IsTwoCrossingPacking.card_familyCrossingEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    {U : Finset V} {Q : TripleSystemOn V}
    (hQ : IsTwoCrossingPacking U Q) :
    (familyCrossingEdges U Q).card = 2 * Q.card := by
  rw [familyCrossingEdges,
    card_biUnion hQ.1.pairwiseDisjoint_tripleCrossingEdges]
  calc
    ∑ T ∈ Q, (tripleCrossingEdges U T).card = ∑ _T ∈ Q, 2 := by
      apply sum_congr rfl
      exact hQ.2
    _ = 2 * Q.card := by simp [mul_comm]

/-- A packing of link triangles contributes two distinct crossing edges per
triangle, both within a triangle and between different triangles. -/
lemma IsSimultaneousLinkFamily.card_familyCrossingEdges
    {O V : Type*} [Fintype V] [DecidableEq V]
    {U : Finset V} {center : O ↪ V} {K : O → BipartiteLink V}
    (hcenter : ∀ o, (K o).center = center o)
    (hout : ∀ o, center o ∉ U)
    (hleft : ∀ o, (K o).left ⊆ U)
    (hright : ∀ o, (K o).right ⊆ U)
    {Q : TripleSystemOn V} (hfamily : IsSimultaneousLinkFamily K Q)
    (hpacking : IsPackingOn Q) :
    (familyCrossingEdges U Q).card = 2 * Q.card := by
  apply IsTwoCrossingPacking.card_familyCrossingEdges
  exact ⟨hpacking, fun T hT ↦
    hfamily.card_tripleCrossingEdges hcenter hout hleft hright hT⟩

lemma IsSimultaneousLinkFamily.isTwoCrossingPacking
    {O V : Type*} [Fintype V] [DecidableEq V]
    {U : Finset V} {center : O ↪ V} {K : O → BipartiteLink V}
    (hcenter : ∀ o, (K o).center = center o)
    (hout : ∀ o, center o ∉ U)
    (hleft : ∀ o, (K o).left ⊆ U)
    (hright : ∀ o, (K o).right ⊆ U)
    {Q : TripleSystemOn V} (hfamily : IsSimultaneousLinkFamily K Q)
    (hpacking : IsPackingOn Q) : IsTwoCrossingPacking U Q :=
  ⟨hpacking, fun T hT ↦
    hfamily.card_tripleCrossingEdges hcenter hout hleft hright hT⟩

/-- Use zero for a structurally impossible prescribed family and the C4
power for a genuine two-crossing packing. -/
noncomputable def twoCrossingPackingBound
    {V : Type*} [Fintype V] [DecidableEq V]
    (U : Finset V) (alpha : ℝ≥0) (Q : TripleSystemOn V) : ℝ≥0 := by
  classical
  exact if IsTwoCrossingPacking U Q then alpha ^ Q.card else 0

/-- Every spoke edge of a bipartite link belongs to the indicated reserve. -/
def BipartiteLink.SpokesIn
    {V : Type*} [DecidableEq V] (K : BipartiteLink V)
    (reserve : Finset (Sym2 V)) : Prop :=
  (∀ x ∈ K.left, s(K.center, x) ∈ reserve) ∧
    ∀ x ∈ K.right, s(K.center, x) ∈ reserve

/-- Every crossing edge of a link family is one of its spoke edges, hence is
present in any reserve supporting all the links. -/
lemma IsSimultaneousLinkFamily.familyCrossingEdges_subset
    {O V : Type*} [Fintype V] [DecidableEq V]
    {U : Finset V} {center : O ↪ V} {K : O → BipartiteLink V}
    (hcenter : ∀ o, (K o).center = center o)
    (hout : ∀ o, center o ∉ U)
    (hleft : ∀ o, (K o).left ⊆ U)
    (hright : ∀ o, (K o).right ⊆ U)
    {M : TripleSystemOn V} (hfamily : IsSimultaneousLinkFamily K M)
    {reserve : Finset (Sym2 V)}
    (hspokes : ∀ o, (K o).SpokesIn reserve) :
    familyCrossingEdges U M ⊆ reserve := by
  intro e he
  obtain ⟨T, hTM, heT⟩ := mem_biUnion.mp he
  obtain ⟨⟨o, a, b⟩, rfl⟩ := hfamily T hTM
  have heq := tripleCrossingEdges_linkMatchingTriple
    (U := U) (center := (K o).center)
    (left := (K o).leftEmbedding) (right := (K o).rightEmbedding)
    (hcenterLeft := (K o).center_ne_left)
    (hcenterRight := (K o).center_ne_right)
    (hleftRight := (K o).left_ne_right)
    (by simpa only [hcenter o] using hout o) a b
    (hleft o a.2) (hright o b.2)
  rw [simultaneousLinkPairTriple, heq] at heT
  rcases mem_insert.mp heT with heT | heT
  · rw [heT]
    change s((K o).center, a.1) ∈ reserve
    exact (hspokes o).1 a.1 a.2
  · rw [mem_singleton.mp heT]
    change s((K o).center, b.1) ∈ reserve
    exact (hspokes o).2 b.1 b.2

end

end Erdos207
