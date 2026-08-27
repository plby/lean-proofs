/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.LinkInnerEdgeSampling
import ErdosProblems.Erdos207.SourceQuasiMarking
import ErdosProblems.Erdos207.MasterLinkDegreeLoss
import ErdosProblems.Erdos207.ReserveProtectedPreliminaryGeometry

/-! # Later-level degree damage comes only from the final link inner edges -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

theorem TrianglesMeetAtMostOne.not_covered_adj
    {V : Type*} [DecidableEq V] {U : Finset V} {P : TripleSystemOn V}
    (h : TrianglesMeetAtMostOne U P) {v w : V} (hv : v ∈ U) (hw : w ∈ U) :
    ¬ (coveredGraph P).Adj v w := by
  rintro ⟨T, hT, hvT, hwT, hvw⟩
  exact hvw (h T hT hvT hv hwT hw)

theorem NewTrianglesUseScheduledOuterEdges.meetAtMostOne
    {V : Type*} [Fintype V] [DecidableEq V] {U : Finset V} {E : Finset (Sym2 V)}
    {P Q : TripleSystemOn V} (hP : TrianglesMeetAtMostOne U P)
    (houter : ∀ e ∈ E, e.out.1 ∉ U ∧ e.out.2 ∉ U)
    (huse : NewTrianglesUseScheduledOuterEdges U E P Q) : TrianglesMeetAtMostOne U Q := by
  intro T hT x y hxT hxU hyT hyU
  by_cases hTP : T ∈ P
  · exact hP T hTP hxT hxU hyT hyU
  obtain ⟨e, he, hne, w, _, rfl⟩ := huse T (mem_sdiff.mpr ⟨hT, hTP⟩)
  have heOut := houter e he
  have hx : x = w.1 := by
    simp only [internalEdgeTriangle, thirdVertexTriple, tripleOfThree, mem_insert, mem_singleton] at hxT
    rcases hxT with rfl | rfl | hx
    · exact (heOut.1 hxU).elim
    · exact (heOut.2 hxU).elim
    · exact hx
  have hy : y = w.1 := by
    simp only [internalEdgeTriangle, thirdVertexTriple, tripleOfThree, mem_insert, mem_singleton] at hyT
    rcases hyT with rfl | rfl | hy
    · exact (heOut.1 hyU).elim
    · exact (heOut.2 hyU).elim
    · exact hy
  exact hx.trans hy.symm

theorem card_removedNeighbors_le_local_inner_edges
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U S : Finset V) (P M : TripleSystemOn V) (v : V)
    (hv : v ∈ U) (hS : S ⊆ U) (hP : TrianglesMeetAtMostOne U P) :
    (neighborsIn G S v \ neighborsIn (updatedStageGraph G U (P ∪ M)) S v).card ≤
      (sourceQuasiSpokes S v ∩ M.biUnion tripleEdgeFinset).card := by
  apply card_le_card_of_injOn (f := fun w ↦ s(v, w))
  · intro w hw
    have hwS := (mem_neighborsIn_iff.mp (mem_sdiff.mp hw).1).1
    have hcover := removedNeighbors_subset_coveredNeighborFinset G U S (P ∪ M) v hv hS hw
    have hcover' : (coveredGraph (P ∪ M)).Adj v w := by
      simpa only [SimpleGraph.mem_neighborFinset] using hcover
    obtain ⟨T, hT, hvT, hwT, hvw⟩ := coveredGraph_adj.mp hcover'
    have hTM : T ∈ M := by
      rcases mem_union.mp hT with hTP | hTM
      · exact (hvw (hP T hTP hvT hv hwT (hS hwS))).elim
      · exact hTM
    exact mem_inter.mpr ⟨mem_image.mpr ⟨w, hwS, rfl⟩,
      mem_biUnion.mpr ⟨T, hTM, mk_mem_tripleEdgeFinset_iff.mpr ⟨hvT, hwT, hvw⟩⟩⟩
  · intro w _ z _ heq
    have hh : (v = v ∧ w = z) ∨ (v = z ∧ w = v) := by simpa only [Sym2.eq_iff] using heq
    exact hh.elim And.right (fun h ↦ h.2.trans h.1)

theorem FiniteLaw.probability_local_removed_neighbors_ge_le
    {Ω O V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V]
    (L : FiniteLaw Ω) (selected : Ω → TripleSystemOn V)
    (K : O → BipartiteLink V) (U : Finset V) (hout : ∀ o, (K o).center ∉ U)
    (A : TripleSystemOn V) (hA : IsSimultaneousLinkFamily K A)
    (hselected : L.SupportedOn fun ω ↦ selected ω ⊆ A)
    (sigma : ℝ≥0) (hjoint : ∀ Q : TripleSystemOn V,
      L.probability (fun ω ↦ Q ⊆ selected ω) ≤ sigma ^ Q.card)
    (G : SimpleGraph V) (P : TripleSystemOn V) (hP : TrianglesMeetAtMostOne U P)
    (S : Finset V) (v : V) (hv : v ∈ U) (hS : S ⊆ U)
    (M : ℕ) (hM : ∀ e ∈ sourceQuasiSpokes S v, (linkInnerEdgeFan A e).card ≤ M)
    (s R : ℕ) (hR : 0 < R) (hs : 2*s ≤ R) :
    L.probability (fun ω ↦ R ≤
      (neighborsIn G S v \ neighborsIn (updatedStageGraph G U (P ∪ selected ω)) S v).card) ≤
      (2 * (S.card : ℝ≥0) * M * sigma / R) ^ s := by
  have hinner : ∀ e ∈ sourceQuasiSpokes S v, e.toFinset ⊆ U := by
    intro e he
    obtain ⟨w, hw, rfl⟩ := mem_image.mp he
    simpa only [Sym2.toFinset_mk_eq, insert_subset_iff, singleton_subset_iff] using And.intro hv (hS hw)
  have hb := L.probability_internal_link_edges_card_ge_le selected K U hout A hA hselected sigma hjoint
    (sourceQuasiSpokes S v) hinner M hM s R hR hs
  rw [sourceQuasiSpokes_card] at hb
  apply le_trans _ hb
  apply L.probability_mono
  intro ω hω
  exact hω.trans (card_removedNeighbors_le_local_inner_edges G U S P (selected ω) v hv hS hP)

theorem FiniteLaw.probability_local_removed_neighbors_real_ge_le
    {Ω O V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V]
    (L : FiniteLaw Ω) (selected : Ω → TripleSystemOn V)
    (K : O → BipartiteLink V) (U : Finset V) (hout : ∀ o, (K o).center ∉ U)
    (A : TripleSystemOn V) (hA : IsSimultaneousLinkFamily K A)
    (hselected : L.SupportedOn fun ω ↦ selected ω ⊆ A)
    (sigma : ℝ≥0) (hjoint : ∀ Q : TripleSystemOn V,
      L.probability (fun ω ↦ Q ⊆ selected ω) ≤ sigma ^ Q.card)
    (G : SimpleGraph V) (P : TripleSystemOn V) (hP : TrianglesMeetAtMostOne U P)
    (S : Finset V) (v : V) (hv : v ∈ U) (hS : S ⊆ U)
    (M : ℕ) (hM : ∀ e ∈ sourceQuasiSpokes S v, (linkInnerEdgeFan A e).card ≤ M)
    (s : ℕ) (R : ℝ≥0) (hR : 0 < R) (hs : 2*s ≤ R) :
    L.probability (fun ω ↦ R ≤
      (neighborsIn G S v \ neighborsIn (updatedStageGraph G U (P ∪ selected ω)) S v).card) ≤
      (2 * (S.card : ℝ≥0) * M * sigma / R) ^ s := by
  have hceil : 0 < Nat.ceil R := Nat.one_le_ceil_iff.mpr hR
  have hsceil : 2*s ≤ Nat.ceil R := by
    have hb : ((2*s : ℕ) : ℝ≥0) ≤ Nat.ceil R := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using hs.trans (Nat.le_ceil R)
    exact_mod_cast hb
  have hb := L.probability_local_removed_neighbors_ge_le selected K U hout A hA hselected sigma hjoint
    G P hP S v hv hS M hM s (Nat.ceil R) hceil hsceil
  have hmono : L.probability (fun ω ↦ R ≤
      (neighborsIn G S v \ neighborsIn (updatedStageGraph G U (P ∪ selected ω)) S v).card) ≤
      L.probability (fun ω ↦ Nat.ceil R ≤
        (neighborsIn G S v \ neighborsIn (updatedStageGraph G U (P ∪ selected ω)) S v).card) := by
    apply L.probability_mono
    intro ω hω
    exact Nat.ceil_le.mpr hω
  apply (hmono.trans hb).trans
  gcongr
  exact Nat.le_ceil R

end

end Erdos207
