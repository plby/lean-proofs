/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ChosenCrossingLink

/-!
# Dynamically chosen residual crossing links

The balanced link at a center has to be chosen from the residual graph at the
moment that center is processed.  A link fixed before the finite iteration is
not sufficient: a triangle chosen at an earlier center can cover a spoke at a
later center.  This file gives the state-dependent finite iterator used by the
master cover-down step.
-/

namespace Erdos207

open Finset

noncomputable section

private lemma coveredGraph_mono_dynamic
    {V : Type*} [DecidableEq V]
    {P Q : TripleSystemOn V} (hPQ : P ⊆ Q) :
    coveredGraph P ≤ coveredGraph Q := by
  intro u v huv
  obtain ⟨T, hTP, huT, hvT, huv⟩ := coveredGraph_adj.mp huv
  exact coveredGraph_adj.mpr ⟨T, hPQ hTP, huT, hvT, huv⟩

/-- Finite composition of link covers where the balanced residual link is
chosen afresh from the current packing state.  The conclusion deliberately
states coverage by the enlarged total packing; the master wrapper removes the
old non-reservoir families using its leave-graph invariant. -/
theorem exists_dynamic_crossingLinkCover
    {O V : Type*} [Fintype O] [DecidableEq O]
    [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (center : O → V)
    (F : ForbiddenFamilyOn V) (available P₀ : TripleSystemOn V)
    (hP₀packing : IsPackingOn P₀) (hP₀avoid : AvoidsForbidden P₀ F)
    (hstep : ∀ (P : TripleSystemOn V),
      P₀ ⊆ P → P ⊆ P₀ ∪ available →
      IsPackingOn P → AvoidsForbidden P F →
      ∀ o : O, ∃ K : BipartiteLink V,
        IsResidualBipartition G P (center o) K ∧
        HasLinkCoverExtension F available P K) :
    ∃ M : TripleSystemOn V,
      M ⊆ available ∧ Disjoint P₀ M ∧
      IsPackingOn (P₀ ∪ M) ∧ AvoidsForbidden (P₀ ∪ M) F ∧
      ∀ o : O, ∀ w : V, G.Adj (center o) w →
        (coveredGraph (P₀ ∪ M)).Adj (center o) w := by
  classical
  have hind : ∀ S : Finset O, ∃ P : TripleSystemOn V,
      P₀ ⊆ P ∧ P ⊆ P₀ ∪ available ∧
      IsPackingOn P ∧ AvoidsForbidden P F ∧
      ∀ o ∈ S, ∀ w : V, G.Adj (center o) w →
        (coveredGraph P).Adj (center o) w := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
        refine ⟨P₀, Subset.rfl, subset_union_left, hP₀packing,
          hP₀avoid, ?_⟩
        simp
    | @insert o S ho ih =>
        obtain ⟨P, hP₀P, hPsub, hPpacking, hPavoid, hcovered⟩ := ih
        obtain ⟨K, hK, L, hLavailable, hPLdisjoint, hPLpacking,
          hPLavoid, hLcover⟩ :=
          hstep P hP₀P hPsub hPpacking hPavoid o
        let P' := P ∪ L
        have hP₀P' : P₀ ⊆ P' := hP₀P.trans subset_union_left
        have hP'sub : P' ⊆ P₀ ∪ available := by
          intro T hT
          rcases mem_union.mp hT with hTP | hTL
          · exact hPsub hTP
          · exact mem_union_right P₀ (hLavailable hTL)
        refine ⟨P', hP₀P', hP'sub, hPLpacking, hPLavoid, ?_⟩
        intro j hj w hjw
        rw [mem_insert] at hj
        rcases hj with rfl | hjS
        · by_cases hcoveredP : (coveredGraph P).Adj (center j) w
          · exact coveredGraph_mono_dynamic subset_union_left hcoveredP
          · have hwres : w ∈ residualNeighbors G P (center j) :=
              mem_residualNeighbors_iff.mpr ⟨hjw, hcoveredP⟩
            have hcoveredL :=
              hLcover.covers_residualNeighbors_of_partition hK w hwres
            exact coveredGraph_mono_dynamic subset_union_right hcoveredL
        · exact coveredGraph_mono_dynamic subset_union_left
            (hcovered j hjS w hjw)
  obtain ⟨P, hP₀P, hPsub, hPpacking, hPavoid, hcovered⟩ :=
    hind (Finset.univ : Finset O)
  let M := P \ P₀
  have hMavailable : M ⊆ available := by
    intro T hTM
    have hT := hPsub (mem_sdiff.mp hTM).1
    rcases mem_union.mp hT with hTP₀ | hTA
    · exact ((mem_sdiff.mp hTM).2 hTP₀).elim
    · exact hTA
  have hP₀M : P₀ ∪ M = P := by
    ext T
    constructor
    · intro hT
      rcases mem_union.mp hT with hTP₀ | hTM
      · exact hP₀P hTP₀
      · exact (mem_sdiff.mp hTM).1
    · intro hTP
      by_cases hTP₀ : T ∈ P₀
      · exact mem_union_left M hTP₀
      · exact mem_union_right P₀ (mem_sdiff.mpr ⟨hTP, hTP₀⟩)
  have hdisjoint : Disjoint P₀ M := by
    rw [Finset.disjoint_left]
    intro T hTP₀ hTM
    exact (mem_sdiff.mp hTM).2 hTP₀
  refine ⟨M, hMavailable, hdisjoint, ?_, ?_, ?_⟩
  · simpa only [hP₀M] using hPpacking
  · simpa only [hP₀M] using hPavoid
  · intro o w how
    simpa only [hP₀M] using hcovered o (mem_univ o) w how

/-- The dynamic iterator covers every graph edge having an endpoint outside
`U`, provided the index type contains every such center. -/
theorem exists_dynamic_crossingLinkCover_outside
    {O V : Type*} [Fintype O] [DecidableEq O]
    [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {U : Finset V}
    (center : O → V) (hout : ∀ o, center o ∉ U)
    (hcomplete : ∀ v, v ∉ U → ∃ o, center o = v)
    (F : ForbiddenFamilyOn V) (available P₀ : TripleSystemOn V)
    (hP₀packing : IsPackingOn P₀) (hP₀avoid : AvoidsForbidden P₀ F)
    (hstep : ∀ (P : TripleSystemOn V),
      P₀ ⊆ P → P ⊆ P₀ ∪ available →
      IsPackingOn P → AvoidsForbidden P F →
      ∀ o : O, ∃ K : BipartiteLink V,
        IsResidualBipartition G P (center o) K ∧
        HasLinkCoverExtension F available P K) :
    ∃ M : TripleSystemOn V,
      M ⊆ available ∧ Disjoint P₀ M ∧
      IsPackingOn (P₀ ∪ M) ∧ AvoidsForbidden (P₀ ∪ M) F ∧
      ∀ u v : V, G.Adj u v → (u ∉ U ∨ v ∉ U) →
        (coveredGraph (P₀ ∪ M)).Adj u v := by
  obtain ⟨M, hMA, hdisj, hpack, havoid, hcenters⟩ :=
    exists_dynamic_crossingLinkCover center F available P₀
      hP₀packing hP₀avoid hstep
  refine ⟨M, hMA, hdisj, hpack, havoid, ?_⟩
  intro u v huv houtside
  rcases houtside with hu | hv
  · obtain ⟨o, rfl⟩ := hcomplete u hu
    exact hcenters o v huv
  · obtain ⟨o, rfl⟩ := hcomplete v hv
    exact (hcenters o u huv.symm).symm

end

end Erdos207
