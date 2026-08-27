/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.DynamicCrossingLink

/-!
# Dynamic crossing-link covers with a threaded invariant

The residual bipartition at a center depends on the matchings selected at
all earlier centers.  This iterator exposes the processed-center set and the
current packing to the step theorem, and carries an arbitrary invariant to
the terminal packing.
-/

namespace Erdos207

open Finset

noncomputable section

private lemma coveredGraph_mono_invariant
    {V : Type*} [DecidableEq V]
    {P Q : TripleSystemOn V} (hPQ : P ⊆ Q) :
    coveredGraph P ≤ coveredGraph Q := by
  intro u v huv
  obtain ⟨T, hTP, huT, hvT, huv⟩ := coveredGraph_adj.mp huv
  exact coveredGraph_adj.mpr ⟨T, hPQ hTP, huT, hvT, huv⟩

/-- Finite state-dependent link composition carrying an arbitrary invariant
indexed by the set of centers already processed. -/
theorem exists_dynamic_crossingLinkCover_with_invariant
    {O V : Type*} [Fintype O] [DecidableEq O]
    [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (center : O → V)
    (F : ForbiddenFamilyOn V) (available P₀ : TripleSystemOn V)
    (invariant : Finset O → TripleSystemOn V → Prop)
    (hP₀packing : IsPackingOn P₀) (hP₀avoid : AvoidsForbidden P₀ F)
    (hinitial : invariant ∅ P₀)
    (hstep : ∀ (S : Finset O) (P : TripleSystemOn V),
      invariant S P →
      P₀ ⊆ P → P ⊆ P₀ ∪ available →
      IsPackingOn P → AvoidsForbidden P F →
      ∀ o : O, o ∉ S →
        ∃ K : BipartiteLink V,
          IsResidualBipartition G P (center o) K ∧
          ∃ L : TripleSystemOn V,
            L ⊆ available ∧ Disjoint P L ∧
            IsPackingOn (P ∪ L) ∧ AvoidsForbidden (P ∪ L) F ∧
            CoversBipartiteLink K L ∧
            invariant (insert o S) (P ∪ L)) :
    ∃ M : TripleSystemOn V,
      M ⊆ available ∧ Disjoint P₀ M ∧
      IsPackingOn (P₀ ∪ M) ∧ AvoidsForbidden (P₀ ∪ M) F ∧
      (∀ o : O, ∀ w : V, G.Adj (center o) w →
        (coveredGraph (P₀ ∪ M)).Adj (center o) w) ∧
      invariant univ (P₀ ∪ M) := by
  classical
  have hind : ∀ S : Finset O, ∃ P : TripleSystemOn V,
      invariant S P ∧
      P₀ ⊆ P ∧ P ⊆ P₀ ∪ available ∧
      IsPackingOn P ∧ AvoidsForbidden P F ∧
      ∀ o ∈ S, ∀ w : V, G.Adj (center o) w →
        (coveredGraph P).Adj (center o) w := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
        refine ⟨P₀, hinitial, Subset.rfl, subset_union_left,
          hP₀packing, hP₀avoid, ?_⟩
        simp
    | @insert o S ho ih =>
        obtain ⟨P, hInv, hP₀P, hPsub, hPpacking, hPavoid, hcovered⟩ := ih
        obtain ⟨K, hK, L, hLavailable, hPLdisjoint, hPLpacking,
          hPLavoid, hLcover, hInv'⟩ :=
          hstep S P hInv hP₀P hPsub hPpacking hPavoid o ho
        let P' := P ∪ L
        have hP₀P' : P₀ ⊆ P' := hP₀P.trans subset_union_left
        have hP'sub : P' ⊆ P₀ ∪ available := by
          intro T hT
          rcases mem_union.mp hT with hTP | hTL
          · exact hPsub hTP
          · exact mem_union_right P₀ (hLavailable hTL)
        refine ⟨P', hInv', hP₀P', hP'sub, hPLpacking, hPLavoid, ?_⟩
        intro j hj w hjw
        rw [mem_insert] at hj
        rcases hj with rfl | hjS
        · by_cases hcoveredP : (coveredGraph P).Adj (center j) w
          · exact coveredGraph_mono_invariant subset_union_left hcoveredP
          · have hwres : w ∈ residualNeighbors G P (center j) :=
              mem_residualNeighbors_iff.mpr ⟨hjw, hcoveredP⟩
            have hcoveredL :=
              hLcover.covers_residualNeighbors_of_partition hK w hwres
            exact coveredGraph_mono_invariant subset_union_right hcoveredL
        · exact coveredGraph_mono_invariant subset_union_left
            (hcovered j hjS w hjw)
  obtain ⟨P, hInv, hP₀P, hPsub, hPpacking, hPavoid, hcovered⟩ :=
    hind (univ : Finset O)
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
  refine ⟨M, hMavailable, hdisjoint, ?_, ?_, ?_, ?_⟩
  · simpa only [hP₀M] using hPpacking
  · simpa only [hP₀M] using hPavoid
  · intro o w how
    simpa only [hP₀M] using hcovered o (mem_univ o) w how
  · simpa only [hP₀M] using hInv

end

end Erdos207
