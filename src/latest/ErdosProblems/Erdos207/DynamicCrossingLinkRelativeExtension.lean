/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.DynamicCrossingLinkInvariant
import ErdosProblems.Erdos207.LinkReservoirPointWeight
import ErdosProblems.Erdos207.RelativeExtensionMonotonicity

/-!
# A relative-extension invariant for a dynamic center sweep

At a partially completed sweep the point weight is the sum of the base
future weight and the indicator weights of the unprocessed centers.  Since
an injectively indexed triple contains at most three centers, the initial
weight is bounded by `3 * sigma + baseWeight`; at the terminal state only
the base weight remains.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- Thread the remaining-center extension weight through a dynamic link
sweep.  All probabilistic and link-specific work is isolated in `hstep`. -/
theorem exists_dynamic_crossingLinkCover_with_relativeExtension
    {O V J : Type*} [Fintype O] [DecidableEq O]
    [Fintype V] [Fintype J] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (center : O → V) (hcenterInjective : Function.Injective center)
    (F : ForbiddenFamilyOn V) (available P₀ : TripleSystemOn V)
    (configurations : J → TripleSystemOn V)
    (sigma : ℝ≥0) (baseWeight : TripleOn V → ℝ≥0)
    (kappa : Finset O → ℝ≥0)
    (hP₀packing : IsPackingOn P₀) (hP₀avoid : AvoidsForbidden P₀ F)
    (hinitial : HasExtensionBound (fun j ↦ configurations j \ P₀)
      (fun T ↦ 3 * sigma + baseWeight T) (kappa ∅))
    (hstep : ∀ (S : Finset O) (P : TripleSystemOn V),
      P₀ ⊆ P → P ⊆ P₀ ∪ available →
      IsPackingOn P → AvoidsForbidden P F →
      HasExtensionBound (fun j ↦ configurations j \ P)
        (fun T ↦ centerIndexedTriangleWeight center (univ \ S) sigma T +
          baseWeight T)
        (kappa S) →
      ∀ o : O, o ∉ S →
        ∃ K : BipartiteLink V,
          IsResidualBipartition G P (center o) K ∧
          ∃ L : TripleSystemOn V,
            L ⊆ available ∧ Disjoint P L ∧
            IsPackingOn (P ∪ L) ∧ AvoidsForbidden (P ∪ L) F ∧
            CoversBipartiteLink K L ∧
            HasExtensionBound (fun j ↦ configurations j \ (P ∪ L))
              (fun T ↦ centerIndexedTriangleWeight center
                  (univ \ insert o S) sigma T + baseWeight T)
              (kappa (insert o S))) :
    ∃ M : TripleSystemOn V,
      M ⊆ available ∧ Disjoint P₀ M ∧
      IsPackingOn (P₀ ∪ M) ∧ AvoidsForbidden (P₀ ∪ M) F ∧
      (∀ o : O, ∀ w : V, G.Adj (center o) w →
        (coveredGraph (P₀ ∪ M)).Adj (center o) w) ∧
      HasExtensionBound (fun j ↦ configurations j \ (P₀ ∪ M))
        baseWeight (kappa univ) := by
  classical
  let Inv : Finset O → TripleSystemOn V → Prop := fun S P ↦
    HasExtensionBound (fun j ↦ configurations j \ P)
      (fun T ↦ centerIndexedTriangleWeight center (univ \ S) sigma T +
        baseWeight T)
      (kappa S)
  have hInvInitial : Inv ∅ P₀ := by
    apply hinitial.mono_weight
    intro T
    simp only [Inv, sdiff_empty]
    exact add_le_add
      (centerIndexedTriangleWeight_le_three center hcenterInjective
        univ sigma T)
      le_rfl
  obtain ⟨M, hMavailable, hdisjoint, hpacking, havoid,
      hcovered, hInvFinal⟩ :=
    exists_dynamic_crossingLinkCover_with_invariant center F available P₀
      Inv hP₀packing hP₀avoid hInvInitial (by
        intro S P hInv hP₀P hPsub hPpacking hPavoid o ho
        exact hstep S P hP₀P hPsub hPpacking hPavoid hInv o ho)
  refine ⟨M, hMavailable, hdisjoint, hpacking, havoid, hcovered, ?_⟩
  simpa [Inv, centerIndexedTriangleWeight] using hInvFinal

end

end Erdos207
