/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.LocalForbiddenLegality
import ErdosProblems.Erdos207.StoppedGreedyStateLaw
import ErdosProblems.Erdos207.ProcessedSimultaneousLinkControls

/-! # Every supported local nibble state is globally legal -/

namespace Erdos207

open Finset

noncomputable section

theorem localNibble_global_structure
    {V : Type*} [DecidableEq V] {F : ForbiddenFamilyOn V}
    {A P M : TripleSystemOn V} {q : ℕ} {G : SimpleGraph V}
    (horder : ∀ C ∈ F, C.card + 2 ≤ q)
    (hP : IsPackingOn P) (hPavoid : AvoidsForbidden P F)
    (hsingle : ∀ T ∈ A, ¬ CompletesForbidden F P T)
    (hgraph : G ≤ leaveGraph P) (htri : ConsistsOfTriangles G A)
    (hMA : M ⊆ A) (hM : IsPackingOn M)
    (hlocal : AvoidsForbidden M ((Icc 4 q).biUnion (localForbiddenConfigurations F A P))) :
    IsPackingOn (P ∪ M) ∧ Disjoint P M ∧ AvoidsForbidden (P ∪ M) F := by
  have hcross : ∀ T ∈ M, TriangleAvoidsGraph (coveredGraph P) T :=
    fun _ hT ↦ htri.triangleAvoids_coveredGraph_of_le_leave hgraph (hMA hT)
  exact ⟨hP.union_of_triangleAvoidsCovered hM hcross,
    disjoint_of_triangleAvoidsCovered hcross,
    avoids_union_of_avoids_localForbiddenUnion horder hPavoid hsingle hMA hlocal⟩

theorem stoppedGreedyStateLaw_supported_global_localLegality
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {A P : TripleSystemOn V} {q : ℕ} {G : SimpleGraph V}
    (n : ℕ) (Lstar : ℕ → Finset (Finset {T // T ∈ A}))
    (active : ℕ → GreedyStateOn V → Prop) (S₀ : GreedyStateOn V)
    (hInv : GreedyInvariant (regularizedForbiddenUnion
      (Function.Embedding.subtype (fun T ↦ T ∈ A)) q Lstar) S₀)
    (hchosen : S₀.chosen = ∅) (havailable : S₀.available = A)
    (horder : ∀ C ∈ F, C.card + 2 ≤ q)
    (hP : IsPackingOn P) (hPavoid : AvoidsForbidden P F)
    (hsingle : ∀ T ∈ A, ¬ CompletesForbidden F P T)
    (hgraph : G ≤ leaveGraph P) (htri : ConsistsOfTriangles G A)
    (hcovers : ∀ j ∈ Icc 4 q,
      ∀ E ∈ finiteHypergraphOnSubset A (localForbiddenConfigurations F A P j),
        ∃ C ∈ (Ico 4 j).biUnion Lstar ∪ Lstar j, C ⊆ E) :
    (stoppedGreedyStateLaw n (regularizedForbiddenUnion
      (Function.Embedding.subtype (fun T ↦ T ∈ A)) q Lstar) active S₀).SupportedOn
      (fun S ↦ S.chosen ⊆ A ∧ IsPackingOn (P ∪ S.chosen) ∧
        Disjoint P S.chosen ∧ AvoidsForbidden (P ∪ S.chosen) F) := by
  have hsupp := stoppedGreedyStateLaw_supported n _ active S₀ hInv hchosen
  intro S hmass
  obtain ⟨hSinv, _hSavailable, hSA⟩ := hsupp S hmass
  rw [havailable] at hSA
  have hlocal := avoids_original_union_of_regularized
    (Function.Embedding.subtype (fun T ↦ T ∈ A)) q
    (fun j ↦ finiteHypergraphOnSubset A (localForbiddenConfigurations F A P j))
    Lstar hcovers S.chosen hSinv.2.1
  rw [regularizedForbiddenUnion_local_decode] at hlocal
  exact ⟨hSA, localNibble_global_structure horder hP hPavoid hsingle hgraph htri hSA hSinv.1 hlocal⟩

end

end Erdos207
