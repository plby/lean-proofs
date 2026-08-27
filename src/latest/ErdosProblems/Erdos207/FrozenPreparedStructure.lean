/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.FixedEnvelopeCurrentGeometry

/-! # Global legality on every outcome of the actual frozen preliminary process -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem frozen_prepared_stopped_global_structure
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega] [Fintype V] [DecidableEq V]
    {ell : ℕ} (P : FiniteLaw Omega) (W : Vortex V ell) (current : Fin (ell + 1))
    (available old : Omega → TripleSystemOn V) [∀ omega, Nonempty {T // T ∈ available omega}]
    (F candidates envelope : ℕ → ForbiddenFamilyOn V) (y z a rho : ℕ → ℝ≥0) (q : ℕ) (gap : ℕ → ℕ)
    (Lstar : ℕ → (omega : Omega) → Finset (Finset {T // T ∈ available omega}))
    (hsupport : ∀ omega T, T ∈ available omega → T.1 ⊆ W.U current)
    (hresult : ∀ j ∈ Icc 4 q,
      FixedRandomOrderResult P (W.prefix current)
        (fun omega ↦ Function.Embedding.subtype (fun T ↦ T ∈ available omega)) j (gap j)
        (fun omega ↦ finiteHypergraphOnSubset (available omega)
          (localForbiddenConfigurations ((Icc 4 q).biUnion F) (available omega) (old omega) j))
        (fun omega ↦ (Ico 4 j).biUnion (fun i ↦ Lstar i omega)) (F j) (candidates j)
        (y j) (z j) (a j) (rho j) (Lstar j) (envelope j))
    (G : Omega → SimpleGraph V)
    (hpacking : ∀ omega, IsPackingOn (old omega))
    (havoid : ∀ omega, AvoidsForbidden (old omega) ((Icc 4 q).biUnion F))
    (hsingle : ∀ omega T, T ∈ available omega →
      ¬ CompletesForbidden ((Icc 4 q).biUnion F) (old omega) T)
    (hgraph : ∀ omega, G omega ≤ leaveGraph (old omega))
    (htri : ∀ omega, ConsistsOfTriangles (G omega) (available omega))
    (horizon : Omega → ℕ) (active : Omega → ℕ → GreedyStateOn (W.U current) → Prop) :
    ∀ omega,
      let J := regularizedForbiddenUnion
        (restrictTripleIndexEmbedding (W.U current)
          (Function.Embedding.subtype (fun T ↦ T ∈ available omega))
          (fun T ↦ hsupport omega T.val T.property)) q (fun j ↦ Lstar j omega)
      (stoppedGreedyStateLaw (horizon omega) J (active omega)
        ⟨∅, restrictTripleSystemTo (W.U current) (available omega)⟩).SupportedOn fun S ↦
        let M := mapTripleSystem (Function.Embedding.subtype (fun v ↦ v ∈ W.U current)) S.chosen
        M ⊆ available omega ∧ IsPackingOn (old omega ∪ M) ∧ Disjoint (old omega) M ∧
          AvoidsForbidden (old omega ∪ M) ((Icc 4 q).biUnion F) := by
  have horder : ∀ H ∈ (Icc 4 q).biUnion F, H.card + 2 ≤ q := by
    intro H hH
    obtain ⟨j, hj, hHj⟩ := mem_biUnion.mp hH
    have hcard := ((hresult j hj).spread.uniform H (mem_union_left _ hHj)).1
    have hjbound := mem_Icc.mp hj
    omega
  intro omega
  exact current_regularized_stopped_global_structure (W.U current) (available omega) (old omega)
    ((Icc 4 q).biUnion F) q (horizon omega) (hsupport omega) (fun j ↦ Lstar j omega) (active omega)
    (fun j hj ↦ (hresult j hj).uniform omega) (G omega) horder (hpacking omega) (havoid omega)
    (hsingle omega) (hgraph omega) (htri omega) (fun j hj ↦ (hresult j hj).covers_original omega)

end

end Erdos207
