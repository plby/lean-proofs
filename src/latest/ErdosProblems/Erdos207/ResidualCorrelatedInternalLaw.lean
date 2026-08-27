/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ResidualAugmentedReserveNumeric
import ErdosProblems.Erdos207.InternalEdgeResidualError

/-! # Binding the genuine preliminary and internal kernels in the residual master law -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem IsResidualReserveStronglyWellDistributed.jointBind_correlatedInternal_graphMixed
    {Ω Ξ Ζ V : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype Ξ] [DecidableEq Ξ]
    [Fintype Ζ] [DecidableEq Ζ] [Fintype V] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Ω} {Kpre : Ω → FiniteLaw Ξ} {Kint : Ω → Ξ → FiniteLaw Ζ}
    {W : Vortex V ell} {k next : Fin (ell + 1)} {G : SimpleGraph V}
    {initial later : Ω → TripleSystemOn V} {reserve : Ω → Finset (Sym2 V)}
    {p r C b : ℝ≥0}
    (hstrong : IsResidualReserveStronglyWellDistributed L W k G initial later reserve p r C b)
    (working : Ω → SimpleGraph V) (U : Finset V)
    (pre : Ω → Ξ → TripleSystemOn V) (internal : Ω → Ξ → Ζ → TripleSystemOn V)
    (survival point constant internalPoint : Ω → ℝ≥0) (alpha eta J factor error r' : ℝ≥0)
    (hC : 1 ≤ C) (hJ : 1 ≤ J) (hfactor : 1 ≤ factor) (halpha : alpha ≤ 1)
    (heta : eta ≤ 1) (hr : r ≤ r') (hetar : eta ≤ r')
    (hkn : k ≤ next) (hnonempty : ∀ i, (W.U i).Nonempty)
    (hnew : alpha * p ^ 3 ≤ factor * (p / ((W.U k).card : ℝ≥0)))
    (hreserve : ∀ ω, 0 < L.mass ω → reserve ω ⊆ crossingEdges (working ω) U)
    (hmixed : ∀ ω, 0 < L.mass ω → IsGraphMixedProductBound (Kpre ω) (pre ω)
      (reserveProtectedOuterGraph (working ω) U (reserve ω))
      (survival ω) (point ω) (constant ω) error)
    (hintOne : ∀ ω, 0 < L.mass ω → internalPoint ω ≤ 1)
    (hC4 : ∀ ω, 0 < L.mass ω → ∀ ξ Q,
      (Kint ω ξ).probability (fun z ↦ Q ⊆ internal ω ξ z) ≤ (internalPoint ω) ^ Q.card)
    (halphaBound : ∀ ω, 0 < L.mass ω →
      constant ω * point ω + (constant ω * survival ω) * internalPoint ω ≤ alpha)
    (hetaBound : ∀ ω, 0 < L.mass ω → constant ω * survival ω ≤ eta)
    (hconstant : ∀ ω, 0 < L.mass ω → 2 * constant ω ≤ J)
    (hstruct : ∀ ω, 0 < L.mass ω → ((Kpre ω).jointBind (Kint ω)).SupportedOn fun z ↦
      IsPackingOn ((initial ω ∪ later ω) ∪ preliminaryInternalCombinedAdded (pre ω) (internal ω) z) ∧
        Disjoint (initial ω ∪ later ω) (preliminaryInternalCombinedAdded (pre ω) (internal ω) z) ∧
        ∀ T ∈ preliminaryInternalCombinedAdded (pre ω) (internal ω) z, tripleEdgeFinset T ⊆ graphEdges G)
    (hscheduled : ∀ ω, 0 < L.mass ω → ((Kpre ω).jointBind (Kint ω)).SupportedOn fun z ↦
      Disjoint (pre ω z.1) (internal ω z.1 z.2) ∧
        NewTrianglesUseScheduledOuterEdges U
          (preliminaryResidualInternalEdges (working ω) U (pre ω z.1)) (pre ω z.1)
          (preliminaryInternalCombinedAdded (pre ω) (internal ω) z))
    (hscope : ∀ ω, 0 < L.mass ω → ((Kpre ω).jointBind (Kint ω)).SupportedOn fun z ↦
      ∀ T ∈ preliminaryInternalCombinedAdded (pre ω) (internal ω) z, T.1 ⊆ W.U k) :
    let kernel : Ω → FiniteLaw (Ξ × Ζ) := fun ω ↦ (Kpre ω).jointBind (Kint ω)
    let added : Ω → Ξ × Ζ → TripleSystemOn V := fun ω z ↦ preliminaryInternalCombinedAdded (pre ω) (internal ω) z
    IsResidualReserveStronglyWellDistributed (L.jointBind kernel) W next G
      (jointInitial initial) (jointLater later added)
      (fun z ↦ preliminaryAugmentedReserve (working z.1) U (reserve z.1) (added z.1 z.2))
      p r' (2 * max (C ^ 3 * factor) J) (b + error) := by
  dsimp only
  apply hstrong.jointBind_augmentedReserve_numeric working U
    (fun ω z ↦ preliminaryInternalCombinedAdded (pre ω) (internal ω) z)
    alpha eta J factor error r' hC hJ hfactor halpha heta hr hetar hkn hnonempty hnew
    _ hstruct hscope
  intro ω hω Q E
  have hlocal : ((Kpre ω).jointBind (Kint ω)).SupportedOn fun z ↦
      IsPackingOn (preliminaryInternalCombinedAdded (pre ω) (internal ω) z) ∧
        Disjoint (pre ω z.1) (internal ω z.1 z.2) ∧
        NewTrianglesUseScheduledOuterEdges U
          (preliminaryResidualInternalEdges (working ω) U (pre ω z.1)) (pre ω z.1)
          (preliminaryInternalCombinedAdded (pre ω) (internal ω) z) := by
    intro z hz
    exact ⟨(hstruct ω hω z hz).1.mono subset_union_right, hscheduled ω hω z hz⟩
  have hraw := (hmixed ω hω).protectedInternalCombined_le (Kint ω) U (reserve ω) (hreserve ω hω)
    (internal ω) (internalPoint ω) (hintOne ω hω) (hC4 ω hω) hlocal Q E
  apply hraw.trans
  exact add_le_add
    (mul_le_mul (pow_le_pow_left' (halphaBound ω hω) _) (pow_le_pow_left' (hetaBound ω hω) _) zero_le zero_le)
    (mul_le_mul_of_nonneg_right (pow_le_pow_left' (hconstant ω hω) _) zero_le)

end

end Erdos207
