/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PreliminaryDegreePowerBudgets
import ErdosProblems.Erdos207.RawInternalLeftSuccess

/-! # Actual raw internal success from the reserve, degree, and left-cap events -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

theorem RawResidualInternalStructure.notFailed_of_reserve_degree
    {Ω V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {i : Fin ell} {F : ForbiddenFamilyOn V}
    {G : Ω → SimpleGraph V} {Gamma : SimpleGraph V} {A P M : Ω → TripleSystemOn V}
    {bits : Ω → Sym2 V → Bool} {mu : ℝ≥0} {omega : Ω} {z : InternalEdgeGreedyStateOn V}
    (houtcome : RawResidualInternalStructure W i F G
      (fun w ↦ pairSafeAvailable (A w) (P w ∪ M w)) (fun w ↦ P w ∪ M w) bits
      ⌊mu / 32⌋₊ omega z)
    (hmu : 512 ≤ mu) (I D : TripleSystemOn V) (hclass : z.chosen = I ∪ D)
    (hpacking : IsPackingOn (P omega ∪ M omega))
    (havoid : AvoidsForbidden (P omega ∪ M omega) F)
    (hbase : G omega ≤ Gamma) (hold : G omega ≤ leaveGraph (P omega))
    (hlevel : ∀ T ∈ A omega, (W.prefix i.castSucc).level T = Fin.last i.val)
    (hinitial : ∀ T ∈ A omega, ¬ CompletesForbidden F I T)
    (hprotected : M omega ⊆ reserveProtectedAvailable
      (reserveEdges (G omega) (W.U i.succ) (bits omega)) (A omega))
    (hreserve : InternalReserveSupplyGood (G omega) (A omega) (W.U i.succ) ⌊mu / 8⌋₊ (bits omega))
    (hdegree : PreliminaryResidualDegreeGood
      (reserveProtectedOuterGraph (G omega) (W.U i.succ)
        (reserveEdges (G omega) (W.U i.succ) (bits omega))) (W.U i.succ) (M omega) ⌊mu / 256⌋₊)
    (hleft : SourceLeftCaps (W.prefix i.castSucc) F (W.U i.succ) Gamma I D
      (reserveEdges (G omega) (W.U i.succ) (bits omega)) ⌈mu / 128⌉₊) :
    z.failed = false := by
  have hcuts := internal_cover_rounded_budgets mu hmu
  apply houtcome.notFailed_of_leftCaps I D hclass hpacking havoid hbase
    (fun T hT ↦ hlevel T (pairSafeAvailable_subset_left _ _ hT))
    (fun T hT ↦ hinitial T (pairSafeAvailable_subset_left _ _ hT))
    (pairSafeAvailable_triangleAvoids _ _)
    ((hdegree.mono_selected subset_union_right).internal_incidence
      (reserveEdges_subset_crossingEdges (G omega) (W.U i.succ) (bits omega)))
    (hreserve.preliminary_pairSafe_supply hcuts.2.2.2.1 hold hprotected) hleft

theorem rawResidualInternalKernel_rounded_point_bound
    {Ω V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (i : Fin ell) (F : ForbiddenFamilyOn V)
    (G : Ω → SimpleGraph V) (A P : Ω → TripleSystemOn V) (bits : Ω → Sym2 V → Bool)
    (mu : ℝ≥0) (hmu : 512 ≤ mu) (omega : Ω) (Q : TripleSystemOn V) :
    (rawResidualInternalKernel W i F G A P bits ⌊mu / 32⌋₊ omega).probability
      (fun z ↦ Q ⊆ rawResidualInternalAdded P omega z) ≤ (64 / mu) ^ Q.card := by
  have hcuts := internal_cover_rounded_budgets mu hmu
  have hmu0 : 0 < mu := (by norm_num : (0 : ℝ≥0) < 512).trans_le hmu
  have hpoint : ((⌊mu / 32⌋₊ : ℝ≥0))⁻¹ ≤ 64 / mu := by
    simpa only [one_div, inv_div, inv_inv] using
      one_div_le_one_div_of_le (div_pos hmu0 (by norm_num)) hcuts.2.1
  exact (rawResidualInternalKernel_probability_subset_new_le W i F G A P bits
    ⌊mu / 32⌋₊ hcuts.1 omega Q).trans (pow_le_pow_left' hpoint _)

end

end Erdos207
