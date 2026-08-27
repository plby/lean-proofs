/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceSparseStageBudget
import ErdosProblems.Erdos207.SourceInternalStageBudget
import ErdosProblems.Erdos207.SourceLinkStageBudget
import ErdosProblems.Erdos207.SourceAuxiliaryCoefficients
import ErdosProblems.Erdos207.SourceReservePreparation

/-! # Numeric inputs for a complete compressed cover-down transition -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

def sourceOrdinaryProductConstant (q : ℕ) : ℝ≥0 :=
  ksssSparseGraphProductConstant q (fun d ↦ 9*24^d)

def sourceOrdinaryInternalConstant (q : ℕ) (eta0 C : ℝ≥0) : ℝ≥0 :=
  4*max ((16*C)^3*(152*sourceOrdinaryProductConstant q/eta0)) (2*sourceOrdinaryProductConstant q)

structure SourceCoverStageBudget
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (q h b B k analytic Rmin c R m : ℕ) (W : Vortex V ell) (i : Fin ell) (bank : TripleSystemOn V)
    (p eta xi xi' r C beta eta0 B0 error : ℝ≥0) where
  C_pos : 1 ≤ C
  h_large : 4 ≤ h
  eta_floor : eta0 ≤ eta
  r_pos : 0 < r
  r_le_one : r ≤ 1
  r_small : r ≤ 1/24576
  xi_reference : xi ≤ (1/1048576 : ℝ≥0)/4
  xi_small : xi ≤ 1/1536
  reference_endpoint : 1 ≤ ((1/1048576 : ℝ≥0)/4)*(p^2*eta*(W.U i.succ).card)
  current_density : 6144 ≤ p^4*eta^6*(W.U i.castSucc).card
  inner_margin : ((W.U i.succ).card : ℝ≥0) ≤ p^4*eta^6*(W.U i.castSucc).card/1536
  theta_pos : 0 < 1/(24*(analytic : ℝ)^ksssPowerErrorExponent b B)
  theta_half : 1/(24*(analytic : ℝ)^ksssPowerErrorExponent b B) ≤ 1/2
  sampling : 2*((W.U i.castSucc).card : ℝ)^2*
    Real.exp (-(1/(24*(analytic : ℝ)^ksssPowerErrorExponent b B))^2*
      ((p : ℝ)^2*eta*(W.U i.castSucc).card)/16) < 1
  reserve_error : sourceReserveFailureBound (Fintype.card V) (W.U i.succ).card p eta r (1/1048576) +
    reserveRegularizationFailureBound (W.U i.castSucc).card p eta r ≤ error
  error_half : error ≤ 1/2
  analytic_density_lower : 1/(analytic : ℝ≥0)^b ≤ p
  analytic_density_upper : p ≤ 1/analytic
  auxiliary_coefficient : sourceAuxiliaryCoefficient q i.val ≤ analytic
  auxiliary_density : 1 ≤ p^3*(W.U i.castSucc).card
  auxiliary_extension : ∀ j ∈ Icc 4 q, ∀ j' ∈ Icc j q,
    sourcePrefixZ q bank i.val j' ≤ sourcePrefixY q i.val*p^(3*(j-3))*(W.U i.castSucc).card
  auxiliary_error : sourceAllAuxiliaryDegreeFailure q (3*R+3*c) analytic (3*c) (4*C) B0 ≤ error
  sparse : SourceSparseStageBudget q i.val b B k analytic Rmin c R m
    (W.U i.castSucc).card (Fintype.card V) p eta (sourceAuxiliaryCoefficient q i.val) (8*C) beta B0 error
    (sourcePrefixZ q bank i.val)
  internal : SourceInternalStageBudget W i q bank p eta r (16*C) beta
    (2/(analytic : ℝ≥0)^c) (24/(p^2*eta*(W.U i.castSucc).card)) (sourceOrdinaryProductConstant q)
    (1/(analytic : ℝ≥0)^(c*m)) (sourceOrdinaryInternalConstant q eta0 C)
  link : SourceLinkStageBudget q h W i bank p r (sourceOrdinaryInternalConstant q eta0 C)
    (beta+1/(analytic : ℝ≥0)^(c*m)) eta xi xi'
  link_degree : link.d = ⌊r^2*p^2*eta*(W.U i.succ).card/256⌋₊
  degree_error : internal.degreeError ≤ link.degreeError
  link_reference : link.referenceTolerance = 1/1048576

end

end Erdos207
